open Types
open LlbcAst
include Charon.LlbcAstUtils
open Collections

module FunIdOrderedType : OrderedType with type t = fun_id = struct
  type t = fun_id

  let compare = compare_fun_id
  let to_string = show_fun_id
  let pp_t = pp_fun_id
  let show_t = show_fun_id
end

module FunIdMap = Collections.MakeMap (FunIdOrderedType)
module FunIdSet = Collections.MakeSet (FunIdOrderedType)

let body_as_body = Charon.LlbcAstUtils.body_as_structured

let body_as_body_exn file line f =
  match body_as_body f with
  | Some body -> body
  | None -> Errors.craise_opt_span file line None "Not a LLBC body"

let body_is_known (b : body) : bool = Option.is_some (body_as_body b)

let body_as_target_dispatch (b : body) :
    (string * Types.fun_decl_ref) list option =
  match b with
  | TargetDispatchBody targets -> Some targets
  | _ -> None

let body_is_target_dispatch (b : body) : bool =
  Option.is_some (body_as_target_dispatch b)

(** A function body is translatable if it is either a structured body (normal
    case) or a target dispatch body (multi-target). *)
let body_is_translatable (b : body) : bool =
  body_is_known b || body_is_target_dispatch b

let lookup_fun_sig (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    bound_fun_sig =
  match fun_id with
  | FRegular id ->
      let fun_decl = FunDeclId.Map.find id fun_decls in
      bound_fun_sig_of_decl fun_decl
  | FBuiltin aid -> Builtin.get_builtin_fun_sig aid

(** Return the opaque declarations found in the crate, which are also *not
    builtin*.

    [filter_builtin]: if [true], do not consider as opaque the external
    definitions that we will map to definitions from the standard library.

    Remark: the list of functions also contains the list of opaque global
    bodies. *)
let crate_get_opaque_non_builtin_decls (k : crate) (filter_builtin : bool)
    (type_decls : type_decl TypeDeclId.Map.t)
    (fun_decls : fun_decl FunDeclId.Map.t) : type_decl list * fun_decl list =
  let open ExtractBuiltin in
  let ctx = Charon.NameMatcher.ctx_from_crate k in
  let is_opaque_fun (d : fun_decl) : bool =
    (not (body_is_known d.body))
    (* Something to pay attention to: we must ignore trait method *declarations*
       (which don't have a body but must not be considered as opaque) *)
    && (match d.src with
       | TraitDeclItem (_, _, false) -> false
       | _ -> true)
    && ((not filter_builtin)
       || (not
             (NameMatcherMap.mem ctx d.item_meta.name (builtin_globals_map ())))
          && not (NameMatcherMap.mem ctx d.item_meta.name (builtin_funs_map ()))
       )
  in
  let is_opaque_type (d : type_decl) : bool =
    d.kind = Opaque
    && ((not filter_builtin)
       || not (NameMatcherMap.mem ctx d.item_meta.name (builtin_types_map ())))
  in
  (* Note that by checking the function bodies we also the globals *)
  ( List.filter is_opaque_type (TypeDeclId.Map.values type_decls),
    List.filter is_opaque_fun (FunDeclId.Map.values fun_decls) )

(** Return true if the crate contains opaque declarations, ignoring the builtin
    definitions. *)
let crate_has_opaque_non_builtin_decls (k : crate) (filter_builtin : bool)
    (type_decls : type_decl TypeDeclId.Map.t)
    (fun_decls : fun_decl FunDeclId.Map.t) : bool =
  crate_get_opaque_non_builtin_decls k filter_builtin type_decls fun_decls
  <> ([], [])

(** Strip trailing [PeTarget] elements from a name.

    Multi-target extraction appends [PeTarget] to per-target function names.
    This element doesn't participate in pattern matching (the pattern generator
    skips it), so we strip it before calling [name_to_pattern] to avoid
    triggering its roundtrip assertion. *)
let strip_target_suffix (n : name) : name =
  match List.rev n with
  | Types.PeTarget _ :: rest -> List.rev rest
  | _ -> n

(** Strip all trailing [PeInstantiated] elements from a name.

    Charon's [--monomorphize] pass appends [PeInstantiated] to a name for each
    monomorphized instantiation. Pattern generation in [NameMatcher] drops
    [PeInstantiated] elements entirely (they don't participate in pattern
    matching) — and helpers like [Collections.List.last] / [TypesUtils.as_ident]
    expect the trailing element to be a [PeIdent] (or [PeImpl]). Strip the
    trailing [PeInstantiated]s to expose the underlying identifier. *)
let rec strip_instantiated_suffix (n : name) : name =
  match List.rev n with
  | Types.PeInstantiated _ :: rest ->
      strip_instantiated_suffix (List.rev rest)
  | _ -> n

(** Strip every [PeInstantiated] element from a name, regardless of position.

    Pattern generation in [NameMatcher.name_to_pattern_aux] silently drops
    [PeInstantiated] anywhere in the name, but the round-trip assertion that
    follows ([match_name] checking the produced pattern matches the original
    name) only handles trailing [PeInstantiated]s. For names with
    [PeInstantiated] in the middle (e.g. [crate::Foo::<T>::method]) the
    assertion fires and pattern generation aborts. Strip all of them upfront
    so the pattern and the stripped name agree. *)
let strip_all_instantiated (n : name) : name =
  List.filter (function Types.PeInstantiated _ -> false | _ -> true) n

(** Extract and strip any trailing [PeTarget] element from a name, returning the
    cleaned name and an optional target suffix string (with [-] replaced by
    [_]). *)
let extract_target_suffix (name : name) : name * string option =
  match Collections.List.last name with
  | PeTarget target ->
      let target = String.concat "_" (String.split_on_char '-' target) in
      (Collections.List.prefix (List.length name - 1) name, Some target)
  | _ -> (name, None)

let add_target_suffix (name : name) (target_suffix : string option) : name =
  match target_suffix with
  | None -> name
  | Some target -> name @ [ PeTarget target ]

let name_to_pattern (span : Meta.span option) (ctx : Charon.NameMatcher.ctx)
    (c : Charon.NameMatcher.to_pat_config) (n : name) =
  let n = strip_target_suffix n in
  (* Strip every [PeInstantiated] before round-tripping. Pattern generation
     itself drops these elements, but the post-conversion sanity check
     ([match_name]) drops the generic args carried by [PeInstantiated] and
     then fails the round-trip — even though the pattern is structurally
     fine. Stripping upfront keeps the pattern correct and avoids triggering
     the assertion on monomorphized names. *)
  let n = strip_all_instantiated n in
  if !Config.fail_hard then Charon.NameMatcher.name_to_pattern ctx c n
  else
    try Charon.NameMatcher.name_to_pattern ctx c n
    with
    | Not_found ->
        [%craise_opt_span] span
          "Could not convert the name to a pattern because of missing \
           definition(s)"
    | Assert_failure _ ->
        (* The pattern's round-trip [match_name] assertion is over-strict for
           monomorphized names whose [PeInstantiated] siblings have already
           been stripped. The pattern is still structurally correct, so fall
           back to [name_to_pattern_aux] which skips the assertion. *)
        Charon.NameMatcher.name_to_pattern_aux ctx c n

let name_with_crate_to_pattern_string (span : Meta.span option)
    (crate : LlbcAst.crate) (n : Types.name) : string =
  let mctx = Charon.NameMatcher.ctx_from_crate crate in
  let c : Charon.NameMatcher.to_pat_config =
    {
      tgt = TkPattern;
      use_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
    }
  in
  let pat = name_to_pattern span mctx c n in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat

let name_with_generics_to_pattern (span : Meta.span option)
    (ctx : Charon.NameMatcher.ctx) (c : Charon.NameMatcher.to_pat_config)
    (params : generic_params) (n : Charon.Types.name) (args : generic_args) =
  (* Strip every [PeInstantiated] before round-tripping (see the note in
     [name_to_pattern] above). *)
  let n = strip_all_instantiated n in
  if !Config.fail_hard then
    Charon.NameMatcher.name_with_generics_to_pattern ctx c params n args
  else
    try Charon.NameMatcher.name_with_generics_to_pattern ctx c params n args
    with
    | Not_found ->
        [%craise_opt_span] span
          "Could not convert the name to a pattern because of missing \
           definition(s)"
    | Assert_failure _ ->
        (* Same fallback as in [name_to_pattern]: the assertion is over-strict
           for monomorphized names; the pattern itself is fine. *)
        let m = Charon.NameMatcher.compute_constraints_map params in
        let args_pat = Charon.NameMatcher.generic_args_to_pattern ctx c m args in
        Charon.NameMatcher.name_with_generic_args_to_pattern_aux ctx c n
          (Some args_pat)

let name_with_generics_crate_to_pattern_string (span : Meta.span option)
    (crate : LlbcAst.crate) (n : Types.name) (params : Types.generic_params)
    (args : Types.generic_args) : string =
  let mctx = Charon.NameMatcher.ctx_from_crate crate in
  let c : Charon.NameMatcher.to_pat_config =
    {
      tgt = TkPattern;
      use_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
    }
  in
  let pat = name_with_generics_to_pattern span mctx c params n args in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat

let trait_impl_with_crate_to_pattern_string (span : Meta.span option)
    (crate : LlbcAst.crate) (trait_decl : LlbcAst.trait_decl)
    (trait_impl : LlbcAst.trait_impl) : string =
  name_with_generics_crate_to_pattern_string span crate
    trait_decl.item_meta.name trait_decl.generics trait_impl.impl_trait.generics

(** Return true if the statement contains an instruction which breaks the
    control flow, at the exception of panics (that is: a break, a continue or a
    return) *)
let statement_has_break_continue_return (st : statement) : bool =
  let visitor =
    object
      inherit [_] iter_statement
      method! visit_Break _ _ = raise Utils.Found
      method! visit_Continue _ _ = raise Utils.Found
      method! visit_Return _ = raise Utils.Found
    end
  in
  try
    visitor#visit_statement () st;
    false
  with Utils.Found -> true

(** Return true if the block contains a statement which breaks the control flow,
    at the exception of panics (that is: a break, a continue or a return) *)
let block_has_break_continue_return (st : block) : bool =
  let visitor =
    object
      inherit [_] iter_statement
      method! visit_Break _ _ = raise Utils.Found
      method! visit_Continue _ _ = raise Utils.Found
      method! visit_Return _ = raise Utils.Found
    end
  in
  try
    visitor#visit_block () st;
    false
  with Utils.Found -> true

(** Compute the size of a function body - we count the number of statements and
    blocks *)
let compute_body_size (b : body) : int =
  let size = ref 0 in
  let incr () = size := !size + 1 in
  let visitor =
    object
      inherit [_] iter_statement as super

      method! visit_statement env st =
        incr ();
        super#visit_statement env st

      method! visit_block env st =
        incr ();
        super#visit_block env st
    end
  in
  let () =
    match b with
    | StructuredBody body -> visitor#visit_block () body.body
    | _ -> ()
  in
  !size

(** Compute the size of a function - we count the number of statements and
    blocks *)
let compute_fun_decl_size (f : fun_decl) : int = compute_body_size f.body
