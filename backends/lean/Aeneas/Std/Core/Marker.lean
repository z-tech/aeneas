import Aeneas.Std.Core.Core

namespace Aeneas.Std

@[rust_trait "core::marker::StructuralPartialEq"]
structure core.marker.StructuralPartialEq (Self : Type) where

@[rust_trait "core::marker::Freeze"]
structure core.marker.Freeze (Self : Type) where

/-- `core::marker::PhantomData<T>` is a zero-sized marker type that pretends
to own a `T`. It carries no runtime data, so we model it as a one-constructor
structure with no fields. -/
@[rust_type "core::marker::PhantomData"]
structure core.marker.PhantomData (T : Type u) where
  mk ::

end Aeneas.Std
