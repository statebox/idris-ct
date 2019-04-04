> module Monoid.MonoidAsCategory
>
> import Basic.Category
> import Monoid.Monoid
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> MonoidMorphism : (monoid : Type) -> Unit -> Unit -> Type
> MonoidMorphism monoid _ _ = monoid
>
> monoidAsCategory : Monoid -> Category
> monoidAsCategory monoid = MkCategory
>   Unit
>   (MonoidMorphism (set monoid))
>   (\_ => neutral @{verifiedMonoidToMonoid @{axioms monoid}})
>   (\_, _, _, f, g => (<+>) @{verifiedMonoidToSemigroup @{axioms monoid}} f g)
>   (\_, _, f => monoidNeutralIsNeutralR @{axioms monoid} f)
>   (\_, _, f => monoidNeutralIsNeutralL @{axioms monoid} f)
>   (\_, _, _, _, f, g, h => semigroupOpIsAssociative @{verifiedMonoidToVerifiedSemigroup @{axioms monoid}} f g h)
