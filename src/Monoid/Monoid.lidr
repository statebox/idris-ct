> module Monoid.Monoid
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> record Monoid where
>   constructor MkMonoid
>   set    : Type
>   axioms : VerifiedMonoid set
>
> buildMonoid : (vm : VerifiedMonoid m) => Monoid
> buildMonoid @{vm} {m} = MkMonoid m vm
>
> verifiedMonoidToSemigroup : VerifiedMonoid m => Semigroup m
> verifiedMonoidToSemigroup @{mon} = %implementation
>
> verifiedMonoidToVerifiedSemigroup : VerifiedMonoid m => VerifiedSemigroup m
> verifiedMonoidToVerifiedSemigroup @{mon} = %implementation
>
> verifiedMonoidToMonoid : VerifiedMonoid m => Monoid m
> verifiedMonoidToMonoid @{mon} = %implementation
