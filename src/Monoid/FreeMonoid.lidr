> module Monoid.FreeMonoid
>
> import Data.Fin
> import Interfaces.Verified
> import Monoid.Monoid
>
> %access public export
> %default total
>
> FreeMonoid : Type -> Monoid
> FreeMonoid t = MkMonoid (List t) %implementation
>
> finSetToFreeMonoid : Nat -> Monoid
> finSetToFreeMonoid n = FreeMonoid (Fin n)
