> module Monoid.FreeMonoid
>
> import Data.Fin
> import Interfaces.Verified
> import Monoid.Monoid
>
> %access public export
> %default total
>
> finSetToFreeMonoid : Nat -> Monoid
> finSetToFreeMonoid n = MkMonoid (List (Fin n)) %implementation
