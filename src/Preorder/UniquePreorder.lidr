> module Preorder.UniquePreorder
>
> -- contrib
> import Decidable.Order
>
> %access public export
> %default total
>
> interface Preorder t po => UniquePreorder t (po : t -> t -> Type) where
>   unique : (a, b : t) -> (f, g : po a b) -> f = g
