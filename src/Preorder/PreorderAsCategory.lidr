> module Preorder.PreorderAsCategory
>
> import Basic.Category
> import Preorder.UniquePreorder
>
> -- contrib
> import Decidable.Order
>
> %access public export
> %default total
>
> leftIdentity : UniquePreorder t po
>   => (a, b : t)
>   -> (f : po a b)
>   -> transitive a a b (reflexive a) f = f
> leftIdentity a b f = unique a b (transitive a a b (reflexive a) f) f
>
> rightIdentity : UniquePreorder t po
>   => (a, b : t)
>   -> (f : po a b)
>   -> transitive a b b f (reflexive b) = f
> rightIdentity a b f = unique a b (transitive a b b f (reflexive b)) f
>
> associativity : UniquePreorder t po
>   => (a, b, c, d : t)
>   -> (f : po a b)
>   -> (g : po b c)
>   -> (h : po c d)
>   -> transitive a b d f (transitive b c d g h) = transitive a c d (transitive a b c f g) h
> associativity a b c d f g h = unique a d
>   (Decidable.Order.transitive a b d f (transitive b c d g h))
>   (Decidable.Order.transitive a c d (transitive a b c f g) h)
>
> preorderAsCategory : UniquePreorder t po => Category
> preorderAsCategory {t} {po} = MkCategory
>   t
>   po
>   reflexive
>   transitive
>   (leftIdentity {t} {po})
>   (rightIdentity {t} {po})
>   (associativity {t} {po})
