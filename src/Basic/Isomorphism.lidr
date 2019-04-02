> module Basic.Isomorphism
>
> import Basic.Category
>
> %access public export
> %default total
>
> record Isomorphism (cat : Category) (a : obj cat) (b : obj cat) (morphism : mor cat a b) where
>   constructor MkIsomorphism
>   isoInverse: mor cat b a
>   lawleft: compose cat a b a morphism isoInverse = identity cat a
>   lawright: compose cat b a b isoInverse morphism = identity cat b
