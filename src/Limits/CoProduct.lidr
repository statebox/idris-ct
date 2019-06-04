> module Limits.CoProduct
>
> import Basic.Category
>
> %access public export
> %default total
>
> record CoProduct (cat : Category) (a : obj cat) (b : obj cat) where
>   constructor MkCoProduct
>   payload: obj cat
>   inl: mor cat a payload
>   inr: mor cat b payload
>   cfgMorphism:
>        (c : obj cat)
>     -> (f : mor cat a c)
>     -> (g : mor cat b c)
>     -> mor cat payload c
>   leftCompose:
>        (c : obj cat)
>     -> (f : mor cat a c)
>     -> (g : mor cat b c)
>     -> compose cat a payload c inl (cfgMorphism c f g) = f
>   rightCompose:
>        (c : obj cat)
>     -> (f : mor cat a c)
>     -> (g : mor cat b c)
>     -> compose cat b payload c inr (cfgMorphism c f g) = g
>   unique:
>        (c : obj cat)
>     -> (f : mor cat a c)
>     -> (g : mor cat b c)
>     -> (h : mor cat payload c)
>     -> (left  : f = compose cat a payload c inl h )
>     -> (right : g = compose cat b payload c inr h )
>     -> cfgMorphism c f g = h
