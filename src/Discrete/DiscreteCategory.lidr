> module Discrete.DiscreteCategory
>
> import Basic.Category
>
> %access public export
> %default total
>
> DiscreteMorphism : (x, y : a) -> Type
> DiscreteMorphism x y = x = y
>
> discreteIdentity : (x : a) -> DiscreteMorphism x x
> discreteIdentity _ = Refl
>
> discreteCompose : (x, y, z : a) -> DiscreteMorphism x y -> DiscreteMorphism y z -> DiscreteMorphism x z
> discreteCompose _ _ _ Refl Refl = Refl
>
> discreteLeftIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x x y (discreteIdentity x) f = f
> discreteLeftIdentity _ _ Refl = Refl
>
> discreteRightIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x y y f (discreteIdentity y) = f
> discreteRightIdentity _ _ Refl = Refl
>
> discreteAssociativity : (w, x, y, z : a)
>                      -> (f : DiscreteMorphism w x)
>                      -> (g : DiscreteMorphism x y)
>                      -> (h : DiscreteMorphism y z)
>                      -> discreteCompose w x z f (discreteCompose x y z g h)
>                       = discreteCompose w y z (discreteCompose w x y f g) h
> discreteAssociativity _ _ _ _ Refl Refl Refl = Refl
>
> discreteCategory : (a : Type) -> Category
> discreteCategory a = MkCategory
>   a
>   DiscreteMorphism
>   discreteIdentity
>   discreteCompose
>   discreteLeftIdentity
>   discreteRightIdentity
>   discreteAssociativity
