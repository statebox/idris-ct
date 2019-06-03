> module Limit.Initial
>
> import Basic.Category
> import Basic.Isomorphism
>
> %access public export
> %default total
>
> record InitialObject (cat : Category) where
>     constructor MkInitialObject
>     payload: obj cat
>     exists: (b : obj cat) -> mor cat payload b
>     unique: (b : obj cat) -> (f, g : mor cat payload b) -> f = g
>
> composeInitialMorphisms :
>      (cat : Category)
>   -> (a : InitialObject cat)
>   -> (b : InitialObject cat)
>   -> mor cat (payload a) (payload a)
> composeInitialMorphisms cat a b =
>   let
>       x = payload a
>       y = payload b
>   in
>       compose cat x y x (exists a y) (exists b x)
>
> initialObjectsAreIsomorphic :
>      (cat : Category)
>   -> (a : InitialObject cat)
>   -> (b : InitialObject cat)
>   -> Isomorphism cat (payload a) (payload b) (exists a (payload b))
> initialObjectsAreIsomorphic cat a b = MkIsomorphism
>   ( exists b (payload a) )
>   ( unique a (payload a) (composeInitialMorphisms cat a b) (identity cat (payload a)) )
>   ( unique b (payload b) (composeInitialMorphisms cat b a) (identity cat (payload b)) )
