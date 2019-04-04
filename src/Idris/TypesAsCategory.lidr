> module Idris.TypesAsCategory
>
> import Basic.Category
>
> %access public export
> %default total
>
> TypeMorphism : Type -> Type -> Type
> TypeMorphism a b = a -> b
>
> identity : (a : Type) -> TypeMorphism a a
> identity a = id
>
> compose :
>      (a, b, c : Type)
>   -> (f : TypeMorphism a b)
>   -> (g : TypeMorphism b c)
>   -> TypeMorphism a c
> compose a b c f g = g . f
>
> leftIdentity :
>      (a, b : Type)
>   -> (f : TypeMorphism a b)
>   -> f . (identity a) = f
> leftIdentity a b f = Refl
>
> rightIdentity :
>      (a, b : Type)
>   -> (f : TypeMorphism a b)
>   -> (identity b) . f = f
> rightIdentity a b f = Refl
>
> associativity :
>      (a, b, c, d : Type)
>   -> (f : TypeMorphism a b)
>   -> (g : TypeMorphism b c)
>   -> (h : TypeMorphism c d)
>   -> (h . g) . f = h . (g . f)
> associativity a b c d f g h = Refl
>
> typesAsCategory : Category
> typesAsCategory = MkCategory
>   Type
>   TypeMorphism
>   identity
>   compose
>   leftIdentity
>   rightIdentity
>   associativity
