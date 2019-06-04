> module Idris.CoProduct
>
> import Idris.TypesAsCategoryExtensional
>
> import Basic.Category
> import Limits.CoProduct
>
> applyLeftOrRight :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> (ExtensionalTypeMorphism (Either a b) c)
> applyLeftOrRight a b c f g = MkExtensionalTypeMorphism
>   (\x => case x of
>           Left y => func f y
>           Right y => func g y
>   )
>
> cfgLeftCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> extCompose a (Either a b) c (MkExtensionalTypeMorphism Left) (applyLeftOrRight a b c f g) = f
> cfgLeftCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> cfgRightCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   ->  extCompose b (Either a b) c (MkExtensionalTypeMorphism Right) (applyLeftOrRight a b c f g) = g
> cfgRightCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> cfgUnique :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> (h : ExtensionalTypeMorphism (Either a b) c)
>   -> (left  : f = extCompose a (Either a b) c (MkExtensionalTypeMorphism Left) h)
>   -> (right : g = extCompose b (Either a b) c (MkExtensionalTypeMorphism Right) h)
>   -> applyLeftOrRight a b c f g = h
> cfgUnique a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) (MkExtensionalTypeMorphism h) left right =
>   funExt(
>     \x => case x of
>          Left y => cong {f =(\extFun => apply (func extFun) y)} left
>          Right y => cong {f =(\extFun => apply (func extFun) y)} right
>   )
>
> eitherToCoProduct : (a, b : Type) -> CoProduct Idris.TypesAsCategoryExtensional.typesAsCategoryExtensional a b
> eitherToCoProduct a b = MkCoProduct
>   ( Either a b )
>   ( MkExtensionalTypeMorphism Left )
>   ( MkExtensionalTypeMorphism Right )
>   ( applyLeftOrRight a b )
>   ( cfgLeftCompose a b )
>   ( cfgRightCompose a b )
>   ( cfgUnique a b )
