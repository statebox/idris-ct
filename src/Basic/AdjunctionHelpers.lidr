> module Basic.AdjunctionHelpers

> import Basic.Adjunction
> import Basic.Category as Cat
> import Basic.Functor
> import Basic.HomFunctor
> import Basic.Isomorphism
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Dual.DualCategory
> import Dual.DualFunctor
> import Idris.TypesAsCategoryExtensional as Idris
> import Product.ProductCategory
> import Product.ProductFunctor
> import Utils
>
> %access public export
> %default total

> adjunctionCommutativity :
>        {cat1, cat2 : Category}
>     -> {funL : CFunctor cat2 cat1}
>     -> {funR : CFunctor cat1 cat2}
>     -> (adj: Adjunction cat1 cat2 funL funR)
>     -> {a, a' : obj cat2}
>     -> {b, b' : obj cat1}
>     -> (f: mor cat2 a' a)
>     -> (g: mor cat1 b b')
>     -> (h: mor cat1 (mapObj funL a) b)
>     -> func (compose Idris.typesAsCategoryExtensional _ _ _
>          (component (morphism adj) (a, b))
>          (mapMor (postHomFunctor funR) (a, b) (a', b') (MkProductMorphism f g))) h
>      = func (compose Idris.typesAsCategoryExtensional _ _ _
>          (mapMor (preHomFunctor funL) (a, b) (a', b') (MkProductMorphism f g))
>          (component (morphism adj) (a', b'))) h
> adjunctionCommutativity {cat1} {cat2} {funL} {funR} adj {a} {a'} {b} {b'} f g h =
>   cong {f=\m => func m h} (commutativity (morphism adj) (a, b) (a', b') (MkProductMorphism f g))

> adjunctionCommutativity' :
>        {cat1, cat2 : Category}
>     -> {funL : CFunctor cat2 cat1}
>     -> {funR : CFunctor cat1 cat2}
>     -> (adj: Adjunction cat1 cat2 funL funR)
>     -> {a, a' : obj cat2}
>     -> {b, b' : obj cat1}
>     -> (f: mor cat2 a' a)
>     -> (g: mor cat1 b b')
>     -> (h: mor cat1 (mapObj funL a) b)
>     -> func (mapMor (postHomFunctor funR) (a, b) (a', b') (MkProductMorphism f g))
>          (func (component (morphism adj) (a, b)) h)
>      = func (component (morphism adj) (a', b'))
>          (func (mapMor (preHomFunctor funL) (a, b) (a', b') (MkProductMorphism f g)) h)
> adjunctionCommutativity' {cat1} {cat2} {funL} {funR} adj {a} {a'} {b} {b'} f g h =
>   trans (sym (funcPreserveCompose (component (morphism adj) (a, b)) (mapMor (postHomFunctor funR) (a, b) (a', b') (MkProductMorphism f g))))
>   (trans (adjunctionCommutativity adj f g h)
>   (funcPreserveCompose (mapMor (preHomFunctor funL) (a, b) (a', b') (MkProductMorphism f g)) (component (morphism adj) (a', b'))))

> {-
> adjunctionInverseCommutativity :
>        {cat1, cat2 : Category}
>     -> {funL : CFunctor cat2 cat1}
>     -> {funR : CFunctor cat1 cat2}
>     -> (adj: Adjunction cat1 cat2 funL funR)
>     -> {a, a' : obj cat2}
>     -> {b, b' : obj cat1}
>     -> (f: mor cat2 a' a)
>     -> (g: mor cat1 b b')
>     -> compose Idris.typesAsCategoryExtensional _ _ _
>          (component (Inverse adj) (a, b))
>          (mapMor (preHomFunctor funL) (a, b) (a', b') (MkProductMorphism f g))
>      = compose Idris.typesAsCategoryExtensional _ _ _
>          (mapMor (postHomFunctor funR) (a, b) (a', b') (MkProductMorphism f g))
>          (component (Inverse adj) (a', b'))
> adjunctionInverseCommutativity {cat1} {cat2} {funL} {funR} adj {a} {a'} {b} {b'} f g =
>   commutativity (Inverse adj) (a, b) (a', b') (MkProductMorphism f g)
> -}
