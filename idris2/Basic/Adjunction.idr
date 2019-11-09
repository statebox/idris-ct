module Basic.Adjunction

import Basic.Category
import Basic.Functor
import Basic.NaturalIsomorphism
import Dual.DualCategory
import Idris.TypesAsCategoryExtensional as Idris
import Product.ProductCategory
import Profunctors.HomFunctor

public export
Adjunction : (cat1, cat2 : Category) -> CFunctor cat2 cat1 -> CFunctor cat1 cat2 -> Type
Adjunction cat1 cat2 funL funR = NaturalIsomorphism
  (productCategory (dualCategory cat2) cat1)
  Idris.typesAsCategoryExtensional
  (costar funL)
  (star funR)

adjunctionCommutativity :
       {cat1, cat2 : Category}
    -> {funL : CFunctor cat2 cat1}
    -> {funR : CFunctor cat1 cat2}
    -> (adj: Adjunction cat1 cat2 funL funR)
    -> {a, a' : obj cat2}
    -> {b, b' : obj cat1}
    -> (f: mor cat2 a' a)
    -> (g: mor cat1 b b')
    -> (h: mor cat1 (mapObj funL a) b)
    -> func (compose Idris.typesAsCategoryExtensional _ _ _
         (component (morphism adj) (a, b))
         (mapMor (star funR) (a, b) (a', b') (MkProductMorphism f g))) h
     = func (compose Idris.typesAsCategoryExtensional _ _ _
         (mapMor (costar funL) (a, b) (a', b') (MkProductMorphism f g))
         (component (morphism adj) (a', b'))) h
adjunctionCommutativity {cat1} {cat2} {funL} {funR} adj {a} {a'} {b} {b'} f g h =
  cong (\m => func m h) (commutativity (morphism adj) (a, b) (a', b') (MkProductMorphism f g))

-- adjunctionCommutativity' :
--        {cat1, cat2 : Category}
--     -> {funL : CFunctor cat2 cat1}
--     -> {funR : CFunctor cat1 cat2}
--     -> (adj: Adjunction cat1 cat2 funL funR)
--     -> {a, a' : obj cat2}
--     -> {b, b' : obj cat1}
--     -> (f: mor cat2 a' a)
--     -> (g: mor cat1 b b')
--     -> (h: mor cat1 (mapObj funL a) b)
--     -> func (mapMor (star funR) (a, b) (a', b') (MkProductMorphism f g))
--          (func (component (morphism adj) (a, b)) h)
--      = func (component (morphism adj) (a', b'))
--          (func (mapMor (costar funL) (a, b) (a', b') (MkProductMorphism f g)) h)
-- adjunctionCommutativity' {cat1} {cat2} {funL} {funR} adj {a} {a'} {b} {b'} f g h =
--   trans (sym (funcPreserveCompose (component (morphism adj) (a, b)) (mapMor (star funR) (a, b) (a', b') (MkProductMorphism f g))))
--   (trans (adjunctionCommutativity adj f g h)
--   (funcPreserveCompose (mapMor (costar funL) (a, b) (a', b') (MkProductMorphism f g)) (component (morphism adj) (a', b'))))
