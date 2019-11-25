module Day.CovariantDayConvolution

import Basic.Functor
import Comonad.Comonad
import Idris.TypesAsCategoryExtensional
import Monad.Monad
import MonoidalCategory.MonoidalCategory
import Utils

Day :
     {moncat : MonoidalCategory}
  -> (fun1, fun2 : CFunctor (cat moncat) TypesAsCategoryExtensional.typesAsCategoryExtensional)
  -> CFunctor (cat moncat) TypesAsCategoryExtensional.typesAsCategoryExtensional
Day {moncat} fun1 fun2 = MkCFunctor
  (\a => (  x : obj (cat moncat)
         ** (y : obj (cat moncat)
         ** (mapObj fun1 x, mapObj fun2 y, mor (cat moncat) (mapObj (tensor moncat) (x, y)) a))))
  (\a, b, f => MkExtensionalTypeMorphism
                 (\k => (  (fst k)
                        ** (fst $ snd k)
                        ** ( fst (DPair.snd $ DPair.snd k)
                           , fst $ snd (DPair.snd $ DPair.snd k)
                           , compose (cat moncat)
                                     (mapObj (tensor moncat) (fst k, fst $ snd k))
                                     a
                                     b
                                     (snd $ snd (DPair.snd $ DPair.snd k)) f))))
  (\a => funExt (\x => dPairEq Refl (dPairEq Refl (pairEq Refl (pairEq Refl
           (rightIdentity (cat moncat)
                          (mapObj (tensor moncat) (fst x, fst (snd x)))
                          a
                          (snd (snd (snd (snd x))))))))))
  (\a, b, c, f, g => funExt (\x => dPairEq Refl (dPairEq Refl (pairEq Refl (pairEq Refl
                       (associativity (cat moncat)
                                      (mapObj (tensor moncat) (fst x, fst (snd x)))
                                      a
                                      b
                                      c
                                      (snd (snd (snd (snd x))))
                                      f
                                      g))))))
