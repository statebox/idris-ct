module Profunctors.HomFunctor

import Basic.Category
import Basic.Functor
import Dual.DualFunctor
import Idris.TypesAsCategoryExtensional
import Product.ProductCategory
import Product.ProductFunctor
import Profunctors.Profunctor

public export
homFunctor : (cat : Category) -> Profunctor cat cat
homFunctor cat = MkCFunctor
  (\a => mor cat (fst a) (snd a))
  (\a, b, f => MkExtensionalTypeMorphism (\h => compose cat (fst b) (fst a) (snd b) (pi1 f) (compose cat (fst a) (snd a) (snd b) h (pi2 f))))
  (\a => funExt (\x => trans (leftIdentity cat (fst a) (snd a) _) (rightIdentity cat (fst a) (snd a) x)))
  (\a, b, c, f, g => funExt (\x =>
    trans (sym (associativity cat _ _ _ _ (pi1 g) (pi1 f) _))
    (cong (compose cat (fst c) (fst b) (snd c) (pi1 g)) (
      trans (cong (compose cat (fst b) (fst a) (snd c) (pi1 f)) (associativity cat _ _ _ _ x (pi2 f) (pi2 g)))
      (associativity cat _ _ _ _ (pi1 f) _ (pi2 g))))))

-- costar f takes f : C -> D to D(F, 1)
public export
costar : {cat1, cat2 : Category}
      -> CFunctor cat1 cat2
      -> Profunctor cat2 cat1
costar {cat2} f = functorComposition _ _ _ (productFunctor (dualFunctor f) (idFunctor cat2)) (homFunctor cat2)

-- star f takes f : C -> D to D(1, F)
public export
star : {cat1, cat2 : Category}
    -> CFunctor cat1 cat2
    -> Profunctor cat1 cat2
star {cat2} f = functorComposition _ _ _ (productFunctor (dualFunctor (idFunctor cat2)) f) (homFunctor cat2)
