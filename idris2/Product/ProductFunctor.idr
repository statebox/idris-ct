module Product.ProductFunctor

import Basic.Category
import Basic.Functor
import Product.ProductCategory
import Utils

public export
productFunctor :
     CFunctor cat1 cat2
  -> CFunctor cat3 cat4
  -> CFunctor (productCategory cat1 cat3) (productCategory cat2 cat4)
productFunctor func1 func2 = MkCFunctor
  (\a => (mapObj func1 (fst a), mapObj func2 (snd a)))
  (\a, b, f => MkProductMorphism (mapMor func1 (fst a) (fst b) (pi1 f)) (mapMor func2 (snd a) (snd b) (pi2 f)))
  (\a => cong2 (MkProductMorphism {a = (mapObj func1 (fst a), mapObj func2 (snd a))}
                                  {b = (mapObj func1 (fst a), mapObj func2 (snd a))}
               )
               (preserveId func1 (fst a))
               (preserveId func2 (snd a))
  )
  (\a, b, c, f, g => cong2 MkProductMorphism (preserveCompose func1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
                                             (preserveCompose func2 (snd a) (snd b) (snd c) (pi2 f) (pi2 g)))
