module Hom.HomFunctor

import Basic.Category
import Basic.Functor
import Dual.DualCategory
import Dual.DualFunctor
import Idris.TypesAsCategoryExtensional as Idris
import Product.ProductCategory
import Product.ProductFunctor
import Profunctors.Profunctor

public export
homFunctor : (cat : Category) -> Profunctor cat cat
homFunctor cat = MkCFunctor
  (\a => mor cat (fst a) (snd a))
  (\a, b, f => MkExtensionalTypeMorphism (\h => compose cat (fst b) (fst a) (snd b)
                                                        (pi1 f)
                                                        (compose cat (fst a) (snd a) (snd b) h (pi2 f))))
  (\a => Idris.funExt (\x => trans (leftIdentity cat (fst a) (snd a) _) (rightIdentity cat (fst a) (snd a) x)))
  (\a, b, c, f, g => Idris.funExt (\x =>
    trans (sym (associativity cat _ _ _ _ (pi1 g) (pi1 f) _))
          (cong (compose cat (fst c) (fst b) (snd c) (pi1 g))
                (trans (cong (compose cat (fst b) (fst a) (snd c) (pi1 f))
                             (associativity cat _ _ _ _ x (pi2 f) (pi2 g)))
                       (associativity cat _ _ _ _ (pi1 f) _ (pi2 g))))))

-- postCompose cat a is Hom(a,–), it takes a morphism g to \f => (f; g)
postCompose : (cat : Category) -> (a : obj cat) -> CFunctor cat Idris.typesAsCategoryExtensional
postCompose cat a = MkCFunctor
  (\b => mor cat a b)
  (\b, c, g => MkExtensionalTypeMorphism (\f => compose cat a b c f g))
  (\b => Idris.funExt (\f => rightIdentity cat a b f))
  (\b, c, d, g, h => Idris.funExt (\f => associativity cat a b c d f g h))

-- preCompose cat a is Hom(–,a), it takes a morphism g to \f => (g; f)
preCompose : (cat : Category) -> (a : obj cat) -> CFunctor (dualCategory cat) Idris.typesAsCategoryExtensional
preCompose cat a = MkCFunctor
  (\b => mor cat b a)
  (\b, c, g => MkExtensionalTypeMorphism (\f => compose cat c b a g f))
  (\b => Idris.funExt (\f => leftIdentity cat b a f))
  (\b, c, d, g, h => Idris.funExt (\f => sym (associativity cat d c b a h g f)))

-- costar f takes f : C -> D to D(f, 1)
public export
costar : {cat1, cat2 : Category}
      -> CFunctor cat1 cat2
      -> Profunctor cat2 cat1
costar {cat2} f = functorComposition _ _ _ (productFunctor (dualFunctor f) (idFunctor cat2)) (homFunctor cat2)

-- star f takes f : C -> D to D(1, f)
public export
star : {cat1, cat2 : Category}
    -> CFunctor cat1 cat2
    -> Profunctor cat1 cat2
star {cat2} f = functorComposition _ _ _ (productFunctor (dualFunctor (idFunctor cat2)) f) (homFunctor cat2)
