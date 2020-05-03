module Tactics.MorphismTest

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation
import Syntax.PreorderReasoning
import Tactics

%language ElabReflection

naturalTransformationCompositionTest :
     (cat1, cat2 : Category)
  -> (fun1, fun2, fun3 : CFunctor cat1 cat2)
  -> NaturalTransformation cat1 cat2 fun1 fun2
  -> NaturalTransformation cat1 cat2 fun2 fun3
  -> NaturalTransformation cat1 cat2 fun1 fun3
naturalTransformationCompositionTest cat1 cat2 fun1 fun2 fun3
  (MkNaturalTransformation comp1 comm1)
  (MkNaturalTransformation comp2 comm2) =
    MkNaturalTransformation
      (\a => compose cat2 (mapObj fun1 a) (mapObj fun2 a) (mapObj fun3 a) (comp1 a) (comp2 a))
      (\a, b, f =>
        (compose cat2 _ _ _ (compose cat2 _ _ _ (comp1 a) (comp2 a)) (mapMor fun3 a b f))
        -- I did tests at the following equality. If you run :elab h <RET>
        -- intros <RET> morphism <RET> :qed, the goal gets solved. However, if
        -- you paste the corresponding code into the hole, it just runs forever.
        -- `%runElab morphism` in place of the hole should also work, but has
        -- the same issue. Similar behaviour can be seen elsewhere, where it
        -- runs fine interactively, but when used in a file it requires extra
        -- annotations or sometimes doesn't work at all.
          ={ %runElab morphism }=
        -- The following line works, but that's of course not really what we want
          -- ={ the ((compose _ _ _ _ (compose _ _ _ _ (comp1 a) (comp2 a)) (mapMor fun3 a b f)) = 
          --         (compose _ _ _ _ (comp1 a) (compose _ _ _ _ (comp2 a) (mapMor fun3 a b f)))) 
          --        (%runElab morphism) }=
        (compose _ _ _ _ (comp1 a) (compose _ (mapObj fun2 a) (mapObj fun3 a) (mapObj fun3 b) (comp2 a) (mapMor fun3 a b f)))
          ={ cong $ comm2 a b f }=
        (compose cat2 _ _ _ (comp1 a) (compose cat2 _ _ _ (mapMor fun2 _ _ f) (comp2 b)))
          ={ associativity cat2 _ _ _ _ (comp1 a) (mapMor fun2 a b f) (comp2 b) }=
        (compose cat2 _ _ _ (compose cat2 _ _ _ (comp1 a) (mapMor fun2 _ _ f)) (comp2 b))
          ={ cong {f = \h => compose cat2 _ _ _ h (comp2 b)} $ comm1 a b f }=
        (compose cat2 _ _ _ (compose cat2 _ _ _ (mapMor fun1 a b f) (comp1 b)) (comp2 b))
          ={ sym $ associativity cat2 _ _ _ _ (mapMor fun1 _ _ f) (comp1 b) (comp2 b) }=
        (compose cat2 _ _ _ (mapMor fun1 _ _ f) (compose cat2 _ _ _ (comp1 b) (comp2 b)))
      QED)