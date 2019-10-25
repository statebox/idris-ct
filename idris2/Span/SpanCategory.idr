module Span.SpanCategory

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation
import Cats.FunctorsAsCategory
import Data.Vect
import Free.Path
import Span.Span
import Utils

public export
SpanMorphism : {cat : Category}
            -> {a, b : obj cat}
            -> (s1, s2 : Span {cat} a b)
            -> Type
SpanMorphism {cat} {a} {b} s1 s2 =
  (nt  : NaturalTransformation SpanIndexCategory cat (spanFunctor s1) (spanFunctor s2)
  ** e : (component nt X ~=~ identity cat a)
  **      component nt Y ~=~ identity cat b)

spanIdentity : {cat : Category}
            -> {a, b : obj cat}
            -> (s : Span {cat} a b)
            -> SpanMorphism s s
spanIdentity {cat} s =
  (  idTransformation SpanIndexCategory cat (spanFunctor s)
  ** rewrite fst $ snd s in Refl
  ** rewrite snd $ snd s in Refl)

spanComposition : {cat : Category}
               -> {a, b : obj cat}
               -> (s1, s2, s3 : Span {cat} a b)
               -> SpanMorphism s1 s2
               -> SpanMorphism s2 s3
               -> SpanMorphism s1 s3
spanComposition {cat} {a} {b} s1 s2 s3 f g =
  (  naturalTransformationComposition SpanIndexCategory
                                      cat
                                      (spanFunctor s1)
                                      (spanFunctor s2)
                                      (spanFunctor s3)
                                      (fst f)
                                      (fst g)
  ** hTrans (composeEq cat (fst $ snd s1) (fst $ snd s2) (fst $ snd s3) (fst $ snd f) (fst $ snd g))
            (leftIdentity cat a a (identity cat a))
  ** hTrans (composeEq cat (snd $ snd s1) (snd $ snd s2) (snd $ snd s3) (snd $ snd f) (snd $ snd g))
            (leftIdentity cat b b (identity cat b)))