module Lens.SymmetricBimorphicLens

import Basic.Category
import Quotient.EquivalenceRelation
import Quotient.ImplicitQuotient
import Quotient.Quotient

record SymmetricBimorphicLens (S : Type) (T : Type) (A : Type) (B : Type) where
  constructor MkSymmetricBimorphicLens
  X           : Type
  Y           : X -> Type
  leftView    : X -> S
  rightView   : X -> A
  leftUpdate  : (x : X) -> T -> Y x
  rightUpdate : (x : X) -> B -> Y x

idSymmetricBimorphicLens : {s, t : Type} -> SymmetricBimorphicLens s t s t
idSymmetricBimorphicLens {s} {t} = MkSymmetricBimorphicLens
  s
  (const t)
  id
  id
  (const id)
  (const id)

TypePullback : {x, y, z : Type}
            -> (f : x -> z)
            -> (g : y -> z)
            -> Type
TypePullback {x} {y} {z} f g = (p : (x, y) ** f (fst p) = g (snd p))

typePushoutRelation : {x, y, z : Type}
                   -> (f : z -> x)
                   -> (g : z -> y)
                   -> Relation (Either x y)
typePushoutRelation {x} {y} {z} f g (Left a) (Right b) = (k : z ** p : (f k = a) ** g k = b)
typePushoutRelation {x} {y} {z} f g _        _         = Void

TypePushout : {x, y, z : Type}
           -> (f : z -> x)
           -> (g : z -> y)
           -> Type
TypePushout {x} {y} {z} f g = QuotientType {t=Either x y} (equivalenceClosure $ typePushoutRelation f g)

symmetricBimorphicLensComposition : {s, t, a, b, c, d : Type}
                                 -> SymmetricBimorphicLens s t a b
                                 -> SymmetricBimorphicLens a b c d
                                 -> SymmetricBimorphicLens s t c d
symmetricBimorphicLensComposition (MkSymmetricBimorphicLens x1 y1 lv1 rv1 lu1 ru1)
                                  (MkSymmetricBimorphicLens x2 y2 lv2 rv2 lu2 ru2) =
  MkSymmetricBimorphicLens
    (TypePullback {x=x1} {y=x2} {z=a} rv1 lv2)
    (\xx => TypePushout {x=y1 $ fst $ fst xx} {y=y2 $ snd $ fst xx} {z=b} (ru1 $ fst $ fst xx) (lu2 $ snd $ fst xx))
    (lv1 . fst . fst)
    (rv2 . snd . fst)
    (\xx, t => Wrap $ Left $ lu1 (fst $ fst xx) t)
    (\xx, d => Wrap $ Right $ ru2 (snd $ fst xx) d)

symmetricBimorphicLensCategory : Category
symmetricBimorphicLensCategory = MkCategory
  (Type, Type)
  (\st, ab => SymmetricBimorphicLens (fst st) (snd st) (fst ab) (snd ab))
  (\st => idSymmetricBimorphicLens {s=fst st} {t=snd st})
  (\st, ab, cd => symmetricBimorphicLensComposition {s=fst st} {t=snd st} {a=fst ab} {b=snd ab} {c=fst cd} {d=snd cd})
  ?lId
  ?rId
  ?assoc