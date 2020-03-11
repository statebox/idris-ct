module Monoid.MonoidMorphism

import Monoid.Monoid
import Utils

public export
record MonoidMorphism (domain : Monoid) (codomain : Monoid) where
  constructor MkMonoidMorphism
  func       : set domain -> set codomain
  funcRespOp : (a, b : set domain)
            -> func ((<+>) @{verifiedMonoidToSemigroup @{axioms domain}} a b)
             = (<+>) @{verifiedMonoidToSemigroup @{axioms codomain}} (func a) (func b)
  funcRespId : func (neutral @{verifiedMonoidToMonoid @{axioms domain}})
             = neutral @{verifiedMonoidToMonoid @{axioms codomain}}

public export
monoidMorphismEq :
     (mor1, mor2 : MonoidMorphism m1 m2)
  -> ((x : set m1) -> (func mor1 x) = (func mor2 x))
  -> mor1 = mor2
monoidMorphismEq mor1 mor2 pointWisePrf = believe_me pointWisePrf

public export
monoidIdentity : (m : Monoid) -> MonoidMorphism m m
monoidIdentity m = MkMonoidMorphism
  id
  (\_, _ => Refl)
  Refl

public export
monoidMorphismsComposition :
     MonoidMorphism a b
  -> MonoidMorphism b c
  -> MonoidMorphism a c
monoidMorphismsComposition mor1 mor2 =
  MkMonoidMorphism
    ((func mor2) . (func mor1))
    (\a, b => trans (cong (func mor2) (funcRespOp mor1 a b)) (funcRespOp mor2 (func mor1 a) (func mor1 b)))
    (trans (cong (func mor2) (funcRespId mor1)) (funcRespId mor2))