module Monoid.MonoidsCategory

import Basic.Category
import Monoid.Monoid
import Monoid.MonoidMorphism
import Utils

public export
monoidsLeftIdentity :
     (m1, m2 : Monoid)
  -> (mor : MonoidMorphism m1 m2)
  -> monoidMorphismsComposition (monoidIdentity m1) mor = mor
monoidsLeftIdentity m1 m2 mor = monoidMorphismEq
  (monoidMorphismsComposition (monoidIdentity m1) mor)
  mor
  (\x => Refl)

public export
monoidRightIdentity :
     (m1, m2 : Monoid)
  -> (mor : MonoidMorphism m1 m2)
  -> monoidMorphismsComposition mor (monoidIdentity m2) = mor
monoidRightIdentity m1 m2 mor = monoidMorphismEq
  (monoidMorphismsComposition mor (monoidIdentity m2))
  mor
  (\x => Refl)


public export
monoidAssociativity :
     (m1, m2, m3, m4 : Monoid)
  -> (mor1 : MonoidMorphism m1 m2)
  -> (mor2 : MonoidMorphism m2 m3)
  -> (mor3 : MonoidMorphism m3 m4)
  -> monoidMorphismsComposition mor1 (monoidMorphismsComposition mor2 mor3)
   = monoidMorphismsComposition (monoidMorphismsComposition mor1 mor2) mor3
monoidAssociativity m1 m2 m3 m4 mor1 mor2 mor3 = monoidMorphismEq
  (monoidMorphismsComposition mor1 (monoidMorphismsComposition mor2 mor3))
  (monoidMorphismsComposition (monoidMorphismsComposition mor1 mor2) mor3)
  (\x => Refl)

public export
monoidsCategory : Category
monoidsCategory = MkCategory
  Monoid
  MonoidMorphism
  monoidIdentity
  (\m1, m2, m3 => monoidMorphismsComposition {a = m1} {b = m2} {c = m3})
  monoidsLeftIdentity
  monoidRightIdentity
  monoidAssociativity