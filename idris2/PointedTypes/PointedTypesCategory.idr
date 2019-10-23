module PointedTypes.PointedTypesCategory

import Basic.Category

public export
PointedObject : Type
PointedObject = (a : Type ** a)

public export
record PointedMorphism (a : PointedObject) (b : PointedObject) where
  constructor MkPointedMorphism
  func : (fst a) -> (fst b)
  funcRespPoint : func (snd a) = snd b

public export
pointedIdentity : (a : PointedObject) -> PointedMorphism a a
pointedIdentity (a' ** x) = MkPointedMorphism id Refl

public export
compose : (a, b, c : PointedObject) -> (f : PointedMorphism a b) -> (g : PointedMorphism b c) -> PointedMorphism a c
compose
  (a' ** x)
  (b' ** y)
  (c' ** z)
  (MkPointedMorphism f' fxy)
  (MkPointedMorphism g' gyz)
  = MkPointedMorphism (g' . f') (trans (cong g' fxy) gyz)

public export
leftReflId : (p : x = y) -> trans Refl p = p
leftReflId Refl = Refl

public export
pointedLeftIdentity :
     (a, b : PointedObject)
  -> (f : PointedMorphism a b)
  -> compose a a b (pointedIdentity a) f = f
pointedLeftIdentity
  (a' ** x)
  (b' ** y)
  (MkPointedMorphism f' fxy)
  = cong (MkPointedMorphism f') (leftReflId fxy)

public export
rightReflId : (p : x = y) -> trans p Refl = p
rightReflId Refl = Refl

public export
congId : (p : x = y) -> cong Prelude.id p = p
congId Refl = Refl

public export
pointedRightIdentity :
     (a, b : PointedObject)
  -> (f : PointedMorphism a b)
  -> compose a b b f (pointedIdentity b) = f
pointedRightIdentity
  (a' ** x)
  (b' ** y)
  (MkPointedMorphism f' fxy)
  = cong (MkPointedMorphism f') (trans (rightReflId (cong id fxy)) (congId fxy))

public export
transCongAssociacivity :
     (f : a -> b)
  -> (g : b -> c)
  -> (h : c -> d)
  -> (fxy : f x = y)
  -> (gyw : g y = w)
  -> (hwz : h w = z)
  -> trans
      (cong (h . g) fxy)
      (trans (cong h gyw) hwz)
    = trans
      (cong h (trans (cong g fxy) gyw)) hwz
transCongAssociacivity f g h Refl Refl Refl = Refl

public export
pointedAssociativity :
     (a, b, c, d : PointedObject)
  -> (f : PointedMorphism a b)
  -> (g : PointedMorphism b c)
  -> (h : PointedMorphism c d)
  -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h
pointedAssociativity
  (a' ** x)
  (b' ** y)
  (c' ** w)
  (d' ** z)
  (MkPointedMorphism f' fxy)
  (MkPointedMorphism g' gyw)
  (MkPointedMorphism h' hwz)
  = cong (MkPointedMorphism (h' . g' . f')) (transCongAssociacivity f' g' h' fxy gyw hwz)

public export
pointedTypesCategory : Category
pointedTypesCategory = MkCategory
  PointedObject
  PointedMorphism
  pointedIdentity
  compose
  pointedLeftIdentity
  pointedRightIdentity
  pointedAssociativity
