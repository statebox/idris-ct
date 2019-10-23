module Idris.TypesAsCategory

import Basic.Category

public export
TypeMorphism : Type -> Type -> Type
TypeMorphism a b = a -> b

public export
identity : (a : Type) -> TypeMorphism a a
identity a = id

public export
compose :
     (a, b, c : Type)
  -> (f : TypeMorphism a b)
  -> (g : TypeMorphism b c)
  -> TypeMorphism a c
compose a b c f g = g . f

public export
leftIdentity :
     (a, b : Type)
  -> (f : TypeMorphism a b)
  -> f . (identity a) = f
leftIdentity a b f = Refl

public export
rightIdentity :
     (a, b : Type)
  -> (f : TypeMorphism a b)
  -> (identity b) . f = f
rightIdentity a b f = Refl

public export
associativity :
     (a, b, c, d : Type)
  -> (f : TypeMorphism a b)
  -> (g : TypeMorphism b c)
  -> (h : TypeMorphism c d)
  -> (h . g) . f = h . (g . f)
associativity a b c d f g h = Refl

public export
typesAsCategory : Category
typesAsCategory = MkCategory
  Type
  TypeMorphism
  identity
  (\a => compose a)
  leftIdentity
  rightIdentity
  associativity
