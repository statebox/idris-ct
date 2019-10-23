module Idris.EitherAsCoProduct

import Idris.TypesAsCategoryExtensional
import Basic.Category
import CoLimits.CoProduct

public export
applyLeftOrRight :
     (a, b, c : Type)
  -> (f : ExtensionalTypeMorphism a c)
  -> (g : ExtensionalTypeMorphism b c)
  -> ExtensionalTypeMorphism (Either a b) c
applyLeftOrRight a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) =
  (MkExtensionalTypeMorphism (either f g))

public export
leftCompose :
     (a, b, c : Type)
  -> (f : ExtensionalTypeMorphism a c)
  -> (g : ExtensionalTypeMorphism b c)
  -> extCompose a (Either a b) c (MkExtensionalTypeMorphism Left) (applyLeftOrRight a b c f g) = f
leftCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl

public export
rightCompose :
     (a, b, c : Type)
  -> (f : ExtensionalTypeMorphism a c)
  -> (g : ExtensionalTypeMorphism b c)
  -> extCompose b (Either a b) c (MkExtensionalTypeMorphism Right) (applyLeftOrRight a b c f g) = g
rightCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl

public export
applyExtWith :
     (x : a)
  -> (f : ExtensionalTypeMorphism a b)
  -> b
applyExtWith x f = apply (func f) x

public export
unique :
     (f : ExtensionalTypeMorphism a c)
  -> (g : ExtensionalTypeMorphism b c)
  -> (h : ExtensionalTypeMorphism (Either a b) c)
  -> (commutativityLeft : extCompose a (Either a b) c (MkExtensionalTypeMorphism Left) h = f)
  -> (commutativityRight: extCompose b (Either a b) c (MkExtensionalTypeMorphism Right) h = g)
  -> h = applyLeftOrRight a b c f g
unique (MkExtensionalTypeMorphism f)
       (MkExtensionalTypeMorphism g)
       (MkExtensionalTypeMorphism h)
       commutativityLeft
       commutativityRight =
  funExt(\x =>
    case x of
      Left l  => cong (applyExtWith l) commutativityLeft
      Right r => cong (applyExtWith r) commutativityRight
  )

public export
eitherToCoProduct : (a, b : Type) -> CoProduct Idris.TypesAsCategoryExtensional.typesAsCategoryExtensional a b
eitherToCoProduct a b = MkCoProduct
  (Either a b)
  (MkExtensionalTypeMorphism Left)
  (MkExtensionalTypeMorphism Right)
  (\c, f, g => MkCommutingMorphism (applyLeftOrRight a b c f g) (leftCompose a b c f g) (rightCompose a b c f g))
  (\c, f, g, h => unique f g (challenger h) (commutativityLeft h) (commutativityRight h))