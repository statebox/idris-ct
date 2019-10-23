module Discrete.DiscreteCategory

import Basic.Category

public export
DiscreteMorphism : (x, y : a) -> Type
DiscreteMorphism x y = x = y

public export
discreteIdentity : (x : a) -> DiscreteMorphism x x
discreteIdentity _ = Refl

public export
discreteCompose : (x, y, z : a) -> DiscreteMorphism x y -> DiscreteMorphism y z -> DiscreteMorphism x z
discreteCompose _ _ _ Refl Refl = Refl

public export
discreteLeftIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x x y (discreteIdentity x) f = f
discreteLeftIdentity _ _ Refl = Refl

public export
discreteRightIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x y y f (discreteIdentity y) = f
discreteRightIdentity _ _ Refl = Refl

public export
discreteAssociativity : (w, x, y, z : a)
                     -> (f : DiscreteMorphism w x)
                     -> (g : DiscreteMorphism x y)
                     -> (h : DiscreteMorphism y z)
                     -> discreteCompose w x z f (discreteCompose x y z g h)
                      = discreteCompose w y z (discreteCompose w x y f g) h
discreteAssociativity _ _ _ _ Refl Refl Refl = Refl

public export
discreteCategory : (a : Type) -> Category
discreteCategory a = MkCategory
  a
  DiscreteMorphism
  discreteIdentity
  discreteCompose
  discreteLeftIdentity
  discreteRightIdentity
  discreteAssociativity