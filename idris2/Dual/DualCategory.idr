module Dual.DualCategory

import Basic.Category

public export
dualMorphism :
     (cat : Category)
  -> (a, b  : obj cat)
  -> Type
dualMorphism cat a b = mor cat b a

public export
dualCompose :
     (cat : Category)
  -> (a, b, c : obj cat)
  -> (f : dualMorphism cat a b)
  -> (g : dualMorphism cat b c)
  -> dualMorphism cat a c
dualCompose cat a b c f g = (compose cat) c b a g f

public export
dualAssoc :
     (cat : Category)
  -> (a, b, c, d : obj cat)
  -> (f : dualMorphism cat a b)
  -> (g : dualMorphism cat b c)
  -> (h : dualMorphism cat c d)
  ->  dualCompose cat a b d f (dualCompose cat b c d g h)
      = dualCompose cat a c d (dualCompose cat a b c f g) h
dualAssoc cat a b c d f g h = sym (associativity cat d c b a h g f)

public export
dualLeftIdentity :
     (cat : Category)
  -> (a, b : obj cat)
  -> (f : dualMorphism cat a b)
  -> dualCompose cat a a b (identity cat a) f = f
dualLeftIdentity cat a b f = rightIdentity cat b a f

public export
dualRightIdentity :
     (cat : Category)
  -> (a, b : obj cat)
  -> (f : dualMorphism cat a b)
  -> dualCompose cat a b b f (identity cat b) = f
dualRightIdentity cat a b f = leftIdentity cat b a f

public export
dualCategory : (cat : Category) -> Category
dualCategory cat = MkCategory
  (obj cat)
  (dualMorphism cat)
  (identity cat)
  (dualCompose cat)
  (dualLeftIdentity cat)
  (dualRightIdentity cat)
  (dualAssoc cat)
