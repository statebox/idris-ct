module CoLimits.CoProduct

import Basic.Category

public export
record CommutingMorphism
 (cat : Category)
 (a : obj cat) (b : obj cat) (carrier : obj cat) (c : obj cat)
 (inl : mor cat a carrier) (inr : mor cat b carrier)
 (f : mor cat a c) (g : mor cat b c)
where
  constructor MkCommutingMorphism
  challenger         : mor cat carrier c
  commutativityLeft  : compose cat a carrier c inl challenger = f
  commutativityRight : compose cat b carrier c inr challenger = g

public export
record CoProduct
  (cat : Category)
  (a : obj cat) (b : obj cat)
where
  constructor MkCoProduct
  carrier: obj cat
  inl: mor cat a carrier
  inr: mor cat b carrier
  exists:
       (c : obj cat)
    -> (f : mor cat a c)
    -> (g : mor cat b c)
    -> CommutingMorphism cat a b carrier c inl inr f g
  unique:
       (c : obj cat)
    -> (f : mor cat a c)
    -> (g : mor cat b c)
    -> (h : CommutingMorphism cat a b carrier c inl inr f g)
    -> challenger h = challenger (exists c f g)