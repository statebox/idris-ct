module Basic.Category

public export
record Category where
  constructor MkCategory
  obj           : Type
  mor           : obj -> obj -> Type
  identity      : (a : obj) -> mor a a
  compose       : (a, b, c : obj)
               -> (f : mor a b)
               -> (g : mor b c)
               -> mor a c
  leftIdentity  : (a, b : obj)
               -> (f : mor a b)
               -> compose a a b (identity a) f = f
  rightIdentity : (a, b : obj)
               -> (f : mor a b)
               -> compose a b b f (identity b) = f
  associativity : (a, b, c, d : obj)
               -> (f : mor a b)
               -> (g : mor b c)
               -> (h : mor c d)
               -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h

public export
castMor : {cat : Category}
     -> {x1, x2, y1, y2 : obj cat}
     -> x1 = x2
     -> y1 = y2
     -> mor cat x1 y1
     -> mor cat x2 y2
castMor Refl Refl = id

public export
composeEq : (cat : Category)
         -> {x1, x2, y1, y2, z1, z2 : obj cat}
         -> {f1 : mor cat x1 y1} -> {f2 : mor cat x2 y2} -> {g1 : mor cat y1 z1} -> {g2 : mor cat y2 z2}
         -> x1 = x2 -> y1 = y2 -> z1 = z2 -> f1 ~=~ f2 -> g1 ~=~ g2
         -> compose cat x1 y1 z1 f1 g1 ~=~ compose cat x2 y2 z2 f2 g2
composeEq cat Refl Refl Refl Refl Refl = Refl
