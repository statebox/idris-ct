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
