module MonoidalCategory.StrictMonoidalCategory

import Basic.Category
import Basic.Functor
import Product.ProductCategory

public export
record StrictMonoidalCategory where
  constructor MkStrictMonoidalCategory
  cat : Category
  tensor : CFunctor (productCategory cat cat) cat
  unit : obj cat
  tensorIsLeftUnital  : (a : obj cat) -> mapObj tensor (unit, a) = a
  tensorIsRightUnital : (a : obj cat) -> mapObj tensor (a, unit) = a
  tensorIsAssociativeObj : (a, b, c : obj cat)
                        -> mapObj tensor (a, mapObj tensor (b, c)) = mapObj tensor (mapObj tensor (a, b), c)
  --tensorIsAssociativeMor : (a, b, c, d, e, f : obj cat)
  --                      -> (g : mor cat a b)
  --                      -> (h : mor cat c d)
  --                      -> (k : mor cat e f)
  --                      -> mapMor tensor
  --                                (a, mapObj tensor (c,e))
  --                                (b, mapObj tensor (d,f))
  --                                (MkProductMorphism g (mapMor tensor (c,e) (d,f) (MkProductMorphism h k)))
  --                       = mapMor tensor
  --                                (mapObj tensor (a,c), e)
  --                                (mapObj tensor (b,d), f)
  --                                (MkProductMorphism (mapMor tensor (a,c) (b,d) (MkProductMorphism g h)) k)