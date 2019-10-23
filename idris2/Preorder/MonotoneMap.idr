module Preorder.MonotoneMap

public export
record MonotoneMap (t1 : Type) (po1 : t1 -> t1 -> Type) (t2 : Type) (po2 : t2 -> t2 -> Type) where
  constructor MkMonotoneMap
  func : t1 -> t2
  funcRespOrd : (a, b : t1) -> po1 a b -> po2 (func a) (func b)
