module Preorder.UniquePreorder

public export
interface Preorder t (po : t -> t -> Type) where
  transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c
  reflexive : (a : t) -> po a a

public export
interface Preorder t po => UniquePreorder t (po : t -> t -> Type) where
  unique : (a, b : t) -> (f, g : po a b) -> f = g
