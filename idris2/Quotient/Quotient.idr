module Quotient.Quotient

import Quotient.EquivalenceRelation

extEq : (a -> b) -> (a -> b) -> Type
extEq {a} f g = (x : a) -> f x = g x

public export
RespectingMap : (x, y : Type) -> EquivalenceRelation x -> Type
RespectingMap x y eq = (f : (x -> y) ** ((a, b : x) -> (rel eq) a b -> f a = f b))

public export
record Quotient (x : Type) (eq : EquivalenceRelation x) where
  constructor MkQuotient
  carrier : Type
  proj : RespectingMap x carrier eq
  exists : (y : Type)
        -> (f : RespectingMap x y eq)
        -> (g : (carrier -> y) ** (extEq (fst f) (g . (fst proj))))
  unique : (y : Type)
        -> (f : RespectingMap x y eq)
        -> (g : (carrier -> y))
        -> extEq (fst f) (g . (fst proj))
        -> extEq g (fst (exists y f))

public export
ClosureQuotient : (x : Type) -> Relation x -> Type
ClosureQuotient x rel = Quotient x (equivalenceClosure rel)