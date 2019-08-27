module Quotient

import Control.Isomorphism

%access public export
%default total

extEq : (a -> b) -> (a -> b) -> Type
extEq {a} f g = (x : a) -> f x = g x

Rel : Type -> Type
Rel x = x -> x -> Type

record EqRel (x : Type) where
  constructor MkEqRel
  rel : Rel x
  refl : (a : x) -> rel a a
  sym : (a, b : x) -> rel a b -> rel b a
  trans : (a, b, c : x) -> rel a b -> rel b c -> rel a c

RespectingMap : (x, y : Type) -> EqRel x -> Type
RespectingMap x y eq = (f : (x -> y) ** ((a, b : x) -> (rel eq) a b -> f a = f b))

record Quotient (x : Type) (eq : EqRel x) where
  constructor MkQuotient
  carrier : Type
  proj : RespectingMap x carrier eq
  exists : (y : Type) -> (f : RespectingMap x y eq)
        -> (g : (carrier -> y) ** (extEq (fst f) (g . (fst proj))))
  unique : (y : Type) -> (f : RespectingMap x y eq)
        -> (g : (carrier -> y)) -> extEq (fst f) (g . (fst proj))
        -> extEq g (fst (exists y f))

existsUnique : (q : Quotient x eq) -> (f : RespectingMap x y eq)
            -> (g : carrier q -> y) -> (extEq (fst f) (g . (fst $ proj q)))
            -> (h : carrier q -> y) -> (extEq (fst f) (h . (fst $ proj q)))
            -> extEq g h
existsUnique {y=y} (MkQuotient carrier proj exists unique) f g gh h hh x =
  trans (unique y f g gh x) $ sym $ unique y f h hh x

projectionInducesIdentity : (q : Quotient x eq) -> (f : carrier q -> carrier q) -> extEq (fst $ proj q) (f . (fst $ proj q)) -> extEq f Basics.id
projectionInducesIdentity q f h x = sym $ existsUnique q (proj q) id (\a => Refl) f h x

QuotientUnique : (q, q' : Quotient x eq)
              -> (iso : Iso (carrier q) (carrier q') ** (extEq ((to iso) . (fst $ proj q)) (fst $ proj q')))
QuotientUnique q q' = let
                        (isoTo ** commTo) = exists q (carrier q') (proj q')
                        (isoFrom ** commFrom) = exists q' (carrier q) (proj q)
                        iso = MkIso isoTo isoFrom
                                (projectionInducesIdentity q' (isoTo . isoFrom) (\a => trans (commTo a) (cong $ commFrom a)))
                                (projectionInducesIdentity q (isoFrom . isoTo) (\a => trans (commFrom a) (cong $ commTo a)))
                      in (iso ** (\a => sym $ commTo a))

