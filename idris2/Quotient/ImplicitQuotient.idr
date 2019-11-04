module Quotient.ImplicitQuotient

import Quotient.EquivalenceRelation
import Quotient.Quotient

private
data InternalQuotientType : {t : Type} -> (eq : EquivalenceRelation t) -> Type where
  InternalWrap : t -> InternalQuotientType {t} eq

public export
QuotientType : {t : Type} -> (eq : EquivalenceRelation t) -> Type
QuotientType = InternalQuotientType

public export
Wrap : t -> QuotientType {t} eq
Wrap = InternalWrap

private
unwrap : {t : Type}
      -> {eq : EquivalenceRelation t}
      -> QuotientType {t} eq
      -> t
unwrap (InternalWrap x) = x

public export
eqQuotient : {t : Type}
          -> {x, y : t}
          -> (eq : EquivalenceRelation t)
          -> (rel eq x y)
          -> Wrap {eq} x = Wrap {eq} y
eqQuotient eq prf = believe_me ()

implicitQuotientUnique : {t : Type}
                      -> {eq : EquivalenceRelation t}
                      -> (y : Type)
                      -> (f : RespectingMap t y eq)
                      -> (g : InternalQuotientType eq -> y)
                      -> (h : (x : t) -> (fst {p = \g => (a : t) -> (b : t) -> rel eq a b -> g a = g b} f x)
                                       = (g (InternalWrap x)))
                      -> (x : InternalQuotientType eq)
                      -> (g x) = (fst {p = \g => (a : t) -> (b : t) -> rel eq a b -> g a = g b} f (unwrap x))
implicitQuotientUnique {t} {eq} y f g h (InternalWrap x) = sym $ h x

public export
implicitQuotient : {t : Type}
                  -> (eq : EquivalenceRelation t)
                  -> Quotient t eq
implicitQuotient {t} eq = MkQuotient
  (QuotientType {t} eq)
  (Wrap ** (\_, _, h => eqQuotient {t} eq h))
  (\_, f => ((fst f) . unwrap ** (\x => Refl)))
  (implicitQuotientUnique {t} {eq})