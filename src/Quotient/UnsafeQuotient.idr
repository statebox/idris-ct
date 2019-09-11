module Quotient.UnsafeQuotient

import Quotient.Quotient

%default total
%access export

private
data InternalQuotientType : (x : Type) -> (eq : EqRel x) -> Type where
  InternalWrap : x -> InternalQuotientType x eq

QuotientType : (x : Type) -> (eq : EqRel x) -> Type
QuotientType = InternalQuotientType

Wrap : x -> QuotientType x eq
Wrap = InternalWrap

private
unwrap : QuotientType x eq -> x
unwrap (InternalWrap a) = a

postulate
QuotientEquality : (x : Type) -> (eq : EqRel x) -> (rel eq a b) -> Wrap a = Wrap b

UnsafeQuotient : (x : Type) -> (eq : EqRel x) -> Quotient x eq
UnsafeQuotient x eq = MkQuotient
  (QuotientType x eq)
  (Wrap ** (\a, b, h => QuotientEquality x eq h))
  (\y, f => ((\a => fst f $ unwrap a) ** (\a => Refl)))
  (\y, f, g, h, (InternalWrap a) => sym $ h a)

UnsafeQuotient' : (x : Type) -> (eq : Rel x) -> Quotient' x eq
UnsafeQuotient' x eq = UnsafeQuotient x (EqClosure eq)
