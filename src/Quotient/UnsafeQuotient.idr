module UnsafeQuotient

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

unwrap : QuotientType x eq -> x
unwrap (InternalWrap a) = a

wrapUnwrapId : (a : QuotientType x eq) -> a = Wrap (unwrap a)
wrapUnwrapId (InternalWrap a) = Refl

postulate
QuotientEquality : (x : Type) -> (eq : EqRel x) -> (rel eq a b) -> Wrap a = Wrap b

UnsafeQuotient : (x : Type) -> (eq : EqRel x) -> Quotient x eq
UnsafeQuotient x eq = MkQuotient
                        (QuotientType x eq)
                        (Wrap ** (\a, b, h => QuotientEquality x eq h))
                        (\y, f => ((\a => fst f $ unwrap a) ** (\a => Refl)))
                        (\y, f, g, h, a => trans (cong $ wrapUnwrapId a) (sym $ h $ unwrap a))
