module Quotient.Quotients

import Quotient.Quotient

%access public export
%default total

trivialEqRel : (x : Type) -> EqRel x
trivialEqRel x = MkEqRel (\x, y => x = y) (\x => Refl) (\x, y, r => sym r) (\x, y, z, l, r => trans l r)

trivialQuotient : (x : Type) -> Quotient x $ trivialEqRel x
trivialQuotient x = MkQuotient x
                      ((id {a=x}) ** (\a, b, h => h))
                      (\y, f => ((fst f) ** (\a => Refl)))
                      (\y, f, g, h, a => sym $ h a)

fullEqRel : (x : Type) -> EqRel x
fullEqRel x = MkEqRel (\x, y => ()) (\x => ()) (\x, y, r => ()) (\x, y, z, l, r => ())

fullQuotient : (x : Type) -> (a : x) -> Quotient x $ fullEqRel x
fullQuotient x a = MkQuotient ()
                     ((\b => ()) ** (\a, b, h => Refl))
                     (\y, f => ((\b => (fst f) a) ** (\b => snd f b a ())))
                     (\y, f, g, h, () => sym $ h a)
