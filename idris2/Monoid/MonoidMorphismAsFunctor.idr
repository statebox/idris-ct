module Monoid.MonoidMorphismAsFunctor

import Basic.Category
import Basic.Functor
import Monoid.Monoid
import Monoid.MonoidAsCategory
import Monoid.MonoidMorphism
import Utils

public export
monoidMorphismToFunctor :
     (monoid1, monoid2 : Monoid)
  -> MonoidMorphism monoid1 monoid2
  -> CFunctor (monoidAsCategory monoid1) (monoidAsCategory monoid2)
monoidMorphismToFunctor monoid1 monoid2 (MkMonoidMorphism fun frOp frId) =
  MkCFunctor
    id
    (\_, _ => fun)
    (\_ => frId)
    (\_, _, _, f, g => frOp f g)