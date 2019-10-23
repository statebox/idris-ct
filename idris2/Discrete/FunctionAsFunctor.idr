module Discrete.FunctionAsFunctor

import Basic.Category
import Basic.Functor
import Discrete.DiscreteCategory

public export
functionMapMor : (f : a -> b) -> (x, y : a) -> DiscreteMorphism x y -> DiscreteMorphism (f x) (f y)
functionMapMor f x x Refl = Refl

public export
functionPreserveCompose :
     (f : a -> b)
  -> (x, y, z : a)
  -> (g : DiscreteMorphism x y)
  -> (h : DiscreteMorphism y z)
  -> functionMapMor f x z (discreteCompose x y z g h)
   = discreteCompose (f x) (f y) (f z) (functionMapMor f x y g) (functionMapMor f y z h)
functionPreserveCompose f x x x Refl Refl = Refl

public export
functionAsFunctor :
     (f : a -> b)
  -> CFunctor (discreteCategory a) (discreteCategory b)
functionAsFunctor f = MkCFunctor
  f
  (functionMapMor f)
  (\_ => Refl)
  (functionPreserveCompose f)