module Monad.KleisliCategory

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation
import Monad.Monad

%access public export
%default total

kleisliCategory : (cat : Category) -> UnlawfulMonad cat -> Category
kleisliCategory cat m =
  MkCategory
    (obj cat)
    (\a, b => mor cat a (mapObj (functor m) b))
    (\a => component (unit m) a)
    (\a, b, c, f, g =>
      compose cat _ _ _
        (compose cat _ _ _ f (mapMor (functor m) _ _ g))
        (component (multiplication m) c))
    ?leftId
    ?rightId
    ?assoc
