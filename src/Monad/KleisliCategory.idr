module Monad.KleisliCategory

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation
import Monad.Monad

%access public export
%default total

kleisliCategory : (cat : Category) -> Monad cat -> Category
kleisliCategory cat m =
  MkCategory
    (obj cat)
    (\a, b => mor cat a (mapObj (functor m) b))
    (\a => component (unit m) a)
    (\a, b, c, f, g =>
      compose cat _ _ _
        (compose cat _ _ _ f (mapMor (functor m) _ _ g))
        (component (multiplication m) c))
    (\a, b, f => ?asdf)
    (\a, b, f => trans (sym $ associativity cat a
                                                (mapObj (functor m) b)
                                                (mapObj (functor m) (mapObj (functor m) b))
                                                (mapObj (functor m) b)
                                                f
                                                (mapMor (functor m) b (mapObj (functor m) b) (component (unit m) b))
                                                (component (multiplication m) b))
                       -- ?qwer)
                       (trans (cong {f = compose cat a (mapObj (functor m) b) (mapObj (functor m) b) f}
                                    (cong {f = \nt => component nt b} (leftUnit m)))
                              (rightIdentity cat a (mapObj (functor m) b) f)))
    ?assoc
