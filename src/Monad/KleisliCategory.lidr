\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

> module Monad.KleisliCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Monad.Monad
>
> %access public export
> %default total
>
> -- TODO : this should be useless. Modify the definition of `naturalTransformationComposition` so that we can remove this
> natTransComposeEquality :
>      (f : CFunctor cat cat)
>   -> (m : NaturalTransformation cat cat f (functorComposition cat cat cat f f))
>   -> (n : NaturalTransformation cat cat (functorComposition cat cat cat f f) f)
>   -> compose cat (mapObj f a)
>                  (mapObj f (mapObj f a))
>                  (mapObj f a)
>                  (component m a)
>                  (component n a)
>    = component (naturalTransformationComposition cat cat f (functorComposition cat cat cat f f) f m n) a
> natTransComposeEquality f (MkNaturalTransformation mComp mComm) (MkNaturalTransformation nComp nComm) = Refl
>
> kleisliCategory : {cat : Category} -> Monad cat -> Category
> kleisliCategory {cat} m = MkCategory
>   (obj cat)
>   (\a, b => mor cat a (mapObj (functor m) b))
>   (component (unit m))
>   (\a, b, c, f, g => compose cat _ _ _ (compose cat _ _ _ f (mapMor (functor m) _ _ g))
>                                        (component (multiplication m) c))
>   (\a, b, f => trans (cong {f = \x => compose cat
>                                               a
>                                               (mapObj (functor m) (mapObj (functor m) b))
>                                               (mapObj (functor m) b)
>                                               x
>                                               (component (multiplication m) b)}
>                            (commutativity (unit m) a (mapObj (functor m) b) f))
>                            (trans (sym $ associativity cat a
>                                                        (mapObj (functor m) b)
>                                                        (mapObj (functor m) (mapObj (functor m) b))
>                                                        (mapObj (functor m) b)
>                                                        f
>                                                        (component (unit m) (mapObj (functor m) b))
>                                                        (component (multiplication m) b))
>                                   (trans (cong {f = compose cat a (mapObj (functor m) b) (mapObj (functor m) b) f}
>                                                (natTransComposeEquality {a = b} (functor m)
>                                                                         (replace {P = \x => NaturalTransformation cat cat x (functorComposition cat cat cat (functor m) (functor m))}
>                                                                                  (catsRightIdentity cat cat (functor m))
>                                                                                  (composeNatTransFunctor cat cat cat (functor m) (idFunctor cat) (functor m) (unit m)))
>                                                                         (multiplication m)))
>                                          (trans (cong {f = \x => compose cat a (mapObj (functor m) b) (mapObj (functor m) b) f (component x b)}
>                                                       (leftUnit m))
>                                                 (rightIdentity cat a (mapObj (functor m) b) f)))))

>   ?rId
>   ?assoc

-- >   MkCategory
-- >     (obj cat)
-- >     (\a, b => mor cat a (mapObj (functor m) b))
-- >     (\a => component (unit m) a)
-- >     (\a, b, c, f, g =>
-- >       compose cat _ _ _
-- >         (compose cat _ _ _ f (mapMor (functor m) _ _ g))
-- >         (component (multiplication m) c))
-- >     (\a, b, f => ?asdf)
-- >     (\a, b, f => trans (sym $ associativity cat a
-- >                                                 (mapObj (functor m) b)
-- >                                                 (mapObj (functor m) (mapObj (functor m) b))
-- >                                                 (mapObj (functor m) b)
-- >                                                 f
-- >                                                 (mapMor (functor m) b (mapObj (functor m) b) (component (unit m) b))
-- >                                                 (component (multiplication m) b))
-- >                        -- ?qwer)
-- >                        (trans (cong {f = compose cat a (mapObj (functor m) b) (mapObj (functor m) b) f}
-- >                                     (cong {f = \nt => component nt b} (leftUnit m)))
-- >                               (rightIdentity cat a (mapObj (functor m) b) f)))
-- >     ?assoc
