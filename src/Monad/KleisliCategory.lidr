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
> kleisliCategory : {cat : Category} -> Monad cat -> Category
> kleisliCategory {cat} m = MkCategory
>   (obj cat)
>   (\a, b => mor cat a (mapObj (functor m) b))
>   (component (unit m))
>   (\a, b, c, f, g => compose cat _ _ _ (compose cat _ _ _ f (mapMor (functor m) _ _ g))
>                                        (component (multiplication m) c))
>   (\a, b, f => trans (cong {f = \x => compose cat _ _ _ x (component (multiplication m) b)}
>                            (commutativity (unit m) a (mapObj (functor m) b) f))
>                            (trans (sym $ associativity cat _ _ _ _
>                                                        f
>                                                        (component (unit m) (mapObj (functor m) b))
>                                                        (component (multiplication m) b))
>                                   (trans (cong {f = \x => compose cat _ _ _ f (component x b)}
>                                                       (leftUnit m))
>                                          (rightIdentity cat a (mapObj (functor m) b) f))))
>   (\a, b, f => trans (sym $ associativity cat _ _ _ _
>                                               f
>                                               (mapMor (functor m) _ _ (component (unit m) b))
>                                               (component (multiplication m) b))
>                      (trans (cong {f = \x => compose cat _ _ _ f (component x b)}
>                                   (rightUnit m))
>                             (rightIdentity cat _ _ f)))
>   (\a, b, c, d, f, g, h =>
>     trans (cong {f = \x => compose cat a
>                                        (mapObj (functor m) (mapObj (functor m) d))
>                                        (mapObj (functor m) d)
>                                        (compose cat a
>                                                     (mapObj (functor m) b)
>                                                     (mapObj (functor m) (mapObj (functor m) d))
>                                                     f
>                                                     x)
>                                        (component (multiplication m) d)}
>                 (preserveCompose (functor m) b
>                                              (mapObj (functor m) (mapObj (functor m) d))
>                                              (mapObj (functor m) d)
>                                              (compose cat b
>                                                           (mapObj (functor m) c)
>                                                           (mapObj (functor m) (mapObj (functor m) d))
>                                                           g
>                                                           (mapMor (functor m) c (mapObj (functor m) d) h))
>                                                           (component (multiplication m) d)))
>     (trans (cong {f = \x => compose cat a
>                                         (mapObj (functor m) (mapObj (functor m) d))
>                                         (mapObj (functor m) d)
>                                         x
>                                         (component (multiplication m) d)}
>                  (associativity cat a
>                                     (mapObj (functor m) b)
>                                     (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                     (mapObj (functor m) (mapObj (functor m) d))
>                                     f
>                                     (mapMor (functor m) b
>                                                         (mapObj (functor m) (mapObj (functor m) d))
>                                                         (compose cat b
>                                                                      (mapObj (functor m) c)
>                                                                      (mapObj (functor m) (mapObj (functor m) d))
>                                                                      g
>                                                                      (mapMor (functor m) c
>                                                                                          (mapObj (functor m) d)
>                                                                                          h)))
>                                     (mapMor (functor m) (mapObj (functor m) (mapObj (functor m) d))
>                                                         (mapObj (functor m) d)
>                                                         (component (multiplication m) d))))
>     (trans (sym $ associativity cat a
>                                     (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                     (mapObj (functor m) (mapObj (functor m) d))
>                                     (mapObj (functor m) d)
>                                     (compose cat a
>                                                  (mapObj (functor m) b)
>                                                  (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                                  f
>                                                  (mapMor (functor m) b
>                                                                      (mapObj (functor m) (mapObj (functor m) d))
>                                                                      (compose cat b
>                                                                                   (mapObj (functor m) c)
>                                                                                   (mapObj (functor m) (mapObj (functor m) d))
>                                                                                   g
>                                                                                   (mapMor (functor m) c
>                                                                                                       (mapObj (functor m) d)
>                                                                                                       h))))
>                                     (mapMor (functor m) (mapObj (functor m) (mapObj (functor m) d))
>                                                         (mapObj (functor m) d)
>                                                         (component (multiplication m) d))
>                                     (component (multiplication m) d))
>     (trans (cong {f = compose cat a
>                                   (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                   (mapObj (functor m) d)
>                                   (compose cat a
>                                                (mapObj (functor m) b)
>                                                (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                                f
>                                                (mapMor (functor m) b
>                                                                    (mapObj (functor m) (mapObj (functor m) d))
>                                                                    (compose cat b
>                                                                                 (mapObj (functor m) c)
>                                                                                 (mapObj (functor m) (mapObj (functor m) d))
>                                                                                 g
>                                                                                 (mapMor (functor m) c
>                                                                                                     (mapObj (functor m) d)
>                                                                                                     h))))}
>                  (cong {f = \x => component x d} (associativity m)))
>     (trans (cong $ leftIdentity cat (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                     (mapObj (functor m) d)
>                                     (compose cat (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                                  (mapObj (functor m) (mapObj (functor m) d))
>                                                  (mapObj (functor m) d)
>                                                  (component (multiplication m) (mapObj (functor m) d))
>                                                  (component (multiplication m) d)))
>     (trans (cong {f = \x => compose cat a
>                                         (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                         (mapObj (functor m) d)
>                                         (compose cat a
>                                                      (mapObj (functor m) b)
>                                                      (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                                      f
>                                                      x)
>                                         (compose cat (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                                      (mapObj (functor m) (mapObj (functor m) d))
>                                                      (mapObj (functor m) d)
>                                                      (component (multiplication m) (mapObj (functor m) d))
>                                                      (component (multiplication m) d))}
>                  (preserveCompose (functor m) b
>                                               (mapObj (functor m) c)
>                                               (mapObj (functor m) (mapObj (functor m) d))
>                                               g
>                                               (mapMor (functor m) c (mapObj (functor m) d) h)))
>     (trans (cong {f = \x => compose cat a
>                                         (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                         (mapObj (functor m) d)
>                                         x
>                                         (compose cat (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                                      (mapObj (functor m) (mapObj (functor m) d))
>                                                      (mapObj (functor m) d)
>                                                      (component (multiplication m) (mapObj (functor m) d))
>                                                      (component (multiplication m) d))}
>                  (associativity cat a
>                                     (mapObj (functor m) b)
>                                     (mapObj (functor m) (mapObj (functor m) c))
>                                     (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                     f
>                                     (mapMor (functor m) b (mapObj (functor m) c) g)
>                                     (mapMor (functor m) (mapObj (functor m) c)
>                                                         (mapObj (functor m) (mapObj (functor m) d))
>                                                         (mapMor (functor m) c (mapObj (functor m) d) h))))
>     (trans (sym $ associativity cat a
>                                     (mapObj (functor m) (mapObj (functor m) c))
>                                     (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                     (mapObj (functor m) d)
>                                     (compose cat a
>                                                  (mapObj (functor m) b)
>                                                  (mapObj (functor m) (mapObj (functor m) c))
>                                                  f
>                                                  (mapMor (functor m) b (mapObj (functor m) c) g))
>                                     (mapMor (functor m) (mapObj (functor m) c)
>                                                         (mapObj (functor m) (mapObj (functor m) d))
>                                                         (mapMor (functor m) c (mapObj (functor m) d) h))
>                                     (compose cat (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                                  (mapObj (functor m) (mapObj (functor m) d))
>                                                  (mapObj (functor m) d)
>                                                  (component (multiplication m) (mapObj (functor m) d))
>                                                  (component (multiplication m) d)))
>     (trans (cong {f = compose cat a
>                                   (mapObj (functor m) (mapObj (functor m) c))
>                                   (mapObj (functor m) d)
>                                   (compose cat a
>                                                (mapObj (functor m) b)
>                                                (mapObj (functor m) (mapObj (functor m) c))
>                                                f
>                                                (mapMor (functor m) b (mapObj (functor m) c) g))}
>                  (associativity cat (mapObj (functor m) (mapObj (functor m) c))
>                                     (mapObj (functor m) (mapObj (functor m) (mapObj (functor m) d)))
>                                     (mapObj (functor m) (mapObj (functor m) d))
>                                     (mapObj (functor m) d)
>                                     (mapMor (functor m) (mapObj (functor m) c)
>                                                         (mapObj (functor m) (mapObj (functor m) d))
>                                                         (mapMor (functor m) c (mapObj (functor m) d) h))
>                                     (component (multiplication m) (mapObj (functor m) d))
>                                     (component (multiplication m) d)))
>     (trans (cong {f = \x => compose cat a
>                                         (mapObj (functor m) (mapObj (functor m) c))
>                                         (mapObj (functor m) d)
>                                         (compose cat a
>                                                      (mapObj (functor m) b)
>                                                      (mapObj (functor m) (mapObj (functor m) c))
>                                                      f
>                                                      (mapMor (functor m) b (mapObj (functor m) c) g))
>                                         (compose cat (mapObj (functor m) (mapObj (functor m) c))
>                                                      (mapObj (functor m) (mapObj (functor m) d))
>                                                      (mapObj (functor m) d)
>                                                      x
>                                                      (component (multiplication m) d))}
>                  (sym $ commutativity (multiplication m) c (mapObj (functor m) d) h))
>     (trans (associativity cat a
>                               (mapObj (functor m) (mapObj (functor m) c))
>                               (mapObj (functor m) (mapObj (functor m) d))
>                               (mapObj (functor m) d)
>                               (compose cat a
>                                            (mapObj (functor m) b)
>                                            (mapObj (functor m) (mapObj (functor m) c))
>                                            f
>                                            (mapMor (functor m) b (mapObj (functor m) c) g))
>                               (compose cat (mapObj (functor m) (mapObj (functor m) c))
>                                            (mapObj (functor m) c)
>                                            (mapObj (functor m) (mapObj (functor m) d))
>                                            (component (multiplication m) c)
>                                            (mapMor (functor m) c (mapObj (functor m) d) h))
>                               (component (multiplication m) d))
>     (cong {f = \x => compose cat a
>                                  (mapObj (functor m) (mapObj (functor m) d))
>                                  (mapObj (functor m) d)
>                                  x
>                                  (component (multiplication m) d)}
>           (associativity cat a
>                              (mapObj (functor m) (mapObj (functor m) c))
>                              (mapObj (functor m) c)
>                              (mapObj (functor m) (mapObj (functor m) d))
>                              (compose cat a
>                                           (mapObj (functor m) b)
>                                           (mapObj (functor m) (mapObj (functor m) c))
>                                           f
>                                           (mapMor (functor m) b (mapObj (functor m) c) g))
>                              (component (multiplication m) c)
>                              (mapMor (functor m) c (mapObj (functor m) d) h))))))))))))))
