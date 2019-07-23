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

> module Monad.Monad
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
>
> %access public export
> %default total
>
> record Monad (cat : Category) where
>   constructor MkMonad
>   functor : CFunctor cat cat
>   unit : NaturalTransformation _ _ (idFunctor cat) functor
>   multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor
>   associativity : naturalTransformationComposition cat cat
>                                                    (functorComposition cat cat cat (functorComposition cat cat cat functor functor) functor)
>                                                    (functorComposition cat cat cat functor functor)
>                                                    functor
>                                                    (composeFunctorNatTrans cat cat cat
>                                                                            (functorComposition cat cat cat functor functor)
>                                                                            functor
>                                                                            multiplication
>                                                                            functor)
>                                                    multiplication
>                 = naturalTransformationComposition cat cat
>                                                    (functorComposition cat cat cat functor (functorComposition cat cat cat functor functor))
>                                                    (functorComposition cat cat cat functor functor)
>                                                    functor
>                                                    (composeNatTransFunctor cat cat cat
>                                                                            functor
>                                                                            (functorComposition cat cat cat functor functor)
>                                                                            functor
>                                                                            multiplication)
>                                                    multiplication
>   leftUnit : naturalTransformationComposition cat cat
>                                                functor
>                                                (functorComposition cat cat cat functor functor)
>                                                functor
>                                                (replace {P = \x => NaturalTransformation cat cat x (functorComposition cat cat cat functor functor)}
>                                                         (catsRightIdentity cat cat functor)
>                                                         (composeNatTransFunctor cat cat cat
>                                                                                 functor
>                                                                                 (idFunctor cat)
>                                                                                 functor
>                                                                                 unit))
>                                                multiplication
>             = idTransformation cat cat functor
>   rightUnit : naturalTransformationComposition cat cat
>                                               functor
>                                               (functorComposition cat cat cat functor functor)
>                                               functor
>                                               (replace {P = \x => NaturalTransformation cat cat x (functorComposition cat cat cat functor functor)}
>                                                        (catsLeftIdentity cat cat functor)
>                                                        (composeFunctorNatTrans cat cat cat
>                                                                                (idFunctor cat)
>                                                                                functor
>                                                                                unit
>                                                                                functor))
>                                               multiplication
>            = idTransformation cat cat functor
