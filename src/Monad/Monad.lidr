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
> import CategoryReasoning as CR
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Syntax.PreorderReasoning
>
> %access public export
> %default total
>
> qed : (a : obj (functorCategory cat cat)) -> mor _ a a
> qed = CR.qed (functorCategory cat cat)
>
> step :
>      (a : obj (functorCategory cat cat))
>   -> mor (functorCategory cat cat) a b
>   -> mor (functorCategory cat cat) b c
>   -> mor (functorCategory cat cat) a c
> step = CR.step (functorCategory cat cat)
>
> liftEquality : (a, b : obj (functorCategory cat cat)) -> a = b -> mor (functorCategory cat cat) a b
> liftEquality = CR.liftEquality (functorCategory cat cat)
>
> record Monad (cat : Category) where
>   constructor MkMonad
>   functor : CFunctor cat cat
>   unit : NaturalTransformation _ _ (idFunctor cat) functor
>   multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor
>   associativity :
>     ((functorComposition _ _ _ functor (functorComposition _ _ _ functor functor))
>     ={ composeNatTransFunctor _ _ _ functor (functorComposition _ _ _ functor functor) functor multiplication }=
>     (functorComposition cat cat cat functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>     =
>     ((functorComposition cat cat cat functor (functorComposition cat cat cat functor functor))
>     ={ liftEquality
>          (functorComposition cat cat cat functor (functorComposition cat cat cat functor functor))
>          (functorComposition cat cat cat (functorComposition cat cat cat functor functor) functor)
>          (catsAssociativity _ _ _ _ functor functor functor) }=
>     (functorComposition cat cat cat (functorComposition cat cat cat functor functor) functor)
>     ={ composeFunctorNatTrans cat cat cat
>          (functorComposition cat cat cat functor functor) functor multiplication functor }=
>     (functorComposition cat cat cat functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>   leftUnit :
>     (functor
>     ={ liftEquality functor (functorComposition _ _ _ (idFunctor cat) functor)
>          (sym $ catsLeftIdentity cat cat functor) }=
>     (functorComposition _ _ _ (idFunctor cat) functor)
>     ={ composeFunctorNatTrans cat cat cat (idFunctor cat) functor unit functor }=
>      (functorComposition _ _ _ functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>     =
>     idTransformation cat cat functor
>   rightUnit :
>     (functor
>     ={ liftEquality functor (functorComposition _ _ _ functor (idFunctor cat))
>          (sym $ catsRightIdentity cat cat functor) }=
>     (functorComposition _ _ _ functor (idFunctor cat))
>     ={ composeNatTransFunctor cat cat cat functor (idFunctor cat) functor unit }=
>      (functorComposition _ _ _ functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>     =
>     idTransformation cat cat functor
