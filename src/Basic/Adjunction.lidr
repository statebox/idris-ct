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

> module Basic.Adjunction
>
> import Basic.Category
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Idris.TypesAsCategory as Idris
> import Utils
>
> %access public export
> %default total
>
> infixr 1 >>>
> (>>>) : {cat1, cat2, cat3 : Category} -> CFunctor cat1 cat2 -> CFunctor cat2 cat3 -> CFunctor cat1 cat3
> (>>>) {cat1} {cat2} {cat3} = functorComposition cat1 cat2 cat3
>
> record Adjunction
>   (cat1 : Category)
>   (cat2 : Category)
>   (funL : CFunctor cat2 cat1)
>   (funR : CFunctor cat1 cat2)
> where
>   constructor MkAdjunction
>   counit : NaturalTransformation cat1 cat1 (funR >>> funL) (idFunctor cat1)
>   unit   : NaturalTransformation cat2 cat2 (idFunctor cat2) (funL >>> funR)
>   leftCounitUnitEq :
>     idTransformation cat2 cat1 funL =
>     naturalTransformationComposition cat2 cat1 funL ((funL >>> funR) >>> funL) funL
>       (replace2 (catsLeftIdentity _ _ funL) (Refl { x = (funL >>> funR) >>> funL })
>          (composeFunctorNatTrans cat2 cat2 cat1 (idFunctor cat2) (funL >>> funR) unit funL))
>       (replace2 (catsAssociativity _ _ _ _ funL funR funL) (catsRightIdentity _ _ funL)
>         (composeNatTransFunctor cat2 cat1 cat1 funL (funR >>> funL) (idFunctor cat1) counit))
>   rightCounitUnitEq :
>     idTransformation cat1 cat2 funR =
>     naturalTransformationComposition cat1 cat2 funR ((funR >>> funL) >>> funR) funR
>       (replace2 (catsRightIdentity _ _ funR) (catsAssociativity _ _ _ _ funR funL funR)
>         (composeNatTransFunctor cat1 cat2 cat2 funR (idFunctor cat2) (funL >>> funR) unit))
>       (replace (catsLeftIdentity _ _ funR)
>          (composeFunctorNatTrans cat1 cat1 cat2 (funR >>> funL) (idFunctor cat1) counit funR))
