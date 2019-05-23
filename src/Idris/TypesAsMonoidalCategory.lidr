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

> module Idris.TypesAsMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Idris.TypesAsCategory
> import MonoidalCategory.MonoidalCategory
> import MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
>
> %access public export
> %default total
>
> typesTensor : CFunctor (productCategory TypesAsCategory.typesAsCategory TypesAsCategory.typesAsCategory)
>                        TypesAsCategory.typesAsCategory
>
> typesAssociator : Associator TypesAsCategory.typesAsCategory TypesAsMonoidalCategory.typesTensor
>
> typesLeftUnitor : NaturalIsomorphism TypesAsCategory.typesAsCategory
>                                      TypesAsCategory.typesAsCategory
>                                      (leftIdTensor TypesAsCategory.typesAsCategory
>                                                    TypesAsMonoidalCategory.typesTensor
>                                                    ())
>                                      (idFunctor TypesAsCategory.typesAsCategory)
>
> typesRightUnitor : NaturalIsomorphism TypesAsCategory.typesAsCategory
>                                       TypesAsCategory.typesAsCategory
>                                       (rightIdTensor TypesAsCategory.typesAsCategory
>                                                      TypesAsMonoidalCategory.typesTensor
>                                                      ())
>                                       (idFunctor TypesAsCategory.typesAsCategory)
>
> typesPentagon : (a, b, c, d : Type) -> MonoidalPentagon TypesAsCategory.typesAsCategory
>                                                         TypesAsMonoidalCategory.typesTensor
>                                                         TypesAsMonoidalCategory.typesAssociator
>                                                         a b c d
>
> typesTriangle : (a, b : Type) -> MonoidalTriangle TypesAsCategory.typesAsCategory
>                                                   TypesAsMonoidalCategory.typesTensor
>                                                   ()
>                                                   TypesAsMonoidalCategory.typesAssociator
>                                                   TypesAsMonoidalCategory.typesLeftUnitor
>                                                   TypesAsMonoidalCategory.typesRightUnitor
>                                                   a b
>
> typesAsMonoidalCategory : MonoidalCategory
> typesAsMonoidalCategory = MkMonoidalCategory
>   TypesAsCategory.typesAsCategory
>   typesTensor
>   ()
>   typesAssociator
>   typesLeftUnitor
>   typesRightUnitor
>   typesPentagon
>   typesTriangle
