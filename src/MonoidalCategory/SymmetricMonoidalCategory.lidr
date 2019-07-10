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

> module MonoidalCategory.SymmetricMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import MonoidalCategory.MonoidalCategory
> import MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
> import MonoidalCategory.SymmetricMonoidalCategoryHelpers
>
> %access public export
> %default total
>
> data SymmetricMonoidalCategory : Type where
>   MkSymmetricMonoidalCategory :
>        (monoidalCategory : MonoidalCategory)
>     -> (symmetry : NaturalIsomorphism (productCategory (cat monoidalCategory) (cat monoidalCategory))
>                                       (cat monoidalCategory)
>                                       (tensor monoidalCategory)
>                                       (functorComposition (productCategory (cat monoidalCategory)
>                                                                            (cat monoidalCategory))
>                                                           (productCategory (cat monoidalCategory)
>                                                                            (cat monoidalCategory))
>                                                           (cat monoidalCategory)
>                                                           (swapFunctor (cat monoidalCategory)
>                                                                        (cat monoidalCategory))
>                                                           (tensor monoidalCategory)))
>     -> ((a : obj (cat monoidalCategory)) -> UnitCoherence (cat monoidalCategory)
>                                                         (tensor monoidalCategory)
>                                                         (unit monoidalCategory)
>                                                         (leftUnitor monoidalCategory)
>                                                         (rightUnitor monoidalCategory)
>                                                         symmetry
>                                                         a)
>     -> ((a, b, c : obj (cat monoidalCategory)) -> AssociativityCoherence (cat monoidalCategory)
>                                                                          (tensor monoidalCategory)
>                                                                          ?associator -- should be (associator monoidalCategory)
>                                                                          symmetry
>                                                                          a b c)
>     -> ((a, b : obj (cat monoidalCategory)) -> InverseLaw (cat monoidalCategory)
>                                                           (tensor monoidalCategory)
>                                                           symmetry
>                                                           a b)
>     -> SymmetricMonoidalCategory
