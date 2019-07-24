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

> module MonoidalCategory.MonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
>
> %access public export
> %default total
>
> -- we are not using a record here because compilation does not terminate in that case
> data MonoidalCategory : Type where
>   MkMonoidalCategory :
>        (cat : Category)
>     -> (tensor : CFunctor (productCategory cat cat) cat)
>     -> (unit : obj cat)
>     -> (associator : Associator cat tensor)
>     -> (leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) (idFunctor cat))
>     -> (rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat))
>     -> ((a, b, c, d : obj cat) -> MonoidalPentagon cat tensor associator a b c d)
>     -> ((a, b : obj cat) -> MonoidalTriangle cat tensor unit associator leftUnitor rightUnitor a b)
>     -> MonoidalCategory
>
> cat : MonoidalCategory -> Category
> cat (MkMonoidalCategory innerCat _ _ _ _ _ _ _) = innerCat
>
> tensor : (mCat : MonoidalCategory) -> CFunctor (productCategory (cat mCat) (cat mCat)) (cat mCat)
> tensor (MkMonoidalCategory _ monoidalTensor _ _ _ _ _ _) = monoidalTensor
>
> unit : (mCat : MonoidalCategory) -> obj (cat mCat)
> unit (MkMonoidalCategory _ _ unit _ _ _ _ _) = unit
>
> associator : (mCat : MonoidalCategory) -> Associator (cat mCat) (tensor mCat)
> associator (MkMonoidalCategory _ _ _ associator _ _ _ _) = associator
>
> leftUnitor : (mCat : MonoidalCategory) -> NaturalIsomorphism (cat mCat)
>                                                              (cat mCat)
>                                                              (leftIdTensor (cat mCat) (tensor mCat) (unit mCat))
>                                                              (idFunctor (cat mCat))
> leftUnitor (MkMonoidalCategory _ _ _ _ leftUnitor _ _ _) = leftUnitor
>
> rightUnitor : (mCat : MonoidalCategory) -> NaturalIsomorphism (cat mCat)
>                                                              (cat mCat)
>                                                              (rightIdTensor (cat mCat) (tensor mCat) (unit mCat))
>                                                              (idFunctor (cat mCat))
> rightUnitor (MkMonoidalCategory _ _ _ _ _ rightUnitor _ _) = rightUnitor
>
