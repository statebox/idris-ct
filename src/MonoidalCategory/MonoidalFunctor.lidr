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

> module MonoidalCategory.MonoidalFunctor
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import MonoidalCategory.MonoidalCategory
> import Product.ProductCategory
>
> %access public export
> %default total
>
> mapThenTensor :
>      (mcat1, mcat2 : MonoidalCategory)
>   -> CFunctor (productCategory (cat mcat1) (cat mcat1)) (cat mcat2)
> mapThenTensor mcat1 mcat2 = ?asdf
>
> tensorThenMap :
>      (mcat1, mcat2 : MonoidalCategory)
>   -> CFunctor (productCategory (cat mcat1) (cat mcat1)) (cat mcat2)
> tensorThenMap mcat1 mcat2 = ?qwer
>
> record MonoidalFunctor (mcat1 : MonoidalCategory) (mcat2 : MonoidalCategory) where
>   constructor MkMonoidalFunctor
>   func         : CFunctor (cat mcat1) (cat mcat2)
>   coherenceNat : NaturalTransformation (productCategory (cat mcat1) (cat mcat1))
>                                        (cat mcat2)
>                                        (mapThenTensor mcat1 mcat2)
>                                        (tensorThenMap mcat1 mcat2)
>   coherenceMor : mor (cat mcat2) (unit mcat2) (mapObj func (unit mcat1))
