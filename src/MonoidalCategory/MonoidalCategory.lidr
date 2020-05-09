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
> import Data.Vect
> import public MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
> 
> %access public export
> %default total
> 
> record MonoidalCategory where
>   constructor MkMonoidalCategory
>   cat : Category
>   tensor : CFunctor (productCategory [cat, cat]) cat
>   unit : obj cat
>   associator : Associator cat tensor
>   leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) (idFunctor cat)
>   rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat)
>   monoidalPentagon : (a, b, c, d : obj cat) -> MonoidalPentagon cat tensor associator a b c d
>   monoidalTriangle : (a, b : obj cat) -> MonoidalTriangle cat tensor unit associator leftUnitor rightUnitor a b
