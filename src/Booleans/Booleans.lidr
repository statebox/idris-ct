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

> module Booleans.Booleans
>
> import Basic.Category
> import Decidable.Order
> import Preorder.PreorderAsCategory
> import Preorder.UniquePreorder
>
> %access public export
> %default total
>
> data BoolArr : Bool -> Bool -> Type where
>   FId : BoolArr False False
>   F2T : BoolArr False True
>   TId : BoolArr True  True
>
> uniqueBoolArr : (a, b : Bool) -> (f, g : BoolArr a b) -> f = g
> uniqueBoolArr False False FId FId = Refl
> uniqueBoolArr False True  F2T F2T = Refl
> uniqueBoolArr True  True  TId TId = Refl
>
> boolId : (b : Bool) -> BoolArr b b
> boolId False = FId
> boolId True = TId
>
> boolCompose : (a, b, c : Bool) -> BoolArr a b -> BoolArr b c -> BoolArr a c
> boolCompose _ _ _ FId f = f
> boolCompose _ _ _ f TId = f
>
> Preorder Bool BoolArr where
>   transitive = boolCompose
>   reflexive = boolId
>
> UniquePreorder Bool BoolArr where
>   unique = uniqueBoolArr

The (pre)order of booleans, often referred to as just "2".

> Booleans : Category
> Booleans = preorderAsCategory {t=Bool} {po=BoolArr}
