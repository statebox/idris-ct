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

> module Booleans.BooleanCoLimits
>
> import Basic.Category
> import Booleans.Booleans
> import CoLimits.InitialObject
> import CoLimits.CoProduct
> import Preorder.PreorderAsCategory
>
> %access public export
> %default total
>
> boolInitializer : (b : Bool) -> BoolArr False b
> boolInitializer False = FId
> boolInitializer True  = F2T
>
> falseIsInitial : InitialObject Booleans
> falseIsInitial = MkInitialObject False boolInitializer (uniqueBoolArr False)
>
> boolInl : (a, b : Bool) -> BoolArr a (a || b)
> boolInl False False = FId
> boolInl False True  = F2T
> boolInl True  _     = TId
>
> boolInr : (a, b : Bool) -> BoolArr b (a || b)
> boolInr False False = FId
> boolInr True  False = F2T
> boolInr False True  = TId
> boolInr True  True  = TId
>
> boolCoProductExists : (a, b, c : Bool)
>                    -> (f : BoolArr a c)
>                    -> (g : BoolArr b c)
>                    -> CommutingMorphism Booleans a b (a || b) c (boolInl a b) (boolInr a b) f g
> boolCoProductExists False False c f g = MkCommutingMorphism f (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
> boolCoProductExists False True  c f g = MkCommutingMorphism g (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
> boolCoProductExists True  b     c f g = MkCommutingMorphism f (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
>
> orIsCoProduct : (a, b : Bool) -> CoProduct Booleans a b
> orIsCoProduct a b = MkCoProduct
>   (a || b)
>   (boolInl a b)
>   (boolInr a b)
>   (boolCoProductExists a b)
>   (\_, _, _, _ => uniqueBoolArr _ _ _ _)
