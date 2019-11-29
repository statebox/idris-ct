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

> module Booleans.BooleanLimits
>
> import Basic.Category
> import Booleans.Booleans
> import Limits.TerminalObject
> import Limits.Product
> import Preorder.PreorderAsCategory
>
> %access public export
> %default total
>
> boolTerminator : (b : Bool) -> BoolArr b True
> boolTerminator False = F2T
> boolTerminator True  = TId
>
> trueIsTerminal : TerminalObject Booleans
> trueIsTerminal = MkInitialObject True boolTerminator (\b => uniqueBoolArr b True)
>
> boolPil : (a, b : Bool) -> BoolArr (a && b) a
> boolPil True  True  = TId
> boolPil True  False = F2T
> boolPil False _     = FId
>
> boolPir : (a, b : Bool) -> BoolArr (a && b) b
> boolPir True  True  = TId
> boolPir False True  = F2T
> boolPir True  False = FId
> boolPir False False = FId
>
> boolProductExists : (a, b, c : Bool)
>                  -> (f : BoolArr c a)
>                  -> (g : BoolArr c b)
>                  -> CommutingMorphism (dualCategory Booleans) a b (a && b) c (boolPil a b) (boolPir a b) f g
> boolProductExists True  True  c f g = MkCommutingMorphism f (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
> boolProductExists True  False c f g = MkCommutingMorphism g (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
> boolProductExists False b     c f g = MkCommutingMorphism f (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
>
> andIsProduct : (a, b : Bool) -> Product Booleans a b
> andIsProduct a b = MkCoProduct
>   (a && b)
>   (boolPil a b)
>   (boolPir a b)
>   (boolProductExists a b)
>   (\_, _, _, _ => uniqueBoolArr _ _ _ _)
