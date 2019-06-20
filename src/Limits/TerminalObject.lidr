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

> module Limits.TerminalObject
>
> import Basic.Category
> import Basic.Isomorphism
>
> %access public export
> %default total
>
> record TerminalObject (cat : Category) where
>   constructor MkTerminalObject
>   Carrier : obj cat
>   exists  : (a : obj cat) -> mor cat a Carrier
>   unique  : (a : obj cat) -> (f, g : mor cat a Carrier) -> f = g
>
> composeTerminalMorphisms :
>      (cat : Category)
>   -> (a, b : TerminalObject cat)
>   -> mor cat (Carrier a) (Carrier a)
> composeTerminalMorphisms cat a b =
>   compose cat (Carrier a) (Carrier b) (Carrier a) (exists b (Carrier a)) (exists a (Carrier b))
>
> terminalObjectsAreIsomorphic :
>      (cat : Category)
>   -> (a, b : TerminalObject cat)
>   -> Isomorphism cat (Carrier a) (Carrier b) (exists b (Carrier a))
> terminalObjectsAreIsomorphic cat a b = MkIsomorphism
>   (exists a (Carrier b))
>   (unique a (Carrier a) (composeTerminalMorphisms cat a b) (identity cat (Carrier a)))
>   (unique b (Carrier b) (composeTerminalMorphisms cat b a) (identity cat (Carrier b)))
