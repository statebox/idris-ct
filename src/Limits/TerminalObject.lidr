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
> %auto_implicits off
>
> record TerminalObject (cat : Category) where
>   constructor MkTerminalObject
>   carrier : obj cat
>   exists  : (a : obj cat) -> mor cat a carrier
>   unique  : (a : obj cat) -> (f, g : mor cat a carrier) -> f = g
>
> composeTerminalMorphisms :
>      (cat : Category)
>   -> (a, b : TerminalObject cat)
>   -> mor cat (carrier a) (carrier a)
> composeTerminalMorphisms cat a b =
>   compose cat (carrier a) (carrier b) (carrier a) (exists b (carrier a)) (exists a (carrier b))
>
> terminalObjectsAreIsomorphic :
>      (cat : Category)
>   -> (a, b : TerminalObject cat)
>   -> Isomorphism cat (carrier a) (carrier b) (exists b (carrier a))
> terminalObjectsAreIsomorphic cat a b = MkIsomorphism
>   (exists a (carrier b))
>   (unique a (carrier a) (composeTerminalMorphisms cat a b) (identity cat (carrier a)))
>   (unique b (carrier b) (composeTerminalMorphisms cat b a) (identity cat (carrier b)))
