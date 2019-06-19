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

> module CoLimits.CoLimit
>
> import Basic.Category
>
> import CoLimits.InitialObject
> import CoLimits.CoConeCat
> import CoLimits.CoCone
> import CommutativeDiagram.Diagram
>
> %access public export
> %default total
>
> record CoLimit
>   (index : Category)
>   (cat : Category)
>   (dia : Diagram index cat)
> where
>   constructor MkCoLimit
>   carrier: CoCone index cat dia
>   exists: (b : CoCone index cat dia) -> CoConeMorphism index cat dia carrier b
>   unique: (b : CoCone index cat dia) -> (f : CoConeMorphism index cat dia carrier b) -> f = exists b
>
> coLimitIsInitial :
>      (index, cat : Category)
>   -> (dia: Diagram index cat)
>   -> (cl: CoLimit index cat dia)
>   -> InitialObject (CoConeCategory index cat dia)
> coLimitIsInitial index cat dia cl = MkInitialObject
>   (carrier cl)
>   (exists cl)
>   (\b, f, g => trans (unique cl b f) (sym (unique cl b g)))
