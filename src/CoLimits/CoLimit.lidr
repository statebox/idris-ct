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
> import Data.Graph
> import Data.Diagram
> import Data.Fin
> import CoLimits.InitialObject
> import CoLimits.CoConeCat
> import CoLimits.CoCone
>
> %access public export
> %default total
>
> record CoLimit
>   (cat : Category)
>   (n : Nat) (m : Nat)
>   (dia : Diagram cat n m)
> where
>   constructor MkCoLimit
>   carrier: CoCone cat n m dia
>   exists: (b : CoCone cat n m dia) -> CoConeMorphism cat n m dia carrier b
>   unique: (b : CoCone cat n m dia) -> (f : CoConeMorphism cat n m dia carrier b) -> f = exists b
>
> coLimitIsInitial :
>      (cat : Category)
>   -> (n, m : Nat)
>   -> (dia: Diagram cat n m)
>   -> (cl: CoLimit cat n m dia)
>   -> InitialObject (CoConeCategory cat n m dia)
> coLimitIsInitial cat n m dia cl = MkInitialObject
>   (carrier cl)
>   (exists cl)
>   (\b, f, g => trans (unique cl b f) (sym (unique cl b g)))
