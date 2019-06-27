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

> module CoLimits.CoLimitAsInitialObject
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
>
> import CoLimits.InitialObject
> import CoLimits.CoConeCat
> import CoLimits.CoCone
> import CommutativeDiagram.Diagram
> import CoLimits.CoLimit
>
> %access public export
> %default total
>
> coLimitToInitial :
>      (colimit: CoLimit index cat dia)
>   -> InitialObject (CoConeCategory index cat dia)
> coLimitToInitial colimit = MkInitialObject
>   (MkCoConeObject (carrier colimit) (cocone colimit))
>   (\b => exists colimit (apex b) (cocone b))
>   (\b, f, g => unique colimit (apex b) (cocone b) f g)
