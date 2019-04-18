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

> module WiringDiagram.DiscreteDynamicalSystem
>
> import Basic.Category
> import Basic.Functor
> import Cats.CatsAsCategory
> import WiringDiagram.WiringDiagram
>
> %access public export
> %default total
>
> -- An (X_1, X_2)-discrete dynamical system is (S, f^update, f^redOut) where
> -- S = set of states
> -- f^update : X_1 \times S -> S
> -- f^readOut : S -> X_2
>
> data DDS : Type -> Type -> Type where
>   MkDDS : (s : Type) -> (fupd : (x1, s) -> s) -> (frdt : s -> x2) -> DDS x1 x2
>
> data DDSMorphism : DDS x1 x2 -> DDS x1 x2 -> Type
>
> ddsIdentity : (dds : DDS x1 x2) -> DDSMorphism dds dds
>
> ddsComposition : (dds1, dds2, dds3 : DDS x1 x2) -> (DDSMorphism dds1 dds2) -> (DDSMorphism dds2 dds3) -> (DDSMorphism dds1 dds3)
>
> ddsAsCategory : (x1, x2 : Type) -> Category
> ddsAsCategory x1 x2 = MkCategory
>   (DDS x1 x2)
>   (DDSMorphism {x1} {x2})
>   ddsIdentity
>   ddsComposition
>   ?lid
>   ?rid
>   ?assoc
>
> -- Denote by DDS(X1, X2) the set (category) of (X1, X2)-discrete dynamical systems
> -- Define a W_Set algebra as follows:
> -- DDS : W_Set -> Cat
> --       X = (X_1, X_2) -> DDS(X_1, X_2)
> --       \phi : X -> Y  -> DDS_\phi : DDS(X_1, X_2) -> DDS(Y1, Y_2)
> -- Given a (X_1, X_2)-DDS (S, f^update : (X_1, S) -> S, f^readout : S -> X_2)
> -- and a wiring diagram \phi : (\phi_1 : (Y_1, X_2) -> X_1, \phi_2 : X_2 -> Y_2)
> -- we can define a (Y_1, Y_2)-DDS
> --   S -- same set of states
> --   f^update  : (Y_1, S) -> (Y_1, S, S) -> (Y_1, X_2, S) -> (X_1, S) -> S
> --   f^readout : S -> X_2 -> Y_2
>
> ddsAlgebraMapObj : (wiringDiagram : (Type, Type)) -> Category
> ddsAlgebraMapObj wiringDiagram = ddsAsCategory (fst wiringDiagram) (snd wiringDiagram)
>
> ddsAlgebraMapMorMapObj :
>      (wd1, wd2 : (Type, Type))
>   -> WiringDiagramMorphism wd1 wd2
>   -> (DDS (fst wd1) (snd wd1))
>   -> (DDS (fst wd2) (snd wd2))
> ddsAlgebraMapMorMapObj wd1 wd2 (MkWiringDiagramMorphism f1 f2) (MkDDS s fupd frdt) = MkDDS
>   s
>   (fupd . (pairMorphism f1 id) . tupleAssociativity . (pairMorphism id (pairMorphism frdt id)) . (pairMorphism id delta))
>   (f2 . frdt)
>
> ddsAlgebraMapMorMapMor :
>      (wd1, wd2 : (Type, Type))
>   -> (wdMorphism : WiringDiagramMorphism wd1 wd2)
>   -> (a, b : DDS (fst wd1) (snd wd1))
>   -> (DDSMorphism a b)
>   -> (DDSMorphism (ddsAlgebraMapMorMapObj wd1 wd2 wdMorphism a) (ddsAlgebraMapMorMapObj wd1 wd2 wdMorphism b))
>
> ddsAlgebraMapMor : (wd1, wd2 : (Type, Type)) -> WiringDiagramMorphism wd1 wd2 -> CFunctor (ddsAlgebraMapObj wd1) (ddsAlgebraMapObj wd2)
> ddsAlgebraMapMor wd1 wd2 wdMorphism = MkCFunctor
>   (ddsAlgebraMapMorMapObj wd1 wd2 wdMorphism)
>   (ddsAlgebraMapMorMapMor wd1 wd2 wdMorphism)
>   ?morPresId
>   ?morPresComp
>
> ddsAlgebra : CFunctor WiringDiagram.wiringDiagramCategory CatsAsCategory.catsAsCategory
> ddsAlgebra = MkCFunctor
>   ddsAlgebraMapObj
>   ddsAlgebraMapMor
>   ?presId
>   ?presComp
>
> -- examples of DDS
>
> data S1 = A | B
>
> fupd1 : (Bool, S1) -> S1
> fupd1 (False, A) = B
> fupd1 (False, B) = B
> fupd1 (True,  A) = A
> fupd1 (True,  B) = B
>
> frdt1 : S1 -> Bool
> frdt1 A = False
> frdt1 B = True
>
> -- this is the NOT machine
> notDDS : DDS Bool Bool
> notDDS = MkDDS
>   S1
>   fupd1
>   frdt1
>
> data S2 = R | S | T
>
> fupd2 : (Bool, S2) -> S2
> fupd2 (False, R) = R
> fupd2 (False, S) = R
> fupd2 (False, T) = R
> fupd2 (True,  R) = S
> fupd2 (True,  S) = T
> fupd2 (True,  T) = T
>
> frdt2 : S2 -> Bool
> frdt2 R = False
> frdt2 S = False
> frdt2 T = True
>
> -- this is the TrueTrue-detector machine
> trueTrueDDS : DDS Bool Bool
> trueTrueDDS = MkDDS
>   S2
>   fupd2
>   frdt2
>
> -- wiring diagram composition
>
> -- parallel composition
>
> ddsTensor : DDS a b -> DDS c d -> DDS (a, c) (b, d)
> ddsTensor (MkDDS s1 fupd1 frdt1) (MkDDS s2 fupd2 frdt2) = MkDDS
>   (s1, s2)
>   (\((a1, c1), x, y) => (fupd1 (a1, x), fupd2 (c1, y)))
>   (\(x, y) => (frdt1 x, frdt2 y))
>
> -- serial composition
>
> zeroZeroDetector : DDS Bool Bool
> zeroZeroDetector = ddsAlgebraMapMorMapObj
>   ((Bool, Bool), (Bool, Bool))
>   (Bool, Bool)
>   (serial Bool Bool Bool)
>   (ddsTensor notDDS trueTrueDDS)
