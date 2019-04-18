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

> module WiringDiagram.WiringDiagram
>
> -- inspired by the talk Systems as Wiring Diagram Algebras by Christina Vasilakopoulou
> -- https://www.youtube.com/watch?v=dEDtaJhgQOY
>
> import Basic.Category
> import Basic.Functor
> import Idris.TypesAsCategory
> import Utils
>
> %access public export
> %default total
>
> -- W_C symmetric monoidal category of C-labeled boxes and wiring diagrams
>
> -- fix C finitely complete category (finite products are enough). We are going to use Types and functions as our category C
>
> -- objects are pairs X = (X_1, X_2) \in C \times C
>
> -- morphisms \phi : (X_1, X_2) -> (Y_1, Y_2) are pairs of morphisms in C
> -- \phi_1 : Y_1 \times X_2 -> X_1
> -- \phi_2 : X_2 -> Y_2
>
> record WiringDiagramMorphism (a : (Type, Type)) (b :(Type, Type)) where
>   constructor MkWiringDiagramMorphism
>   f1 : (fst b, snd a) -> fst a
>   f2 : (snd a -> snd b)
>
> -- composition between two morphisms \phi = (\phi_1, \phi_2) : (X_1, X_2) -> (Y_1, Y_2) and \psi = (\psi_1, \psi_2) : (Y_1, Y_2) -> (Z_1, Z_2) is given by
> -- (\phi ; \psi)_1 = 1 \times \Delta ; 1 \times \phi_2 \times 1 ; \psi_2 \times id ; \phi_2
> -- (\phi ; \psi)_2 = \phi_2 ; \psi_2
>
> delta : a -> (a, a)
> delta x = (x, x)
>
> pairMorphism : (a -> b) -> (c -> d) -> ((a, c) -> (b, d))
> pairMorphism f g (x, y) = (f x, g y)
>
> tupleAssociativity : (a, b ,c) -> ((a, b), c)
> tupleAssociativity (x, y, z) = ((x, y), z)
>
> compose :
>      (a, b, c : (Type, Type))
>   -> (f : WiringDiagramMorphism a b)
>   -> (g : WiringDiagramMorphism b c)
>   -> WiringDiagramMorphism a c
> compose _ _ _ (MkWiringDiagramMorphism f1 f2) (MkWiringDiagramMorphism g1 g2)
>   = MkWiringDiagramMorphism
>     (f1 . (pairMorphism g1 id) . tupleAssociativity . (pairMorphism id (pairMorphism f2 id)) . (pairMorphism id delta))
>     (g2 . f2)
>
> -- the identity on (X_1, X_2) is (fst, id)
>
> identity : (a : (Type, Type)) -> WiringDiagramMorphism a a
> identity a = MkWiringDiagramMorphism fst id
>
> -- this componition and identity form a category
>
> wiringDiagramCategory : Category
> wiringDiagramCategory = MkCategory
>   (Type, Type)
>   WiringDiagramMorphism
>   identity
>   compose
>   ?leftIdentity
>   ?rightIdentity
>   ?associativity
>
> -- the tensor product between object is given by parallel placement of boxes
>
> tensor : (a, b : (Type, Type)) -> (Type, Type)
> tensor (a1, a2) (b1, b2) = ((a1, b1), (a2, b2))
>
> -- tensor unit is given by (Unit, Unit)
>
> unit : (Type, Type)
> unit = ((), ())
>
> -- serial composition
> -- suppose X = (A, B) and Y = (B, C), we want to obtain a wiring diagram going to Z = (A, C) which represents the serial composition of X and Y
> -- we do that by placing the two boxes in parallel and using the output of the first as feedback of the second
> -- \phi : X \tensor Y -> Z
> -- with
> -- \phi_1 = \pi_12
> -- \phi_2 = \pi_2
>
> serial : (a, b, c : Type) -> WiringDiagramMorphism ((a, b), (b, c)) (a, c)
> serial a b c = MkWiringDiagramMorphism (map fst) snd
>
> -- there is a functor W_(-) : FC -> SMC from finitely complete categories to symmetric monoidal categories.
> -- maps any finitely complete category C to W_C
> -- maps finitely product preserving functor K : C -> D to a strong symmetric monoidal functor W_K : W_C -> W_D
> -- W_K (X_1, X_2) = (K X_1, K X_2)
> -- W_K (\phi_1, \phi_2) = (k Y_1 \times K Y_2 ~> K (Y_1 \times Y_2) -> K X_1, K \phi_2 : K X_2 -> K Y_2)
> -- this is changing the types of the wires
