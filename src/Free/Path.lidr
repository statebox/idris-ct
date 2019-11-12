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

> module Free.Path
>
> import Data.Vect
> import Free.Graph
>
> %access public export
> %default total
>
> data Path : (g : Graph) -> vertices g -> vertices g -> Type where
>   Nil  : Path g i i
>   (::) : edges g i j -> Path g j k -> Path g i k
>
> edgeToPath : {g : Graph} -> edges g i j -> Path g i j
> edgeToPath a = [a]
>
> joinPath : Path g i j -> Path g j k -> Path g i k
> joinPath [] y = y
> joinPath (x :: xs) y = x :: joinPath xs y
>
> joinPathNil : (p : Path g i j) -> joinPath p [] = p
> joinPathNil Nil       = Refl
> joinPathNil (x :: xs) = cong $ joinPathNil xs
>
> joinPathAssoc :
>      (p : Path g i j)
>   -> (q : Path g j k)
>   -> (r : Path g k l)
>   -> joinPath p (joinPath q r) = joinPath (joinPath p q) r
> joinPathAssoc Nil q r = Refl
> joinPathAssoc (x :: xs) q r = cong $ joinPathAssoc xs q r
>
> data EdgeListPath : (edges : Vect n (vertices, vertices)) -> vertices -> vertices -> Type where
>   Empty : EdgeListPath edges i i
>   Cons  : Elem (i, j) edges -> EdgeListPath edges j k -> EdgeListPath edges i k
>
> filterElemWhichIsHere : DecEq t => (x : t) -> (l : Vect _ t) -> (k : Nat ** fst $ decEqFilter x (x :: l) = S k)
> filterElemWhichIsHere x [] with (decEq x x)
>   filterElemWhichIsHere x [] | Yes Refl  = (0 ** Refl)
>   filterElemWhichIsHere x [] | No contra = void $ contra Refl
> filterElemWhichIsHere x xs with (decEq x x)
>   filterElemWhichIsHere x xs | Yes Refl with (decEqFilter x xs)
>     filterElemWhichIsHere x xs | Yes Refl | (i ** vs) = (i ** Refl)
>   filterElemWhichIsHere x xs | No contra = void $ contra Refl
>
> countOccurrence : DecEq vertices
>               => {i, j : vertices}
>               -> (edges : Vect n (vertices, vertices))
>               -> Elem (i, j) edges
>               -> Fin $ fst $ decEqFilter (i, j) edges
> countOccurrence {i} {j} ((i, j) :: xs) Here with (decEq (i,j) (i,j))
>   countOccurrence {i} {j} ((i, j) :: xs) Here | Yes Refl with (decEqFilter (i, j) xs)
>     countOccurrence {i} {j} ((i, j) :: xs) Here | Yes Refl | (k ** vs) = 0
>   countOccurrence {i} {j} ((i, j) :: xs) Here | No contra = void $ contra Refl
> countOccurrence {i} {j} ((k, l) :: xs) (There e) with (decEq (i, j) (k, l))
>   countOccurrence {i} {j} ((i, j) :: xs) (There e) | Yes Refl with (decEq (i, j) (i, j))
>     countOccurrence {i} {j} ((i, j) :: xs) (There e) | Yes Refl | Yes Refl with (decEqFilter (i, j) xs) proof prf
>       countOccurrence {i} {j} ((i, j) :: xs) (There e) | Yes Refl | Yes Refl | (k ** vs)
>         = FS $ rewrite cong {f=DPair.fst} prf in countOccurrence {i} {j} xs e
>     countOccurrence {i} {j} ((i, j) :: xs) (There e) | Yes Refl | No contra = void $ contra Refl
>   countOccurrence {i} {j} ((k, l) :: xs) (There e) | No contra with (decEqFilter (i, j) xs) proof prf
>     countOccurrence {i} {j} ((k, l) :: xs) (There e) | No contra | (m ** vs) with (decEq k i)
>       countOccurrence {i} {j} ((i, l) :: xs) (There e) | No contra | (m ** vs) | Yes Refl with (decEq l j)
>         countOccurrence {i} {j} ((i, j) :: xs) (There e) | No contra | (m ** vs) | Yes Refl | Yes Refl
>           = void $ contra Refl
>         countOccurrence {i} {j} ((i, l) :: xs) (There e) | No contra | (m ** vs) | Yes Refl | No contra'
>           = countOccurrence {i} {j} xs e
>       countOccurrence {i} {j} ((k, l) :: xs) (There e) | No contra | (m ** vs) | No contra' with (decEq l j)
>         countOccurrence {i} {j} ((k, j) :: xs) (There e) | No contra | (m ** vs) | No contra' | Yes Refl
>           = countOccurrence {i} {j} xs e
>         countOccurrence {i} {j} ((k, l) :: xs) (There e) | No contra | (m ** vs) | No contra' | No contra''
>           = countOccurrence {i} {j} xs e
>
> edgeListPath : DecEq vertices
>             => {edges : Vect n (vertices, vertices)}
>             -> {i, j : vertices}
>             -> EdgeListPath edges i j
>             -> Path (edgeList edges) i j
> edgeListPath Empty           = Nil
> edgeListPath (Cons elem elp) = (countOccurrence edges elem) :: (edgeListPath elp)
