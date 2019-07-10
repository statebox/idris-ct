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

> module Free.FreeFunctor
>
> import Basic.Category
> import Basic.Functor
> import Free.Category
>
> %access public export
> %default total
>
> forgetCat : Category -> Graph
> forgetCat c = MkGraph (obj c) (mor c)
>
> record GraphMorphism (g1 : Graph) (g2 : Graph) where
>   constructor MkGraphMorphism
>   mapVert : Vert g1 -> Vert g2
>   mapEdge : (v1, v2 : Vert g1) -> Edge g1 v1 v2 -> Edge g2 (mapVert v1) (mapVert v2)
>
> foldPath :
>      (g : Graph)
>   -> (gm : GraphMorphism g (forgetCat cat))
>   -> Path (Edge g) a b
>   -> mor cat (mapVert gm a) (mapVert gm b)
> foldPath {cat} {a} g gm Nil        = identity cat (mapVert gm a)
> foldPath {cat}     g gm (eij :: p) = compose cat _ _ _ (mapEdge gm _ _ eij) (foldPath g gm p)
>
> freeFunctor :
>      (g : Graph)
>   -> (cat : Category)
>   -> GraphMorphism g (forgetCat cat)
>   -> CFunctor (pathCategory g) cat
> freeFunctor (MkGraph v e) cat gm = MkCFunctor
>   (mapVert gm)
>   (\a, b, p => foldPath {cat} (MkGraph v e) gm p)
>   (\_ => Refl)
>   preserveComp
>   where
>     preserveComp :
>          (x, y, z : v)
>       -> (f : Path e x y)
>       -> (g : Path e y z)
>       -> foldPath (MkGraph v e) gm (joinPath f g)
>        = compose cat
>                  (mapVert gm x)
>                  (mapVert gm y)
>                  (mapVert gm z)
>                  (foldPath (MkGraph v e) gm f)
>                  (foldPath (MkGraph v e) gm g)
>     preserveComp y y z Nil      g = sym $ leftIdentity cat (mapVert gm y) (mapVert gm z) (foldPath (MkGraph v e) gm g)
>     preserveComp x y z (fab::f) g = rewrite preserveComp _ _ _ f g
>                                     in associativity cat _ _ _ _ (mapEdge gm x _ fab)
>                                                                  (foldPath (MkGraph v e) gm f)
>                                                                  (foldPath (MkGraph v e) gm g)
>
> freeEmbeddingMorphism : (g : Graph) -> GraphMorphism g (forgetCat $ pathCategory g)
> freeEmbeddingMorphism (MkGraph _ _) = MkGraphMorphism id (\_, _, e => [e])
>
> liftPathToMorphism :
>      (g : Graph)
>   -> Path (Edge g) a b
>   -> mor (pathCategory g) (mapVert (freeEmbeddingMorphism g) a) (mapVert (freeEmbeddingMorphism g) b) -- should actually be mor (pathCategory g) a b
> liftPathToMorphism g p = foldPath g (freeEmbeddingMorphism g) p
