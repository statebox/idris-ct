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
> import Free.Graph
> import Free.PathCategory
>
> %access public export
> %default total
>
> forgetCat : (c : Category) -> Graph (obj c)
> forgetCat c = MkGraph (mor c)
>
> record GraphMorphism (v1 : Type) (v2 : Type) (g1 : Graph v1) (g2 : Graph v2) where
>   constructor MkGraphMorphism
>   mapVert : v1 -> v2
>   mapEdge : (w1, w2 : v1) -> Edge g1 w1 w2 -> Edge g2 (mapVert w1) (mapVert w2)
>
> foldPath :
>      (g : Graph v)
>   -> (gm : GraphMorphism v (obj cat) g (forgetCat cat))
>   -> Path (Edge g) a b
>   -> mor cat (mapVert gm a) (mapVert gm b)
> foldPath {cat} {a} g gm Nil        = identity cat (mapVert gm a)
> foldPath {cat}     g gm (eij :: p) = compose cat _ _ _ (mapEdge gm _ _ eij) (foldPath g gm p)
>
> freeFunctor :
>      (g : Graph v)
>   -> (cat : Category)
>   -> GraphMorphism v (obj cat) g (forgetCat cat)
>   -> CFunctor (pathCategory g) cat
> freeFunctor (MkGraph e) cat gm = MkCFunctor
>   (mapVert gm)
>   (\a, b, p => foldPath {cat} (MkGraph e) gm p)
>   (\_ => Refl)
>   preserveComp
>   where
>     preserveComp :
>          (x, y, z : v)
>       -> (f : Path e x y)
>       -> (g : Path e y z)
>       -> foldPath (MkGraph e) gm (joinPath f g)
>        = compose cat
>                  (mapVert gm x)
>                  (mapVert gm y)
>                  (mapVert gm z)
>                  (foldPath (MkGraph e) gm f)
>                  (foldPath (MkGraph e) gm g)
>     preserveComp y y z Nil      g = sym $ leftIdentity cat (mapVert gm y) (mapVert gm z) (foldPath (MkGraph e) gm g)
>     preserveComp x y z (fab::f) g = rewrite preserveComp _ _ _ f g
>                                     in associativity cat _ _ _ _ (mapEdge gm x _ fab)
>                                                                  (foldPath (MkGraph e) gm f)
>                                                                  (foldPath (MkGraph e) gm g)
>
> freeEmbeddingMorphism : (g : Graph v) -> GraphMorphism v (obj (pathCategory g)) g (forgetCat $ pathCategory g)
> freeEmbeddingMorphism (MkGraph _) = MkGraphMorphism id (\_, _, e => [e])
>
> liftPathToMorphism :
>      (g : Graph v)
>   -> Path (Edge g) a b
>   -> mor (pathCategory g) (mapVert (freeEmbeddingMorphism g) a) (mapVert (freeEmbeddingMorphism g) b) -- should actually be mor (pathCategory g) a b
> liftPathToMorphism g p = foldPath g (freeEmbeddingMorphism g) p
