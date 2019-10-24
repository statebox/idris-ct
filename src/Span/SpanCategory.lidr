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

> module Span.SpanCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import Cats.FunctorsAsCategory
> import Data.Vect
> import Free.Path
> import Span.Span
> import Utils
>
> %access public export
> %default total
>
> SpanMorphism : {cat : Category}
>             -> {a, b : obj cat}
>             -> (s1, s2 : Span a b)
>             -> Type
> SpanMorphism {cat} {a} {b} s1 s2 =
>   (nt  : NaturalTransformation SpanIndexCategory cat (spanFunctor s1) (spanFunctor s2)
>   -- ** e : (component nt X = identity cat a)
>   **      component nt Y = identity cat b)
>
> spanIdentity : {cat : Category}
>             -> {a, b : obj cat}
>             -> (s : Span a b)
>             -> SpanMorphism s s
> spanIdentity {cat} s =
>   (  idTransformation SpanIndexCategory cat (spanFunctor s)
>   -- ** rewrite fst $ snd s in Refl
>   ** rewrite snd $ snd s in Refl)
>
> spanCompositionLemma : {cat : Category}
>                     -> {a, b : obj cat}
>                     -> (s1, s2, s3 : Span a b)
>                     -> (f : SpanMorphism s1 s2)
>                     -> (g : SpanMorphism s2 s3)
>                     -> compose cat (mapObj (fst s1) Y)
>                                    (mapObj (fst s2) Y)
>                                    (mapObj (fst s3) Y)
>                                    (component (fst f) Y)
>                                    (component (fst g) Y)
>                      = compose cat b b b (identity cat b) (identity cat b)
> spanCompositionLemma {cat} {a} {b} (fun1 ** prfX1 ** prfY1) (fun2 ** prfX2 ** prfY2) (fun3 ** prfX3 ** prfY3) (fnt ** fprf) (gnt ** gprf) =
>   composeEq cat prfY1 prfY2 prfY3 fprf gprf
>
> spanComposition : {cat : Category}
>                -> {a, b : obj cat}
>                -> (s1, s2, s3 : Span a b)
>                -> SpanMorphism s1 s2
>                -> SpanMorphism s2 s3
>                -> SpanMorphism s1 s3
> spanComposition {cat} {a} {b} s1 s2 s3 f g =
>   (  naturalTransformationComposition SpanIndexCategory
>                                       cat
>                                       (spanFunctor s1)
>                                       (spanFunctor s2)
>                                       (spanFunctor s3)
>                                       (DPair.fst f)
>                                       (DPair.fst g)
>   -- ** trans (DPair.fst $ DPair.snd f) (DPair.fst $ DPair.snd g)
>   ** trans (spanCompositionLemma {cat} {a} {b} s1 s2 s3 f g) (leftIdentity cat b b (identity cat b)))
>
> -- SpanCategory : {cat : Category}
> --             -> (a, b : obj cat)
> --             -> Category
> -- SpanCategory a b = MkCategory
> --   (Span a b)
> --   (SpanMorphism {a} {b})
> --   spanIdentity
> --   spanComposition
> --   (\a, b, f => ?lId)
> --   (\a, b, f => ?rId)
> --   (\a, b, c, d, f, g, h => ?assoc)
