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
>   ** e : (component nt X = identity cat a)
>   **      component nt Y = identity cat b)
>
> spanIdentity : {cat : Category}
>             -> {a, b : obj cat}
>             -> (s : Span a b)
>             -> SpanMorphism s s
> spanIdentity {cat} s =
>   (  idTransformation SpanIndexCategory cat (spanFunctor s)
>   ** rewrite fst $ snd s in Refl
>   ** rewrite snd $ snd s in Refl)
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
>   ** trans (composeEq cat (fst $ snd s1) (fst $ snd s2) (fst $ snd s3) (fst $ snd f) (fst $ snd g))
>            (leftIdentity cat a a (identity cat a))
>   ** ?qwer)
>   -- TODO: find out why the compiler crashes with the code below
> --  ** trans (composeEq cat (snd $ snd s1) (snd $ snd s2) (snd $ snd s3) (snd $ snd f) (snd $ snd g))
> --           (leftIdentity cat b b (identity cat b)))
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
