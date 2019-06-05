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

\subsection{The module |Functor|}
%
%
In the last Section, we have defined a type |Category|, which is great since many different structures can be formulated as instances of categories. On the other hand, categories are structures themselves, and are themselves the object of a category, the category of categories! The goal of this Section is to define morphisms between categories, formally called \emph{functors}.

A functor maps a category to another category in the very same way a function maps a set to another set. But, since categories have more structure than sets, we want this structure to be preserved in the process. As before we start declaring |Functor| as a module. Notice how, being |Functor| defined for categories, we import the module |Category| we already defined in the previous Section.
%
%
< module Basic.Functor
<
< import Basic.Category
<
< %access public export
< %default total
%
We will again employ |record| to implement functors, as we did for categories.
%
%

< record CFunctor (cat1 : Category) (cat2 : Category) where

%
Notice how we had to use the name |CFunctor| to avoid clashings with |Functor|, which is a type already defined by Idris. We will moreover use |constructor| again to construct concrete values of type |CFunctor|.
%
%

<   constructor MkCFunctor

%
%
%
\subsubsection{The components}
%
%
All the preliminary work is done, let's now start with the real stuff. As we said, a functor between categories $\mathcal{C}$ and $\mathcal{D}$, formally denoted with $F:\mathcal{C} \to \mathcal{D}$, is a mapping. We begin by noticing how a category consists of objects and morphisms, so our functor will have to act both on objects \emph{and} morphisms.

We start with the objects, where we declare our functor to be simply a map: If we have $F:\mathcal{C} \to \mathcal{D}$ then we map every object $a$ of $\mathcal{C}$ to an object $Fa$ of $\mathcal{D}$. In Idris, this becomes:
%
%

<   mapObj          : obj cat1 -> obj cat2

%
As we would expect, |mapObj| takes an object of |cat1|, extracted from the |Category| type using the |obj| value, and maps it to an object of |cat2|.

For morphisms, we do pretty much the same. Notice however that, given a functor $F: \mathcal{C} \to \mathcal{D}$, a morphism $f:a \to b$ has a domain and a codomain, namely the objects $a,b$ of $\mathcal{C}$. We want to map $f$ to a morphism of $\mathcal{D}$, but from what to what? Since we want to respect the structure it makes sense to use what we already defined for objects, and map $f:a \to b$ to a morphism $Ff: Fa \to Fb$.

In our implementation we model this as follows:
%
%

<   mapMor          : (a, b : obj cat1)
<                  -> mor cat1 a b
<                  -> mor cat2 (mapObj a) (mapObj b)

%
|mapMor| is just a map between morphisms of |cat1| and morphisms of |cat2| which is consistent with respect to the map we already defined on objects
This time though our implementation forces us to specify also objects |a| and |b| of |cat1| since the way we defined |mor| expects them.
%
%
%
\subsubsection{The laws}
%
%
Now, we recall that a category is not just a collection of objects and morphisms. We have indeed more structure we have to take into account, namely identities and composition. Since we want functors to be defined so that they respect the categorical structure, it makes sense to require that identities get carried to identities. This translates, for each object $a$ of $\mathcal{C}$, in the equation between morphisms of $\mathcal{D}$:
%
%
\begin{equation*}
F id_a = id_{Fa}
\end{equation*}
%
In Idris we represent this by defining a function that, for each object |a| of |cat1|, provides a proof that the identity on |a| in |cat1| is mapped to the identity on |mapObj a| in |cat2|:
%
%

<   preserveId      : (a : obj cat1)
<                  -> mapMor a a (identity cat1 a) = identity cat2 (mapObj a)

%
Finally, we must account for composition. The idea here is that, if functors respects the categorical structure, it shouldn't matter if we compose two morphisms first and then apply the functor or viceversa. Mathematically, we represent this, for $f:a \to b$ and $g: b \to c$ in $\mathcal{C}$, with the equation between morphisms of $\mathcal{D}$:
%
%
\begin{equation*}
F(f;g) = Ff;Fg
\end{equation*}
%
If you like it more, this can also be depicted as a commutative diagram:
%
%
\begin{center}
  \begin{tikzcd}
    Fa \arrow[d, "Ff"']\arrow[dr, "Ff;Fg"]\\
    Fb \arrow[r, "Fg"']& Fc\\
  \end{tikzcd}
\end{center}
%
In Idris, we proceed in a way similar to what we did for identities:
%
%

<   preserveCompose : (a, b, c : obj cat1)
<                  -> (f : mor cat1 a b)
<                  -> (g : mor cat1 b c)
<                  -> mapMor a c (compose cat1 a b c f g)
 <                   = compose cat2 (mapObj a) (mapObj b) (mapObj c) (mapMor a b f) (mapMor b c g)

%
Given three objects |a, b, c : obj cat1|, which are the domains/codomains of the morphisms we are going to compose, and given two of these morphisms |f : mor cat1 a b| and |g : mor cat1 b c| respectively, we produce a proof that |mapMor| and |compose| commute with each other.
%
%
%
\subsubsection{conclusion}
%
%
The code covered above completes our definition of |CFunctor|, which we provide in its entirety below:

> module Basic.Functor
>
> import Basic.Category
>
> %access public export
> %default total
>
> record CFunctor (cat1 : Category) (cat2 : Category) where
>   constructor MkCFunctor
>   mapObj          : obj cat1 -> obj cat2
>   mapMor          : (a, b : obj cat1)
>                  -> mor cat1 a b
>                  -> mor cat2 (mapObj a) (mapObj b)
>   preserveId      : (a : obj cat1)
>                  -> mapMor a a (identity cat1 a) = identity cat2 (mapObj a)
>   preserveCompose : (a, b, c : obj cat1)
>                  -> (f : mor cat1 a b)
>                  -> (g : mor cat1 b c)
>                  -> mapMor a c (compose cat1 a b c f g)
>                   = compose cat2 (mapObj a) (mapObj b) (mapObj c) (mapMor a b f) (mapMor b c g)
>
> functorEq :
>      (cat1, cat2 : Category)
>   -> (fun1, fun2 : CFunctor cat1 cat2)
>   -> ((a : obj cat1) -> (mapObj fun1 a = mapObj fun2 a))
>   -> ((a, b : obj cat1) -> (f : mor cat1 a b) -> (mapMor fun1 a b f = mapMor fun2 a b f))
>   -> fun1 = fun2
> functorEq cat1 cat2 fun1 fun2 prfObj prfMor = really_believe_me ()
>
> idFunctor : (cat : Category) -> CFunctor cat cat
> idFunctor cat = MkCFunctor
>   id
>   (\a, b => id)
>   (\a => Refl)
>   (\a, b, c, f, g => Refl)
>
> functorComposition :
>      (cat1, cat2, cat3 : Category)
>   -> CFunctor cat1 cat2
>   -> CFunctor cat2 cat3
>   -> CFunctor cat1 cat3
> functorComposition cat1 cat2 cat3 fun1 fun2 = MkCFunctor
>   ((mapObj fun2) . (mapObj fun1))
>   (\a, b => (mapMor fun2 (mapObj fun1 a) (mapObj fun1 b)) . (mapMor fun1 a b))
>   (\a => trans (cong (preserveId fun1 a)) (preserveId fun2 (mapObj fun1 a)))
>   (\a, b, c, f, g => trans (cong (preserveCompose fun1 a b c f g))
>                            (preserveCompose fun2
>                                             (mapObj fun1 a)
>                                             (mapObj fun1 b)
>                                             (mapObj fun1 c)
>                                             (mapMor fun1 a b f)
>                                             (mapMor fun1 b c g)))
