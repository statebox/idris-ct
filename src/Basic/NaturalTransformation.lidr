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

\subsection{The module |NaturalTransformation|}
%
%
Perhaps unsurprisingly, after having defined categories and functors we switch to the next basic element of category theory, natural transformations. Natural transformations are defined between functors, and hence we start by importing what we did up to now, namely the modules |Category| and |Functor|.
%
< module Basic.NaturalTransformation
<
< import Basic.Category
< import Basic.Functor
<
< %access public export
< %default total
%
As we did for the previous modules, to implement |NaturalTransformation| we will resort again to records and constructors. In the following snippet, you can see how the record |NaturalTransformation| is specified by two categories $\mathcal{C}, \mathcal{D}$, implemented as |cat1| and |cat2| respectively, and two functors $F,G:\mathcal{C} \to \mathcal{D}$ between them, implemented as |func1| and |func2|.
%
< record NaturalTransformation
<   (cat1 : Category)
<   (cat2 : Category)
<   (fun1 : CFunctor cat1 cat2)
<   (fun2 : CFunctor cat1 cat2)
<   where
<     constructor MkNaturalTransformation
%
%
%
\subsubsection{The components}
%
%
Recall that, given functors $F,G: \mathcal{C} \to \mathcal{D}$, a natural transformation $\alpha: F \to G$ is defined by specifying, for each object $A$ of $\mathcal{C}$, a morphism $\alpha_A: FA \to GA$ in $\mathcal{D}$, subject to some properties we will get to later. We define the components of a natural transformation, for each object |a| of |cat1|, as follows:
%
%
<     component : (a : obj cat1) -> mor cat2 (mapObj fun1 a) (mapObj fun2 a)
%
|mapObj fun1 a| means that we are applying |fun1| to the object |a|. This is akin to consider $FA$. Similarly, |mapObj fun2 a| is akin to consider $GA$. These two objects, belonging to |cat2| (standing for $\mathcal{D}$ in our mathematical definition), get fed to |mor| producing the homset of morphisms from $FA$ to $GA$. a term of this type is just the implementation of a morphism $FA \to GA$, and it is precisely what we associate to an object |a|.
%
%
%
\subsubsection{The laws}
%
%
Up to now, we defined, for a natural transformation $\alpha:F \to G$, its components $\alpha_A: FA \to GA$ for each $A$ object of $\mathcal{C}$. These components have to be related with each other by a property, stating that for each morphism $f:A \to B$ in $\mathcal{C}$ the following square commutes:
%
%
\begin{center}
  \begin{tikzcd}
    FA \arrow[d, "\alpha_A"']\arrow[r, "Ff"] & FB\arrow[d, "\alpha_B"]\\
    FB \arrow[r, "Gf"']& GB
  \end{tikzcd}
\end{center}
%
%
This property lets us interpret a natural transformation as a way to link the result of applying $F$ to the result of applying $G$ in a way that cooperates with the structure, namely morphism composition: In fact, notice how the commutative square above guarantees that given $f:A \to B$ and $g: B \to C$ in $\mathcal{C}$, applying the natural transformation law above to $f;g$ has the same effect of pasting together the commutative squares for $f$ and $g$, that is, the following diagram commutes:
%
%
\begin{center}
  \begin{tikzcd}
    FA \arrow[d, "\alpha_A"']\arrow[r, "Ff"]\arrow[rr, bend left, "F(f;g)"] & FB\arrow[d, "\alpha_B"]\arrow[r, "Fg"] & FC\arrow[d,"\alpha_C"]\\
    FB \arrow[r, "Gf"']\arrow[rr, bend right, "G(f;g)"']& GB\arrow[r, "Gg"'] &GC
  \end{tikzcd}
\end{center}
%
%
In Idris, as we expect, this property  is expressed by returning a proof of the equation expressed by the diagram above for each morphism $f$:
%
%
<     commutativity : {a, b : obj cat1}
<                  -> (f : mor cat1 a b)
<                  -> compose cat2
<                             (mapObj fun1 a)
<                             (mapObj fun2 a)
<                             (mapObj fun2 b)
<                             (component a)
<                             (mapMor fun2 a b f)
<                   = compose cat2
<                             (mapObj fun1 a)
<                             (mapObj fun1 b)
<                             (mapObj fun2 b)
<                             (mapMor fun1 a b f)
<                             (component b)
%
Here, we specify a morphism |f| from |a| to |b| in |cat1|. From this, we can consider $Ff: FA \to FB$, specified by |mapMor fun1 a b f|, and $Gf: GA \to GB$, specified by |mapMor fun2 a b f|. The equation modeled by the diagram above reads:
%
%
\begin{equation*}
    \alpha_A;Gf = Ff;\alpha_B
\end{equation*}
%
$\alpha_A$ and $\alpha_B$ are respectively |component a| and |component b| in our implementation. We can then apply |compose| to obtain the two sides of the equation, leading to the type
%
%
< compose cat2
<         (mapObj fun1 a)
<         (mapObj fun2 a)
<         (mapObj fun2 b)
<         (component a)
<         (mapMor fun2 a b f)
< = compose cat2
<           (mapObj fun1 a)
<           (mapObj fun1 b)
<           (mapObj fun2 b)
<           (mapMor fun1 a b f)
<           (component b)
%
%
%
\subsubsection{Conclusion}
%
%
The code above is everything we need to define what a natural transformation is. In the next sections, we will proceed by making this definition more specific and obtain a natural isomorphism. The code of this section, presented as a unique block, can be found below.

> module Basic.NaturalTransformation
>
> import Basic.Category
> import Basic.Functor
> import Syntax.PreorderReasoning
>
> %access public export
> %default total
>
> record NaturalTransformation
>   (cat1 : Category)
>   (cat2 : Category)
>   (fun1 : CFunctor cat1 cat2)
>   (fun2 : CFunctor cat1 cat2)
>   where
>     constructor MkNaturalTransformation
>     component : (a : obj cat1) -> mor cat2 (mapObj fun1 a) (mapObj fun2 a)
>     commutativity : (a, b : obj cat1)
>                  -> (f : mor cat1 a b)
>                  -> compose cat2
>                             (mapObj fun1 a)
>                             (mapObj fun2 a)
>                             (mapObj fun2 b)
>                             (component a)
>                             (mapMor fun2 a b f)
>                   = compose cat2
>                             (mapObj fun1 a)
>                             (mapObj fun1 b)
>                             (mapObj fun2 b)
>                             (mapMor fun1 a b f)
>                             (component b)
>
> naturalTransformationExt :
>   (cat1, cat2 : Category)
>   -> (fun1, fun2 : CFunctor cat1 cat2)
>   -> (trans1, trans2 : NaturalTransformation cat1 cat2 fun1 fun2)
>   -> ((a : obj cat1) -> component trans1 a = component trans2 a)
>   -> trans1 = trans2
> naturalTransformationExt cat1 cat2 fun1 fun2 trans1 trans2 eq = really_believe_me()
>
> naturalTransformationComposition :
>   (cat1, cat2 : Category)
>   -> (fun1, fun2, fun3 : CFunctor cat1 cat2)
>   -> NaturalTransformation cat1 cat2 fun1 fun2
>   -> NaturalTransformation cat1 cat2 fun2 fun3
>   -> NaturalTransformation cat1 cat2 fun1 fun3
> naturalTransformationComposition cat1 cat2 fun1 fun2 fun3
>   (MkNaturalTransformation comp1 comm1)
>   (MkNaturalTransformation comp2 comm2) =
>     MkNaturalTransformation
>       (\a => compose cat2 (mapObj fun1 a) (mapObj fun2 a) (mapObj fun3 a) (comp1 a) (comp2 a))
>       (\x, y, f =>
>         (compose cat2 _ _ _ (compose cat2 _ _ _ (comp1 x) (comp2 x)) (mapMor fun3 _ _ f))
>           ={ sym $ (associativity cat2 _ _ _ _ (comp1 x) (comp2 x) (mapMor fun3 x y f)) }=
>         (compose cat2 _ _ _ (comp1 x) (compose cat2 _ _ _ (comp2 x) (mapMor fun3 _ _ f)))
>           ={ cong $ comm2 x y f }=
>         (compose cat2 _ _ _ (comp1 x) (compose cat2 _ _ _ (mapMor fun2 _ _ f) (comp2 y)))
>           ={ associativity cat2 _ _ _ _ (comp1 x) (mapMor fun2 x y f) (comp2 y) }=
>         (compose cat2 _ _ _ (compose cat2 _ _ _ (comp1 x) (mapMor fun2 _ _ f)) (comp2 y))
>           ={ cong {f = \h => compose cat2 _ _ _ h (comp2 y)} $ comm1 x y f }=
>         (compose cat2 _ _ _ (compose cat2 _ _ _ (mapMor fun1 x y f) (comp1 y)) (comp2 y))
>           ={ sym $ associativity cat2 _ _ _ _ (mapMor fun1 _ _ f) (comp1 y) (comp2 y) }=
>         (compose cat2 _ _ _ (mapMor fun1 _ _ f) (compose cat2 _ _ _ (comp1 y) (comp2 y)))
>       QED)
>
> composeFunctorNatTrans :
>   (cat1, cat2, cat3 : Category)
>   -> (fun1, fun2 : CFunctor cat1 cat2)
>   -> (fun3 : CFunctor cat2 cat3)
>   -> NaturalTransformation cat1 cat2 fun1 fun2
>   -> NaturalTransformation cat1 cat3
>      (functorComposition cat1 cat2 cat3 fun1 fun3)
>      (functorComposition cat1 cat2 cat3 fun2 fun3)
> composeFunctorNatTrans cat1 cat2 cat3 fun1 fun2 fun3
>   (MkNaturalTransformation component commutativity) =
>     MkNaturalTransformation
>       (\x => mapMor fun3 (mapObj fun1 x) (mapObj fun2 x) (component x))
>       (\x, y, f =>
>         (compose cat3 _ _ _ (mapMor fun3 _ _ (component x)) (mapMor fun3 _ _ $ mapMor fun2 x y f))
>           ={ sym $ preserveCompose fun3 _ _ _ (component x) (mapMor fun2 x y f) }=
>         (mapMor fun3 _ _ $ compose cat2 _ _ _ (component x) (mapMor fun2 x y f))
>           ={ cong {f = mapMor fun3 (mapObj fun1 x) (mapObj fun2 y)} $ commutativity x y f }=
>         (mapMor fun3 _ _ $ compose cat2 _ _ _ (mapMor fun1 x y f) (component y))
>           ={ preserveCompose fun3 _ _ _ (mapMor fun1 x y f) (component y) }=
>         (compose cat3 _ _ _ (mapMor fun3 _ _ (mapMor fun1 x y f)) (mapMor fun3 _ _ (component y)))
>       QED)
>
> composeNatTransFunctor :
>   (cat1, cat2, cat3 : Category)
>   -> (fun1 : CFunctor cat1 cat2)
>   -> (fun2, fun3 : CFunctor cat2 cat3)
>   -> NaturalTransformation cat2 cat3 fun2 fun3
>   -> NaturalTransformation cat1 cat3
>     (functorComposition cat1 cat2 cat3 fun1 fun2)
>     (functorComposition cat1 cat2 cat3 fun1 fun3)
> composeNatTransFunctor cat1 cat2 cat3 fun1 fun2 fun3
>   (MkNaturalTransformation component commutativity) =
>     MkNaturalTransformation
>       (\x => component (mapObj fun1 x))
>       (\x, y, f => commutativity _ _ (mapMor fun1 x y f))
