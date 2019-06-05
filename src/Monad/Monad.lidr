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

\newcommand{\anonfunc}[2]{\big[#1 \mapsto #2\big]}

\subsection{Monads}

A monad is a monoid in the (monoidal) category of endofunctors of a category $\mathcal{C}$, called $\textbf{End}(\mathcal{C})$. Informally speaking, this means that to define a monad, we need to write down the definition of a monoid using only tools available in monoidal categories, and then replace the category of sets with the category of endofunctors on $\mathcal{C}$.

\subsubsection{Monoids}

A monoid $M$ is a set (which is also called $M$) equipped with a binary operation $+ : M \times M \to M$ and an element $0 \in M$, such that for all $a, b, c \in M$ the following laws hold:
\[ (a + b) + c = a + (b + c), a + 0 = a \text{, and } 0 + a = 0 \]
To express this definition categorically, we first need to get around the fact that objects in categories do not have elements in general. To get around this, we use the notion of a terminal object, which in the category of sets happens to be any set that has just a single element (not every category has a terminal object, but if it exists, it is essentially unique, i.e. unique up to isomorphism). We pick any such set and call it $I$ (and its unique element will be called $*$). Now, the unit $0$ of $M$ can also be thought of as a map $0 : I \to M$, which is the map that sends $*$ to the element $0$.

Now, the unit and associativity laws also need to be expressed without elements. This means in particular that we cannot pick the three elements $a, b$ and $c$. To get around this, we can leave the variables unbound like this:
\[ \anonfunc{(a, b, c)}{(a + b) + c} = \anonfunc{(a, b, c)}{a + (b + c)}  \]
and in the case of the unit laws, we use
\[ \anonfunc{a}{a + 0(*)} = \anonfunc{a}{a}, \text{and } \anonfunc{a}{0(*) + a} = \anonfunc{a}{a}. \]
Note that because $0$ is now a morphism, we need to pass $*$ to $0$ to turn it into an element of $M$. To write this cateorically, it is necessary to change the equations for the unit laws slightly:
\[ \anonfunc{(a, *)}{a + 0(*)} = \anonfunc{(a, *)}{a}, \text{and } \anonfunc{(a, *)}{0(*) + a} = \anonfunc{(a, *)}{a}. \]
The difference here is that $*$ is now just a locally bound element of $I$, instead of a globally bound element. This means it is possible to write the equations using only categorical constructions, as follows:

\begin{center}
  \begin{tikzcd}
    M \times M \times M \arrow[r, "id \times +"] \arrow[d, "+ \times id"] & M \times M \arrow[d, "+"]
     & & M \times I \arrow[dr, "\pi_1"] \arrow[r, "id \times 0"] & M \times M \arrow[d, "+"]
     & & I \times M \arrow[dr, "\pi_2"] \arrow[r, "0 \times id"] & M \times M \arrow[d, "+"] \\
    M \times M \arrow[r, "+"]                                             & M
     & &                                             & M
     & &                                             & M
  \end{tikzcd}
\end{center}

Thus, if a category $\mathcal{C}$ admits finite products and a terminal object, a monoid in $\mathcal{C}$ is an object $M$ together with two morphisms, $0 : I \to M$ and $+ : M \times M \to M$, such that the above diagrams commute. Note that in the diagram for associativity, the coherence isomorphism $M \times (M \times M) \simeq (M \times M) \times M$ was omitted.

We need a slight generalization of this though, because while $\textbf{End}(\mathcal{C})$ might have products and a terminal object (it does, if and only if $\mathcal{C}$ does), a monoid in that structure (if it is there) is not a monad but just a functor that coherently maps objects to monoids. So, if $\mathcal{C}$ is a monoidal categoy, then replacing the initial object by the unit, the product by the tensor product and associativity and projections by the coherence morphisms in the above definition of a monoid gives a monoid in $\mathcal{C}$. If the monoidal structure on $\mathcal{C}$ is given by its initial object and products (called a cartesian monoidal structure), we recover the previous definition.

\subsubsection{Monads}

  By the previous discussion, to describe a monad in a category $\mathcal{C}$, we need to first describe the monoidal structure on $\textbf{End}(\mathcal{C})$. In addition to the cartesian monoidal structure (if it exists), one can give a monoidal structure by letting the unit be the identity functor, and the tensor product be composition. This is a common thing to do for giving endomorphisms the structure of a monoid in algebra. So, to conclude, to specify a monad, it is necessary to give an endofunctor $M : C \to C$, together with natural transformations $\epsilon : Id \to M$ and $\eta : M \circ M \to M$, such that the above diagrams commute.

> module Monad.Monad
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import CategoryReasoning as CR
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Syntax.PreorderReasoning
>
> %access public export
> %default total
>
> qed : (a : obj (functorCategory cat cat)) -> mor _ a a
> qed = CR.qed (functorCategory cat cat)
>
> step :
>      (a : obj (functorCategory cat cat))
>   -> mor (functorCategory cat cat) a b
>   -> mor (functorCategory cat cat) b c
>   -> mor (functorCategory cat cat) a c
> step = CR.step (functorCategory cat cat)
>
> liftEquality : (a, b : obj (functorCategory cat cat)) -> a = b -> mor (functorCategory cat cat) a b
> liftEquality = CR.liftEquality (functorCategory cat cat)
>
> record Monad (cat : Category) where
>   constructor MkMonad
>   functor : CFunctor cat cat
>   unit : NaturalTransformation _ _ (idFunctor cat) functor
>   multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor
>   associativity :
>     ((functorComposition _ _ _ functor (functorComposition _ _ _ functor functor))
>     ={ composeNatTransFunctor _ _ _ functor (functorComposition _ _ _ functor functor) functor multiplication }=
>     (functorComposition cat cat cat functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>     =
>     ((functorComposition cat cat cat functor (functorComposition cat cat cat functor functor))
>     ={ liftEquality
>          (functorComposition cat cat cat functor (functorComposition cat cat cat functor functor))
>          (functorComposition cat cat cat (functorComposition cat cat cat functor functor) functor)
>          (catsAssociativity _ _ _ _ functor functor functor) }=
>     (functorComposition cat cat cat (functorComposition cat cat cat functor functor) functor)
>     ={ composeFunctorNatTrans cat cat cat
>          (functorComposition cat cat cat functor functor) functor multiplication functor }=
>     (functorComposition cat cat cat functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>   leftUnit :
>     (functor
>     ={ liftEquality functor (functorComposition _ _ _ (idFunctor cat) functor)
>          (sym $ catsLeftIdentity cat cat functor) }=
>     (functorComposition _ _ _ (idFunctor cat) functor)
>     ={ composeFunctorNatTrans cat cat cat (idFunctor cat) functor unit functor }=
>      (functorComposition _ _ _ functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>     =
>     idTransformation cat cat functor
>   rightUnit :
>     (functor
>     ={ liftEquality functor (functorComposition _ _ _ functor (idFunctor cat))
>          (sym $ catsRightIdentity cat cat functor) }=
>     (functorComposition _ _ _ functor (idFunctor cat))
>     ={ composeNatTransFunctor cat cat cat functor (idFunctor cat) functor unit }=
>      (functorComposition _ _ _ functor functor)
>     ={ multiplication }=
>     functor
>     QED)
>     =
>     idTransformation cat cat functor
