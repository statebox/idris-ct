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

This library defines various concepts of category theory. Every subsection will document in detail how a module has been implemented.

\subsection{The module |Category|}

We start with the most basic thing we can do, namely the definition of category. First things first, we start by defining our module.
%
%
< module Basic.Category
<
< %access public export
< %default total
%
Then, we implement the basic elements a category consists of.
%
%
< record Category where
%
A |record| in Idris is just the product type of several values, which are called the fields of the record. It's a convenient syntax because Idris provides field access and update functions automatically for us. We add also the constructor |MkCategory| to be able to construct concrete values of type |Category|:
%
%
<   constructor MkCategory
%
%
%
\subsubsection{The elements}
%
%
At its most basic level, a category is a collection of things, called \emph{objects}. To specify what these things are, we add to our definition a field to keep track of them:
%
%
<   obj : Type
%
You can think about |obj| as a collection of dots, which will be items we want to talk about in our category.

Next thing up, we need ways to go from one dot to the other, so that we can wander around our objects. This introduces some dynamics inside our category, which allows us to talk about movement and evolution of systems.

In practice, we need to describe, for any pair of objects $a$ and $b$, the collection of \emph{arrows} (also called \emph{morphisms}) going from $a$ to $b$. An arrow from $a$ to $b$ is sometimes mathematically denoted as $f:a \to b$ or more compactly as $a \xrightarrow{f} b$.
Moreover, if we denote a category as $\mathcal{C}$, a convenient notation to denote \emph{all} the arrows from object $a$ to object $b$ is $\mathcal{C}(a,b)$.

To translate this to Idris, let's add another field to our Category:
%
%
<   mor : obj -> obj -> Type
%
Now, for any pair of objects |a, b : obj|, we can talk about the collection |mor a b| of arrows going from $a$ to $b$. This faithfully models, on the implementation side, what $\mathcal{C}(a,b)$ is on the theoretical side.
%
%
%
\subsubsection{The operations}
%
%
Now that we have arrows in our category, allowing us to go from one object to the other, we would like to start following consecutive arrows; I mean, if an arrow leads us to $b$, we would like to continue our journey by taking any other arrow starting at $b$. Nobody stops us from doing that, but it would be really cumbersome if we must keep track of every single arrow whenever we want to describe a path from one dot to another. The definition of category comes in our help here, providing us with an operation to obtain arrows from paths, called \emph{composition}.
%
%
%
<   compose : (a, b, c : obj)
<          -> (f : mor a b)
<          -> (g : mor b c)
<          -> mor a c
Furthermore, the constructor |MkCategory| asks to determine:
%
<   identity : (a : obj) -> mor a a
%
Which for now is nothing more than a function that, for each object $a$, returns a morphism $a \to a$.
%
%
%
\subsubsection{The laws}
%
%
The part of the construction covered above defines the components of a category, but as they stand nothing ensures that the category axioms hold. For instance, there is nothing in principle that tells us that composing an identity with a morphism returns the morphism itself. This is the role of the remaining definition of the constructor |MkCategory|, ensuring that such axioms are enforced:
%
%
\begin{spec}
  leftIdentity  : (a, b : obj) -> (f : mor a b) -> compose a a b (identity a) f = f
  rightIdentity : (a, b : obj) -> (f : mor a b) -> compose a b b f (identity b) = f
  associativity : (a, b, c, d : obj)
                -> (f : mor a b)
                -> (g : mor b c)
                -> (h : mor c d)
                -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h
\end{spec}
%
These lines are a bit different in concept: They eat type, but produce \emph{equations}, effectively imposing further constraints on the components we defined before. Let's review them in detail.
%
%
\begin{itemize}
  \item |leftIdentity| takes a couple of objects (specified as |a,b: obj|) and a morphism between them (specified as |f: mor a b|) and produces an equation proving that composing the morphism on the left with the identity on its domain amounts to doing nothing. This is akin to the commutativity of the familiar diagram:
  %
  %
  \begin{center}
  \begin{tikzcd}
    a \arrow[d,equal]\arrow[dr, "f"]\\
    a \arrow[r, "f"']& b\\
  \end{tikzcd}
  \captionof{figure}{The equation $id_a ; f=f$}
  \end{center}

  \item Right identity law is defined analogously by |rightIdentity|, modelling the commutative diagram:
  %
  %
  \begin{center}
  \begin{tikzcd}
    a \arrow[r,"f"]\arrow[dr, "f"'] & b\arrow[d,equal]\\
    & b\\
  \end{tikzcd}
  \captionof{figure}{The identity laws $id_a ; f=f$ and $f;id_b = f$}
  \end{center}
  %
  In Idris, we can state the two identity laws as follows:
  %
  %
<   leftIdentity  : (a, b : obj)
<                -> (f : mor a b)
<                -> compose a a b (identity a) f = f
  %
  and
  %
  %
<   rightIdentity : (a, b : obj)
<                -> (f : mor a b)
<                -> compose a b b f (identity b) = f
  %
  In short, this amounts to say that |(identity a) ; f = f = f ; (identity b)| for any morphism |f : a -> b|. As a technical side note, I'd like to emphasise here how Idris allows us to encode equality in the type system; from a practial point of view, equality in Idris is a type which has only one inhabitant, called |Refl|, which corresponding to reflexivity, and stating that |x = x| for any possible |x|.

  \item Finally, the line
<   associativity : (a, b, c, d : obj)
<                -> (f : mor a b)
<                -> (g : mor b c)
<                -> (h : mor c d)
<                -> compose a b d f (compose b c d g h)
<                = compose a c d (compose a b c f g) h
  Imposes the familiar associativity law. It takes four objects and three morphisms between them, and produces an equation stating that the order of composition does not matter. This effectively models the commutative diagram:
  %
  %
  \begin{center}
  \begin{tikzcd}
    a \arrow[r, "f"]\arrow[dr,"f;g"']&b\arrow[d, "g"]\arrow[dr, "g;h"]&\\
    &c\arrow[r, "h"']& d\\
  \end{tikzcd}
  \captionof{figure}{The associativity law $f;(g;h)=(f;g);h$}
  \end{center}
\end{itemize}
%
%
%
\subsubsection{Conclusion}
%
%
Summing up and putting it all together, our definition of |Category| now looks like this:
%
%

> module Basic.Category
>
> %access public export
> %default total
>
> record Category where
>   constructor MkCategory
>   obj           : Type
>   mor           : obj -> obj -> Type
>   identity      : (a : obj) -> mor a a
>   compose       : (a, b, c : obj)
>                -> (f : mor a b)
>                -> (g : mor b c)
>                -> mor a c
>   leftIdentity  : (a, b : obj)
>                -> (f : mor a b)
>                -> compose a a b (identity a) f = f
>   rightIdentity : (a, b : obj)
>                -> (f : mor a b)
>                -> compose a b b f (identity b) = f
>   associativity : (a, b, c, d : obj)
>                -> (f : mor a b)
>                -> (g : mor b c)
>                -> (h : mor c d)
>                -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h
