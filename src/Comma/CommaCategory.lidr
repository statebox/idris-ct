\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2020 Stichting Statebox <https://statebox.nl>

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

> module Comma.CommaCategory
>
> import Basic.Category
> import Basic.Functor
> import Utils
>
> %access public export
> %default total
> %auto_implicits off

We define \emph{Comma categories}: given a diagram
  $F_1:C_1\rightarrow C\leftarrow C_2:F_2$
of categories and functors, we can define the comma category
  $F_1\downarrow F_2$.
An object consists of a triple $(x,y,f)$ where $x$ is an object of $C_1$, $y$ an object of
$C_2$, and $f:F_1(x)\rightarrow F_2(y)$ a morphism of $C$.

> record CommaObject
>   (cat  : Category)
>   (cat1 : Category)
>   (cat2 : Category)
>   (fun1 : CFunctor cat1 cat)
>   (fun2 : CFunctor cat2 cat)
>   where
>     constructor MkCommaObject
>     comObj1 : obj cat1
>     comObj2 : obj cat2
>     comMor  : mor cat (mapObj fun1 comObj1) (mapObj fun2 comObj2)

A morphism in $F_1\downarrow F_2$ from $(x,y,f)$ to $(x',y',f')$ consists of a pair of morphisms $(h,k)$
where $h:x\rightarrow x'$ is a morphism of $C_1$ and $k:y\rightarrow y'$ is a morphism of $C_2$ such that $f;F_2(k) = F_1(h);f'$.

> record CommaMorphism
>   (cat  : Category)
>   (cat1 : Category)
>   (cat2 : Category)
>   (fun1 : CFunctor cat1 cat)
>   (fun2 : CFunctor cat2 cat)
>   (x : CommaObject cat cat1 cat2 fun1 fun2)
>   (y : CommaObject cat cat1 cat2 fun1 fun2)
>   where
>     constructor MkCommaMorphism
>     comMor1 : mor cat1 (comObj1 x) (comObj1 y)
>     comMor2 : mor cat2 (comObj2 x) (comObj2 y)
>     comSq : compose cat (mapObj fun1 (comObj1 x))
>                         (mapObj fun1 (comObj1 y))
>                         (mapObj fun2 (comObj2 y))
>                         (mapMor fun1 _ _ comMor1)
>                         (comMor y)
>           = compose cat (mapObj fun1 (comObj1 x))
>                         (mapObj fun2 (comObj2 x))
>                         (mapObj fun2 (comObj2 y))
>                         (comMor x)
>                         (mapMor fun2 _ _ comMor2)
>
> commaMorphismsEqual :
>       {cat, cat1, cat2 : Category}
>    -> {fun1 : CFunctor cat1 cat}
>    -> {fun2 : CFunctor cat2 cat}
>    -> {x, y : CommaObject cat cat1 cat2 fun1 fun2}
>    -> (u, v : CommaMorphism cat cat1 cat2 fun1 fun2 x y)
>    -> comMor1 u = comMor1 v
>    -> comMor2 u = comMor2 v
>    -> u = v
> commaMorphismsEqual (MkCommaMorphism u1 u2 s) (MkCommaMorphism u1 u2 t) Refl Refl =
>   cong {f = MkCommaMorphism u1 u2} (equalitiesEqual _ _)
>
> commaIdentity :
>        {cat, cat1, cat2 : Category}
>     -> {fun1 : CFunctor cat1 cat}
>     -> {fun2 : CFunctor cat2 cat}
>     -> (x : CommaObject cat cat1 cat2 fun1 fun2)
>     -> CommaMorphism cat cat1 cat2 fun1 fun2 x x
> commaIdentity {cat} {cat1} {cat2} {fun1} {fun2} x = MkCommaMorphism
>   (identity cat1 (comObj1 x))
>   (identity cat2 (comObj2 x))
>   (trans (trans (cong2 {f = compose cat _ _ _} (preserveId fun1 (comObj1 x)) Refl)
>                 (leftIdentity cat _ _ (comMor x)))
>          (sym (trans (cong {f = compose cat _ _ _ _} (preserveId fun2 (comObj2 x)))
>                      (rightIdentity cat _ _ (comMor x)))))

The diagram chase below is as follows:

\begin{align*}
 & F_1(u_1; v_1); h
=& (F_1(u_1); F_1(v_1)); h
=& F_1(u_1) ; (F_1(v_1); h)
=& F_1(u_1) ; (g; F_2(v_2))
=& (F_1(u_1); g); F_2(v_2)
=& (f; F_2(u_2)); F_2(v_2)
=& f; (F_2(u_2) ; F_2(v_2))
=& f; F_2(u_2; v_2)
\end{align*}

> commaCompose :
>      {cat, cat1, cat2 : Category}
>   -> {fun1 : CFunctor cat1 cat}
>   -> {fun2 : CFunctor cat2 cat}
>   -> (x, y, z : CommaObject cat cat1 cat2 fun1 fun2)
>   -> (u : CommaMorphism cat cat1 cat2 fun1 fun2 x y)
>   -> (v : CommaMorphism cat cat1 cat2 fun1 fun2 y z)
>   -> CommaMorphism cat cat1 cat2 fun1 fun2 x z
> commaCompose {cat} {cat1} {cat2} {fun1} {fun2} x y z u v = MkCommaMorphism
>   (compose cat1 (comObj1 x) (comObj1 y) (comObj1 z) (comMor1 u) (comMor1 v))
>   (compose cat2 (comObj2 x) (comObj2 y) (comObj2 z) (comMor2 u) (comMor2 v))
>   (trans7
>     (cong2 {f = compose cat _ _ _} (preserveCompose fun1 _ _ _ (comMor1 u) (comMor1 v)) Refl)
>     (sym (associativity cat _ _ _ _ (mapMor fun1 _ _ (comMor1 u)) (mapMor fun1 _ _ (comMor1 v)) (comMor z)))
>     (cong {f = compose cat _ _ _ _} (comSq v))
>     (associativity cat _ _ _ _ _ _ _)
>     (cong2 {f = compose cat _ _ _} (comSq u) Refl)
>     (sym (associativity cat _ _ _ _ _ _ _))
>     (sym (cong {f = compose cat _ _ _ _} (preserveCompose fun2 _ _ _(comMor2 u) (comMor2 v)))))
>
> commaLeftIdentity :
>      {cat, cat1, cat2 : Category}
>   -> {fun1 : CFunctor cat1 cat}
>   -> {fun2 : CFunctor cat2 cat}
>   -> (x, y : CommaObject cat cat1 cat2 fun1 fun2)
>   -> (u : CommaMorphism cat cat1 cat2 fun1 fun2 x y)
>   -> commaCompose x x y (commaIdentity x) u = u
> commaLeftIdentity {cat} {cat1} {cat2} {fun1} {fun2} x y u =
>   commaMorphismsEqual _ _ (leftIdentity cat1 _ _ (comMor1 u)) (leftIdentity cat2 _ _ (comMor2 u))
>
> commaRightIdentity :
>      {cat, cat1, cat2 : Category}
>   -> {fun1 : CFunctor cat1 cat}
>   -> {fun2 : CFunctor cat2 cat}
>   -> (x, y : CommaObject cat cat1 cat2 fun1 fun2)
>   -> (u : CommaMorphism cat cat1 cat2 fun1 fun2 x y)
>   -> commaCompose x y y u (commaIdentity y) = u
> commaRightIdentity {cat} {cat1} {cat2} {fun1} {fun2} x y u =
>   commaMorphismsEqual _ _ (rightIdentity cat1 _ _ (comMor1 u)) (rightIdentity cat2 _ _ (comMor2 u))
>
> commaAssociativity :
>      {cat, cat1, cat2 : Category}
>   -> {fun1 : CFunctor cat1 cat}
>   -> {fun2 : CFunctor cat2 cat}
>   -> (w, x, y, z : CommaObject cat cat1 cat2 fun1 fun2)
>   -> (f : CommaMorphism cat cat1 cat2 fun1 fun2 w x)
>   -> (g : CommaMorphism cat cat1 cat2 fun1 fun2 x y)
>   -> (h : CommaMorphism cat cat1 cat2 fun1 fun2 y z)
>   -> commaCompose _ _ _ f (commaCompose _ _ _ g h)
>    = commaCompose _ _ _ (commaCompose _ _ _ f g) h
> commaAssociativity {cat} {cat1} {cat2} {fun1} {fun2} w x y z f g h =
>   commaMorphismsEqual _ _ (associativity cat1 _ _ _ _ (comMor1 f) (comMor1 g) (comMor1 h))
>                           (associativity cat2 _ _ _ _ (comMor2 f) (comMor2 g) (comMor2 h))
>
> commaCategory :
>      {cat, cat1, cat2 : Category}
>   -> (fun1 : CFunctor cat1 cat)
>   -> (fun2 : CFunctor cat2 cat)
>   -> Category
> commaCategory {cat} {cat1} {cat2} fun1 fun2 = MkCategory
>   (CommaObject cat cat1 cat2 fun1 fun2)
>   (CommaMorphism cat cat1 cat2 fun1 fun2)
>   commaIdentity
>   commaCompose
>   commaLeftIdentity
>   commaRightIdentity
>   commaAssociativity
