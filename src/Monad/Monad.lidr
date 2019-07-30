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

> module Monad.Monad
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
>
> %access public export
> %default total
> %auto_implicits off
>
> eqNatTrans :
>      {cat1, cat2 : Category}
>   -> (func1, func2 : CFunctor cat1 cat2)
>   -> (func1 = func2)
>   -> NaturalTransformation cat1 cat2 func1 func2
> eqNatTrans func1 func1 Refl = idTransformation cat1 cat2 func1
>
> MonadAssociativity :
>      {cat : Category}
>   -> (functor : CFunctor cat cat)
>   -> (multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor)
>   -> Type
> MonadAssociativity {cat} functor multiplication =
>   naturalTransformationComposition cat cat
>                                    (functorComposition cat cat cat
>                                                        (functorComposition cat cat cat functor functor)
>                                                        functor)
>                                    (functorComposition cat cat cat functor functor)
>                                    functor
>                                    (composeFunctorNatTrans cat cat cat
>                                                            (functorComposition cat cat cat functor functor)
>                                                            functor
>                                                            multiplication
>                                                            functor)
>                                    multiplication
>   = naturalTransformationComposition cat cat
>                                      (functorComposition cat cat cat
>                                                          (functorComposition cat cat cat functor functor)
>                                                          functor)
>                                      (functorComposition cat cat cat
>                                                          functor
>                                                          (functorComposition cat cat cat functor functor))
>                                      functor
>                                      (eqNatTrans (functorComposition cat cat cat
>                                                                      (functorComposition cat cat cat functor functor)
>                                                                      functor)
>                                                  (functorComposition cat cat cat
>                                                                      functor
>                                                                      (functorComposition cat cat cat functor functor))
>                                                  (sym $ catsAssociativity cat cat cat cat functor functor functor))
>                                      (naturalTransformationComposition cat cat
>                                                                           (functorComposition cat cat cat
>                                                                                               functor
>                                                                                               (functorComposition cat cat cat functor functor))
>                                                                           (functorComposition cat cat cat functor functor)
>                                                                           functor
>                                                                           (composeNatTransFunctor cat cat cat
>                                                                                                   functor
>                                                                                                   (functorComposition cat cat cat functor functor)
>                                                                                                   functor
>                                                                                                   multiplication)
>                                                                           multiplication)
>
> -- we are not using a record here because compilation does not terminate in that case
> data Monad : (cat : Category) -> Type where
>   MkMonad :
>        {cat : Category}
>     -> (functor : CFunctor cat cat)
>     -> (unit : NaturalTransformation _ _ (idFunctor cat) functor)
>     -> (multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor)
>     -> (associativity : MonadAssociativity {cat} functor multiplication)
>     -> (leftUnit : naturalTransformationComposition cat cat
>                                                     functor
>                                                     (functorComposition cat cat cat functor functor)
>                                                     functor
>                                                     (replace {P = \x => NaturalTransformation cat cat x (functorComposition cat cat cat functor functor)}
>                                                              (catsRightIdentity cat cat functor)
>                                                              (composeNatTransFunctor cat cat cat
>                                                                                      functor
>                                                                                      (idFunctor cat)
>                                                                                      functor
>                                                                                      unit))
>                                                     multiplication
>                  = idTransformation cat cat functor)
>     -> (rightUnit : naturalTransformationComposition cat cat
>                                                      functor
>                                                      (functorComposition cat cat cat functor functor)
>                                                      functor
>                                                      (replace {P = \x => NaturalTransformation cat cat x (functorComposition cat cat cat functor functor)}
>                                                               (catsLeftIdentity cat cat functor)
>                                                               (composeFunctorNatTrans cat cat cat
>                                                                                       (idFunctor cat)
>                                                                                       functor
>                                                                                       unit
>                                                                                       functor))
>                                                      multiplication
>                   = idTransformation cat cat functor)
>     -> Monad cat
>
> functor : {cat : Category} -> Monad cat -> CFunctor cat cat
> functor {cat} (MkMonad func _ _ _ _ _) = func
>
> unit : {cat : Category} -> (m : Monad cat) -> NaturalTransformation cat cat (idFunctor cat) (functor m)
> unit (MkMonad _ u _ _ _ _) = u
>
> multiplication :
>      {cat : Category}
>   -> (m : Monad cat)
>   -> NaturalTransformation cat cat (functorComposition cat cat cat (functor m) (functor m)) (functor m)
> multiplication (MkMonad _ _ mult _ _ _) = mult
>
> associativity :
>      {cat : Category}
>   -> (m : Monad cat)
>   -> MonadAssociativity (functor m) (multiplication m)
> associativity (MkMonad _ _ _ assoc _ _) = assoc
>
> leftUnit :
>      {cat : Category}
>   -> (m : Monad cat)
>   -> naturalTransformationComposition cat cat
>                                       (functor m)
>                                       (functorComposition cat cat cat (functor m) (functor m))
>                                       (functor m)
>                                       (replace {P = \x => NaturalTransformation cat cat x (functorComposition cat cat cat (functor m) (functor m))}
>                                                (catsRightIdentity cat cat (functor m))
>                                                (composeNatTransFunctor cat cat cat
>                                                                        (functor m)
>                                                                        (idFunctor cat)
>                                                                        (functor m)
>                                                                        (unit m)))
>                                       (multiplication m)
>    = idTransformation cat cat (functor m)
> leftUnit (MkMonad _ _ _ _ lUnit _) = lUnit
>
> rightUnit :
>      {cat : Category}
>   -> (m : Monad cat)
>   -> naturalTransformationComposition cat cat
>                                       (functor m)
>                                       (functorComposition cat cat cat (functor m) (functor m))
>                                       (functor m)
>                                       (replace {P = \x => NaturalTransformation cat cat x (functorComposition cat cat cat (functor m) (functor m))}
>                                                (catsLeftIdentity cat cat (functor m))
>                                                (composeFunctorNatTrans cat cat cat
>                                                                        (idFunctor cat)
>                                                                        (functor m)
>                                                                        (unit m)
>                                                                        (functor m)))
>                                       (multiplication m)
>    = idTransformation cat cat (functor m)
> rightUnit (MkMonad _ _ _ _ _ rUnit) = rUnit
