module Monad.Monad

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation
import Cats.CatsAsCategory
import Cats.FunctorsAsCategory

public export
eqNatTrans :
     {cat1, cat2 : Category}
  -> (func1, func2 : CFunctor cat1 cat2)
  -> (func1 = func2)
  -> NaturalTransformation cat1 cat2 func1 func2
eqNatTrans func1 func1 Refl = idTransformation cat1 cat2 func1

public export
MonadAssociativity :
     {cat : Category}
  -> (functor : CFunctor cat cat)
  -> (multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor)
  -> Type
MonadAssociativity {cat} functor multiplication =
  naturalTransformationComposition cat cat
                                   (functorComposition cat cat cat
                                                       (functorComposition cat cat cat functor functor)
                                                       functor)
                                   (functorComposition cat cat cat functor functor)
                                   functor
                                   (composeFunctorNatTrans multiplication functor)
                                   multiplication
  = naturalTransformationComposition cat cat
                                     (functorComposition cat cat cat
                                                         (functorComposition cat cat cat functor functor)
                                                         functor)
                                     (functorComposition cat cat cat
                                                         functor
                                                         (functorComposition cat cat cat functor functor))
                                     functor
                                     (eqNatTrans (functorComposition cat cat cat
                                                                     (functorComposition cat cat cat functor functor)
                                                                     functor)
                                                 (functorComposition cat cat cat
                                                                     functor
                                                                     (functorComposition cat cat cat functor functor))
                                                 (sym $ catsAssociativity cat cat cat cat functor functor functor))
                                     (naturalTransformationComposition cat cat
                                                                          (functorComposition cat cat cat
                                                                                              functor
                                                                                              (functorComposition cat cat cat functor functor))
                                                                          (functorComposition cat cat cat functor functor)
                                                                          functor
                                                                          (composeNatTransFunctor functor multiplication)
                                                                          multiplication)

public export
MonadLeftUnit :
     {cat : Category}
  -> (functor : CFunctor cat cat)
  -> (unit : NaturalTransformation _ _ (idFunctor cat) functor)
  -> (multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor)
  -> Type
MonadLeftUnit {cat} functor unit multiplication =
  naturalTransformationComposition cat cat
                                   functor
                                   (functorComposition cat cat cat functor functor)
                                   functor
                                   (replace {p = \x => NaturalTransformation cat cat x (functorComposition cat cat cat functor functor)}
                                            (catsRightIdentity cat cat functor)
                                            (composeNatTransFunctor functor unit))
                                   multiplication
  = idTransformation cat cat functor

public export
MonadRightUnit :
     {cat : Category}
  -> (functor : CFunctor cat cat)
  -> (unit : NaturalTransformation _ _ (idFunctor cat) functor)
  -> (multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor)
  -> Type
MonadRightUnit {cat} functor unit multiplication =
  naturalTransformationComposition cat cat
                                   functor
                                   (functorComposition cat cat cat functor functor)
                                   functor
                                   (replace {p = \x => NaturalTransformation cat cat x (functorComposition cat cat cat functor functor)}
                                            (catsLeftIdentity cat cat functor)
                                            (composeFunctorNatTrans unit functor))
                                            multiplication
  = idTransformation cat cat functor

-- we are not using a record here because compilation does not terminate in that case
public export
data Monad : (cat : Category) -> Type where
  MkMonad :
       {cat : Category}
    -> (functor : CFunctor cat cat)
    -> (unit : NaturalTransformation _ _ (idFunctor cat) functor)
    -> (multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor)
    -> (associativity : MonadAssociativity {cat} functor multiplication)
    -> (leftUnit : MonadLeftUnit functor unit multiplication)
    -> (rightUnit : MonadRightUnit functor unit multiplication)
    -> Monad cat

public export
functor : {cat : Category} -> Monad cat -> CFunctor cat cat
functor {cat} (MkMonad func _ _ _ _ _) = func

public export
unit : {cat : Category} -> (m : Monad cat) -> NaturalTransformation cat cat (idFunctor cat) (functor m)
unit (MkMonad _ u _ _ _ _) = u

public export
multiplication :
     {cat : Category}
  -> (m : Monad cat)
  -> NaturalTransformation cat cat (functorComposition cat cat cat (functor m) (functor m)) (functor m)
multiplication (MkMonad _ _ mult _ _ _) = mult

public export
associativity :
     {cat : Category}
  -> (m : Monad cat)
  -> MonadAssociativity (functor m) (multiplication m)
associativity (MkMonad _ _ _ assoc _ _) = assoc

public export
leftUnit :
     {cat : Category}
  -> (m : Monad cat)
  -> MonadLeftUnit (functor m) (unit m) (multiplication m)
leftUnit (MkMonad _ _ _ _ lUnit _) = lUnit

public export
rightUnit :
     {cat : Category}
  -> (m : Monad cat)
  -> MonadRightUnit (functor m) (unit m) (multiplication m)
rightUnit (MkMonad _ _ _ _ _ rUnit) = rUnit
