module Basic.Isomorphism

import Basic.Category
import Utils

public export
LeftInverse : {cat : Category} -> {a, b : obj cat} -> mor cat a b -> mor cat b a -> Type
LeftInverse {cat} {a} {b} morphism inverse = compose cat a b a morphism inverse = identity cat a

public export
RightInverse : {cat : Category} -> {a, b : obj cat} -> mor cat a b -> mor cat b a -> Type
RightInverse {cat} {a} {b} morphism inverse = compose cat b a b inverse morphism = identity cat b

public export
record InverseMorphisms (cat : Category)
                        (a : obj cat)
                        (b : obj cat)
                        (morphism : mor cat a b)
                        (inverse : mor cat b a)
  where
    constructor MkInverseMorphisms
    lawLeft  : LeftInverse  {cat} {a} {b} morphism inverse
    lawRight : RightInverse {cat} {a} {b} morphism inverse

public export
record Isomorphism (cat : Category) (a : obj cat) (b : obj cat) (morphism : mor cat a b) where
  constructor MkIsomorphism
  inverse : mor cat b a
  inverseMorphisms : InverseMorphisms cat a b morphism inverse

public export
buildIsomorphism :
     {cat : Category}
  -> {a, b : obj cat}
  -> (morphism : mor cat a b)
  -> (inverse : mor cat b a)
  -> LeftInverse {cat} {a} {b} morphism inverse
  -> RightInverse {cat} {a} {b} morphism inverse
  -> Isomorphism cat a b morphism
buildIsomorphism {cat} {a} {b} morphism inverse leftInverse rightInverse = MkIsomorphism
  inverse
  (MkInverseMorphisms leftInverse rightInverse)

public export
record Isomorphic (cat : Category) (a : obj cat) (b : obj cat) where
  constructor MkIsomorphic
  morphism : mor cat a b
  isomorphism : Isomorphism cat a b morphism

public export
buildIsomorphic :
     {cat : Category}
  -> {a, b : obj cat}
  -> (morphism : mor cat a b)
  -> (inverse : mor cat b a)
  -> LeftInverse {cat} {a} {b} morphism inverse
  -> RightInverse {cat} {a} {b} morphism inverse
  -> Isomorphic cat a b
buildIsomorphic {cat} {a} {b} morphism inverse leftInverse rightInverse = MkIsomorphic
  morphism
  (buildIsomorphism morphism inverse leftInverse rightInverse)

public export
isomorphicEq :
     {cat : Category}
  -> {a, b : obj cat}
  -> (iso1, iso2 : Isomorphic cat a b)
  -> (morphism iso1 = morphism iso2)
  -> (inverse (isomorphism iso1) = inverse (isomorphism iso2))
  -> iso1 = iso2
isomorphicEq _ _ _ _ = believe_me ()

public export
idIsomorphic : {cat : Category} -> (a : obj cat) -> Isomorphic cat a a
idIsomorphic {cat} a = buildIsomorphic
  (identity cat a)
  (identity cat a)
  (leftIdentity cat a a (identity cat a))
  (leftIdentity cat a a (identity cat a))

public export
isomorphicComposition :
     {cat : Category}
  -> (a, b, c : obj cat)
  -> Isomorphic cat a b
  -> Isomorphic cat b c
  -> Isomorphic cat a c
isomorphicComposition {cat} a b c iso1 iso2 = buildIsomorphic
  (compose cat a b c (morphism iso1) (morphism iso2))
  (compose cat c b a (inverse $ isomorphism iso2) (inverse $ isomorphism iso1))
  (trans (associativity cat a c b a _ (inverse $ isomorphism iso2) (inverse $ isomorphism iso1))
         (trans (cong (\x => compose cat a b a x (inverse (isomorphism iso1)))
                      (trans (sym (associativity cat a b c b (morphism iso1) (morphism iso2) (inverse $ isomorphism iso2)))
                             (trans (cong (compose cat a b b (morphism iso1)) (lawLeft $ inverseMorphisms $ isomorphism iso2))
                                    (rightIdentity cat a b (morphism iso1)))))
                (lawLeft $ inverseMorphisms $ isomorphism iso1)))
  (trans (associativity cat c a b c _ (morphism iso1) (morphism iso2))
         (trans (cong (\x => compose cat c b c x (morphism iso2))
                      (trans (sym (associativity cat c b a b (inverse $ isomorphism iso2) (inverse $ isomorphism iso1) (morphism iso1)))
                             (trans (cong (compose cat c b b (inverse $ isomorphism iso2)) (lawRight $ inverseMorphisms $ isomorphism iso1))
                                    (rightIdentity cat c b (inverse $ isomorphism iso2)))))
                (lawRight $ inverseMorphisms $ isomorphism iso2)))

public export
isomorphicCategory : (cat : Category) -> Category
isomorphicCategory cat = MkCategory
  (obj cat)
  (Isomorphic cat)
  idIsomorphic
  isomorphicComposition
  (\a, b, iso => isomorphicEq (isomorphicComposition a a b (idIsomorphic a) iso) iso
    (leftIdentity cat a b (morphism iso))
    (rightIdentity cat b a (inverse $ isomorphism iso)))
  (\a, b, iso => isomorphicEq (isomorphicComposition a b b iso (idIsomorphic b)) iso
    (rightIdentity cat a b (morphism iso))
    (leftIdentity cat b a (inverse $ isomorphism iso)))
  (\a, b, c, d, iso1, iso2, iso3 => isomorphicEq
    (isomorphicComposition a b d iso1 (isomorphicComposition b c d iso2 iso3))
    (isomorphicComposition a c d (isomorphicComposition a b c iso1 iso2) iso3)
    (associativity cat a b c d (morphism iso1) (morphism iso2) (morphism iso3))
    (sym (associativity cat d c b a (inverse $ isomorphism iso3) (inverse $ isomorphism iso2) (inverse $ isomorphism iso1))))
