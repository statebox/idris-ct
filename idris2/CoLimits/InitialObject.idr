module CoLimits.InitialObject

import Basic.Category
import Basic.Isomorphism

public export
record InitialObject (cat : Category) where
  constructor MkInitialObject
  carrier : obj cat
  exists  : (b : obj cat) -> mor cat carrier b
  unique  : (b : obj cat) -> (f, g : mor cat carrier b) -> f = g

public export
composeInitialMorphisms :
     (cat : Category)
  -> (a, b : InitialObject cat)
  -> mor cat (carrier a) (carrier a)
composeInitialMorphisms cat a b =
  compose cat x y x (exists a y) (exists b x)
  where
  x : obj cat
  x = carrier a
  y : obj cat
  y = carrier b

public export
initialObjectsAreIsomorphic :
     (cat : Category)
  -> (a, b : InitialObject cat)
  -> Isomorphic cat (carrier a) (carrier b)
initialObjectsAreIsomorphic cat a b = buildIsomorphic
  (exists a (carrier b))
  (exists b (carrier a))
  (unique a (carrier a) (composeInitialMorphisms cat a b) (identity cat (carrier a)))
  (unique b (carrier b) (composeInitialMorphisms cat b a) (identity cat (carrier b)))