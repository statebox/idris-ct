module Preorder.PreorderAsCategory

import Basic.Category
import Preorder.UniquePreorder

public export
leftIdentity : UniquePreorder t po
  => (a, b : t)
  -> (f : po a b)
  -> transitive {po} a a b (reflexive {po} a) f = f
leftIdentity a b f = unique a b (transitive a a b (reflexive a) f) f

public export
rightIdentity : UniquePreorder t po
  => (a, b : t)
  -> (f : po a b)
  -> transitive {po} a b b f (reflexive {po} b) = f
rightIdentity a b f = unique a b (transitive a b b f (reflexive b)) f

public export
associativity : UniquePreorder t po
  => (a, b, c, d : t)
  -> (f : po a b)
  -> (g : po b c)
  -> (h : po c d)
  -> transitive {po} a b d f (transitive {po} b c d g h) = transitive {po} a c d (transitive {po} a b c f g) h
associativity a b c d f g h =
  unique a d
  (transitive a b d f (transitive b c d g h))
  (transitive a c d (transitive a b c f g) h)

public export
preorderAsCategory : {t : Type} -> {po : t -> t -> Type} ->
                     UniquePreorder t po => Category
preorderAsCategory = MkCategory
  t
  po
  reflexive
  transitive
  leftIdentity
  rightIdentity
  associativity
