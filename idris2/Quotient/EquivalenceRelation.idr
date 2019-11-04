module Quotient.EquivalenceRelation

public export
Relation : Type -> Type
Relation t = t -> t -> Type

public export
record EquivalenceRelation (t : Type) where
  constructor MkEquivalenceRelation
  rel          : Relation t
  reflexivity  : (a : t) -> rel a a
  symmetry     : (a, b : t) -> rel a b -> rel b a
  transitivity : (a, b, c : t) -> rel a b -> rel b c -> rel a c

parameters (rel : Relation t)
  public export
  data EquivalenceClosure : Relation t where
    ClosureIncl  : rel a b -> EquivalenceClosure a b
    ClosureRefl  : EquivalenceClosure a a
    ClosureSym   : EquivalenceClosure a b -> EquivalenceClosure b a
    ClosureTrans : EquivalenceClosure a b -> EquivalenceClosure b c -> EquivalenceClosure a c

public export
equivalenceClosure : Relation t -> EquivalenceRelation t
equivalenceClosure r = MkEquivalenceRelation
  (EquivalenceClosure r)
  (\_ => ClosureRefl r)
  (\_, _ => ClosureSym r)
  (\_, _, _ => ClosureTrans r)
