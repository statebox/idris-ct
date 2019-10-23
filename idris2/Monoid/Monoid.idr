module Monoid.Monoid

import Utils

public export
record Monoid where
  constructor MkMonoid
  set    : Type
  axioms : VerifiedMonoid set

public export
buildMonoid : {m : Type} -> (vm : VerifiedMonoid m) => Monoid
buildMonoid @{vm} = MkMonoid m vm

public export
verifiedMonoidToSemigroup : VerifiedMonoid m => Semigroup m
verifiedMonoidToSemigroup = %search

public export
verifiedMonoidToVerifiedSemigroup : VerifiedMonoid m => VerifiedSemigroup m
verifiedMonoidToVerifiedSemigroup = %search

public export
verifiedMonoidToMonoid : VerifiedMonoid m => Monoid m
verifiedMonoidToMonoid = %search