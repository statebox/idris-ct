module Utils

public export
cong2 : (f : t -> u -> v) -> a = b -> c = d -> f a c = f b d
cong2 f Refl Refl = Refl

public export
swap : (a, b) -> (b, a)
swap (x, y) = (y, x)

public export
interface Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : {0 a : Type} -> (g : a -> a) -> ((v : a) -> g v = v) -> (x : f a) -> map g x = x
  functorComposition : {0 a, b : Type} -> (x : f a) ->
                       (g1 : a -> b) -> (g2 : b -> c) ->
                       map (g2 . g1) x = (map g2 . map g1) x

public export
functorIdentity' : VerifiedFunctor f => (x : f a) -> map Prelude.id x = x
functorIdentity' = functorIdentity id (\x => Refl)

public export
interface Semigroup a => VerifiedSemigroup a where
  semigroupOpIsAssociative : (l, c, r : a) -> l <+> (c <+> r) = (l <+> c) <+> r

public export
interface (VerifiedSemigroup a, Monoid a) => VerifiedMonoid a where
  monoidNeutralIsNeutralL : (l : a) -> l <+> Prelude.neutral = l
  monoidNeutralIsNeutralR : (r : a) -> Prelude.neutral <+> r = r

-- TODO: we couldn't find a proof for this, so we postulate it for the moment
public export
dPairEq : {x, y : DPair a b}
       -> DPair.fst x ~=~ DPair.fst y
       -> DPair.snd x ~=~ DPair.snd y
       -> x ~=~ y
dPairEq {x=MkDPair u v} {y=MkDPair _ _} Refl prf = believe_me ()

public export
pairEq : {x, y : (a, b)}
      -> fst x ~=~ fst y
      -> snd x ~=~ snd y
      -> x ~=~ y
pairEq {x=(u, v)} {y=(_, _)} Refl Refl = Refl
