module FSMC where

open import Level

open import Data.Nat as N
open import Data.List as L
open import Data.Vec as V
open import Data.Fin
open import Data.Fin.Permutation as Perm
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum as S

open import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

open import Data.Nat.Properties using (≤-trans; ≰⇒>; 1+n≰n; m≤m+n)
open import Data.Fin.Properties using (toℕ-inject+; toℕ-raise; fromℕ≤-toℕ; toℕ<n)
open import Data.Sum.Properties using (swap-involutive)
open import Data.Vec.Properties using (lookup-++ˡ; lookup-++ʳ; lookup-++-<; lookup-++-≥)

open import Function
open import Function.Inverse
open import Function.Equality

open import Axiom.Extensionality.Propositional as Ext
open import Axiom.UniquenessOfIdentityProofs.WithK as UIP

----- Function extensionality

postulate
  ext : Ext.Extensionality Level.zero Level.zero

impext : {A : Set} {B : A → Set} {f g : {x : A} → B x} →
         (∀ {x} → f {x} ≡ g {x}) →
         (λ {x} → f {x}) ≡ g
impext {f = f} {g} p = P.cong expToImp (ext (λ x → p {x}))
  where expToImp : ∀ {A}{B : A → Set} ->((x : A) -> B x) -> ({x : A} -> B x)
        expToImp f {x} = f x

------ Misc permutation stuff

-- A bijection between `Fin n ⊎ Fin` and `Fin (n + m)`
mergeFin : (n m : ℕ) -> Fin n ⊎ Fin m -> Fin (n N.+ m)
mergeFin n m (inj₁ i) = inject+ m i
mergeFin n m (inj₂ j) = raise n j

partitionFin : (n m : ℕ) -> Fin (n N.+ m) -> Fin n ⊎ Fin m
partitionFin n m i with toℕ i N.<? n
... | yes p = inj₁ (fromℕ≤ p)
... | no ¬p = inj₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))

partition-from-to : ∀ n m x → partitionFin n m (mergeFin n m x) ≡ x
partition-from-to n m (inj₁ i) with (toℕ (inject+ m i)) N.<? n
... | yes p rewrite P.sym (toℕ-inject+ m i) = P.cong inj₁ (fromℕ≤-toℕ i p)
... | no ¬p = ⊥-elim (¬p i<n)
  where
    i<n : (toℕ (inject+ m i)) N.< n
    i<n rewrite P.sym (toℕ-inject+ m i) = toℕ<n i
partition-from-to n m (inj₂ j) with (toℕ (raise n j)) N.<? n
... | yes p = ⊥-elim (1+n≰n n<n)
  where
    n<n : n N.< n
    n<n rewrite toℕ-raise n j = ≤-trans (m≤m+n (N.suc n) (toℕ j)) p
... |  no ¬p = P.cong inj₂ (reduce-raise n (≤-pred (≰⇒> ¬p)))
  where
    reduce-raise : ∀ n {m} {j : Fin m}(p : (toℕ (raise n j)) N.≥ n) ->
               reduce≥ (raise n j) p ≡ j
    reduce-raise N.zero p = refl
    reduce-raise (N.suc n) (s≤s p) = reduce-raise n p

partition-to-from : ∀ n m y → mergeFin n m (partitionFin n m y) ≡ y
partition-to-from n m i with toℕ i N.<? n
... | yes p = inject+-fromℕ≤ i p
  where
    inject+-fromℕ≤ : ∀ {n m} (i : Fin (n N.+ m))(p : N.suc (toℕ i) N.≤ n) →
                     inject+ m (fromℕ≤ p) ≡ i
    inject+-fromℕ≤ {m = m} Fin.zero (s≤s z≤n) = refl
    inject+-fromℕ≤ {m = m} (Fin.suc i) (s≤s (s≤s p)) =
      P.cong Fin.suc (inject+-fromℕ≤ i (s≤s p))
... | no ¬p = raise-reduce n i (≤-pred (≰⇒> ¬p))
  where
    raise-reduce : ∀ n {m} (i : Fin (n N.+ m))
                   (p : toℕ i ≥ n) ->
                   raise n (reduce≥ i p) ≡ i
    raise-reduce N.zero i p = refl
    raise-reduce (N.suc n) (Fin.suc i) (s≤s p) =
      P.cong Fin.suc (raise-reduce n i  p)

-- Putting two permutations next to each other
_Perm++_ : {n m n' m' : ℕ} ->
             Permutation n m -> Permutation n' m' ->
             Permutation (n N.+ n') (m N.+ m')
_Perm++_ {n} {m} {n'} {m'} π τ = permutation to from
                                     (record { left-inverse-of = from-to
                                             ; right-inverse-of = to-from
                                             })
  where
    to = mergeFin m m' ∘′ S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_)) ∘′ partitionFin n n'

    from = mergeFin n n' ∘′ S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_)) ∘′ partitionFin m m'

    map-fuse-left : ∀ {n m n' m'}
                    (π : Permutation n m)(τ : Permutation n' m') x →
                    S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_)) (S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_)) x)
                       ≡ x
    map-fuse-left π τ (inj₁ x) = P.cong inj₁ (inverseˡ π)
    map-fuse-left π τ (inj₂ y) = P.cong inj₂ (inverseˡ τ)

    map-fuse-right : ∀ {n m n' m'}
                     (π : Permutation n m)(τ : Permutation n' m') x →
                     S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_)) (S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_)) x)
                       ≡ x
    map-fuse-right π τ (inj₁ x) = P.cong inj₁ (inverseʳ π)
    map-fuse-right π τ (inj₂ y) = P.cong inj₂ (inverseʳ τ)

    open ≡-Reasoning
    from-to : ∀ i → from (to i) ≡ i
    from-to i = begin
      (mergeFin n n' ∘′ S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_)) ∘′ partitionFin m m'
        ∘′ mergeFin m m' ∘′ S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_)) ∘′ partitionFin n n') i
        ≡⟨ P.cong (mergeFin n n' ∘′ S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_)))
                (partition-from-to m m' ((S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_))
                                           ∘′ partitionFin n n') i)) ⟩
      (mergeFin n n' ∘′ S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_))
        ∘′ S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_)) ∘′ partitionFin n n') i
        ≡⟨ P.cong (mergeFin n n') (map-fuse-left π τ (partitionFin n n' i)) ⟩
      (mergeFin n n' ∘′ partitionFin n n') i
        ≡⟨ partition-to-from n n' i ⟩
      i
        ∎
    to-from : ∀ i → to (from i) ≡ i
    to-from i = begin
      (mergeFin m m' ∘′ S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_)) ∘′ partitionFin n n'
        ∘′ mergeFin n n' ∘′ S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_)) ∘′ partitionFin m m') i
        ≡⟨ P.cong (mergeFin m m' ∘′ S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_)))
                (partition-from-to n n' ((S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_))
                                           ∘′ partitionFin m m') i)) ⟩
      (mergeFin m m' ∘′ S.map (π ⟨$⟩ʳ_) ((τ ⟨$⟩ʳ_))
        ∘′ S.map (π ⟨$⟩ˡ_) ((τ ⟨$⟩ˡ_)) ∘′ partitionFin m m') i
        ≡⟨ P.cong (mergeFin m m') (map-fuse-right π τ (partitionFin m m' i)) ⟩
      (mergeFin m m' ∘′ partitionFin m m') i
        ≡⟨ partition-to-from m m' i ⟩
      i
        ∎

-- A permutation swapping two blocks
swapBlock : (n m : ℕ) -> Permutation (n N.+ m) (m N.+ n)
swapBlock n m = permutation (swapPerm n m) (swapPerm m n)
                  (record { left-inverse-of =  swapInv n m
                          ; right-inverse-of = swapInv m n
                          })
  where
    swapPerm : ∀ n m → Fin (n N.+ m) → Fin (m N.+ n)
    swapPerm n m = mergeFin m n ∘′ S.swap ∘′ (partitionFin n m)

    swapInv : ∀ n m → (i : Fin (n N.+ m)) → swapPerm m n (swapPerm n m i) ≡ i
    swapInv n m i = begin
        mergeFin n m (S.swap (partitionFin m n
          (mergeFin m n (S.swap (partitionFin n m i)))))
      ≡⟨ P.cong (mergeFin n m ∘′ S.swap)
              (partition-from-to m n (S.swap (partitionFin n m i))) ⟩
        mergeFin n m (S.swap (S.swap (partitionFin n m i)))
      ≡⟨ P.cong (mergeFin n m) (swap-involutive (partitionFin n m i)) ⟩
        mergeFin n m (partitionFin n m i)
      ≡⟨ partition-to-from n m i ⟩
        i
      ∎
      where open ≡-Reasoning

-- looking up a swapped coordinate is the same as looking up in the
-- swapped table
lookup-swap : {A : Set}{n m : ℕ}(as : Vec A n)(bs : Vec A m) ->
              (i : Fin (n N.+ m)) ->
              V.lookup (bs V.++ as) (swapBlock n m ⟨$⟩ʳ i)
                ≡ V.lookup (as V.++ bs) i
lookup-swap [] bs i = lookup-++ˡ bs [] i
lookup-swap {n = N.suc n} as@(_ ∷ _) bs i with (toℕ i) N.<? N.suc n
... | yes p = trans (lookup-++ʳ bs as (fromℕ≤ p))
                    (P.sym (lookup-++-< as bs i p))
... | no ¬p = trans (lookup-++ˡ bs as (reduce≥ i (≰⇒> (¬p ∘′ s≤s))))
                    (P.sym (lookup-++-≥ as bs i (≰⇒> (¬p ∘′ s≤s))))

------ Def category

record Category : Set1 where
  field
    obj : Set
    mor : obj -> obj -> Set
    compose : {a b c : obj} -> mor a b -> mor b c -> mor a c
    identity : {a : obj} -> mor a a
    -- laws
    leftIdentity  : {a b : obj} -> (f : mor a b) -> compose identity f ≡ f
    rightIdentity : {a b : obj} -> (f : mor a b) -> compose f identity ≡ f
    associativity : {a b c d : obj}
                    -> (f : mor a b)
                    -> (g : mor b c)
                    -> (h : mor c d)
                    -> compose f (compose g h) ≡ compose (compose f g) h


----- Permutations form a category
module _ where

  open Category

  -- How to prove that two permutations are equal (using extensionality).
  -- With a first-order representation of permutations, this should be
  -- provable without assuming function extensionality.
  permExt : {n m : ℕ} -> {π τ : Permutation n m} ->
            ((i : Fin n) -> π ⟨$⟩ʳ i ≡ τ ⟨$⟩ʳ i) -> π ≡ τ
  permExt {π = π} {τ} p =
    permEq π τ (InverseEq _ _ (ext p))
               (InverseEq _ _ (ext (λ i →
      begin
        π ⟨$⟩ˡ i
          ≡⟨ P.cong (π ⟨$⟩ˡ_) (P.sym (trans (p (τ ⟨$⟩ˡ i)) (inverseʳ τ))) ⟩
        π ⟨$⟩ˡ (π ⟨$⟩ʳ (τ ⟨$⟩ˡ i))
          ≡⟨ inverseˡ π ⟩
        τ ⟨$⟩ˡ i
      ∎)))
    where
      open ≡-Reasoning

      -- We use UIP to show that the proofs in a permutation are all equal
      permIrrelevanceLeft : {n m : ℕ} -> (π : Permutation n m) ->
                        (p q : Inverse.from π InverseOf Inverse.to π) ->
                        _InverseOf_.left-inverse-of p ≡ _InverseOf_.left-inverse-of q
      permIrrelevanceLeft π p q = ext (λ x → uip _ _)
      permIrrelevanceRight : {n m : ℕ} -> (π : Permutation n m) ->
                        (p q : Inverse.from π InverseOf Inverse.to π) ->
                        _InverseOf_.right-inverse-of p ≡ _InverseOf_.right-inverse-of q
      permIrrelevanceRight π p q = ext (λ x → uip _ _)
      permIrrelevance : {n m : ℕ} -> (π : Permutation n m) ->
                        (p q : Inverse.from π InverseOf Inverse.to π) ->
                        p ≡ q
      permIrrelevance π p q with permIrrelevanceLeft π p q | permIrrelevanceRight π p q
      ... | refl | refl = refl
      permEq : {n m : ℕ} -> (π τ : Permutation n m) ->
               Inverse.to π ≡ Inverse.to τ ->
               Inverse.from π ≡ Inverse.from τ ->
               π ≡ τ
      permEq π τ refl refl = P.cong (λ z → record { to = _; from = _; inverse-of = z }) (permIrrelevance τ _ _)

      InverseCongIrrelevance :
         {A B : Set} -> (f : P.setoid A ⟶ P.setoid B) ->
         (p q : {i j : A} → i ≡ j → f ⟨$⟩ i ≡ f ⟨$⟩ j) ->
         (λ {i} {j} → p {i} {j}) ≡ q
      InverseCongIrrelevance f p q = impext (impext (ext λ r → uip _ _))

      InverseEq : {A B : Set} -> (f g : P.setoid A ⟶ P.setoid B) ->
                  _⟨$⟩_ f ≡ _⟨$⟩_ g -> f ≡ g
      InverseEq f g refl with InverseCongIrrelevance g (Π.cong g) (Π.cong f)
      ... | refl = refl


  permutationCat : Category
  obj permutationCat = ℕ
  mor permutationCat = Permutation
  compose permutationCat = _∘ₚ_
  identity permutationCat = Perm.id
  leftIdentity permutationCat f = permExt λ i → refl
  rightIdentity permutationCat f = permExt λ i → refl
  associativity permutationCat f g h = permExt λ i → refl

------ A construction of the free symmetric monoidal category on a category C

module _ (C : Category) where

  open Category C

  -- How to prove that two morphisms are equal (a slightly special
  -- case to simplify calculations)
  morEq' : {n m : ℕ}{as : Vec obj n}{bs : Vec obj m} ->
           {π τ : Permutation n m}
           {π' : Fin n -> Fin m}
           {fs : ((i : Fin n) -> mor (V.lookup as i) (V.lookup bs (π' i)))}
           {gs : ((i : Fin n) -> mor (V.lookup as i) (V.lookup bs (π' i)))}
           (p : π ≡ τ) ->
           ((i : Fin n) -> (fs i) ≡ (gs i)) ->
           (q : π' ≡ (π ⟨$⟩ʳ_)) ->
           (q' : π' ≡ (τ ⟨$⟩ʳ_)) ->
           (π , subst (λ z → (i : Fin n) → mor (V.lookup as i) (V.lookup bs (z i))) q fs) ≡ (τ , subst (λ z → (i : Fin n) → mor (V.lookup as i) (V.lookup bs (z i))) q' gs)
  morEq' {π = π} refl p refl refl = P.cong (π ,_) (ext p)



  FreeSymMonoidal : Category
  obj FreeSymMonoidal = Σ[ n ∈ ℕ ] (Vec obj n)
  mor FreeSymMonoidal (n , as) (m , bs) =
        Σ[ π ∈ Permutation n m ]
         ((i : Fin n) -> mor (V.lookup as i) (V.lookup bs (π ⟨$⟩ʳ i)))
  compose FreeSymMonoidal {n , as} (π , fs) (τ , gs) =
    (π ∘ₚ τ , λ i → compose (fs i) (gs (π ⟨$⟩ʳ i)))
  identity FreeSymMonoidal {n , as} = Perm.id , λ i → identity
  leftIdentity FreeSymMonoidal {n , as} {m , bs} (π , fs) =
    morEq' {as = as} {bs = bs}
           (Category.leftIdentity permutationCat π)
           (λ i → leftIdentity (fs i))
           refl refl
  rightIdentity FreeSymMonoidal {n , as} {m , bs} (π , fs) =
    morEq' {as = as} {bs = bs}
           (Category.rightIdentity permutationCat π)
           (λ i → rightIdentity (fs i))
           refl refl
  associativity FreeSymMonoidal {n , as} {d = l , ds}
                                (π , fs) (τ , gs) (ρ , hs) =
    morEq' {as = as} {bs = ds}
           (Category.associativity permutationCat π τ ρ)
           (λ i → associativity (fs i) (gs (π ⟨$⟩ʳ i)) (hs ((π ∘ₚ τ) ⟨$⟩ʳ i)))
           refl refl

----- Constructing the structure

module _ (C : Category) where

  open Category (FreeSymMonoidal C)


  tensor : (a b : obj) -> obj
  tensor (n , as) (m , bs) = (_ , as V.++ bs)

  unit : obj
  unit = (0 , [])

  juxtaposition : {a b a' b' : obj} ->
                  mor a b -> mor a' b' ->
                  mor (tensor a a') (tensor b b')
  juxtaposition {n , as} {m , bs} {n' , as'} {m' , bs'}
                (π , fs) (τ , gs) = (π Perm++ τ) , fs++gs
    where
      fs++gs : ∀ i → Category.mor C
                                (V.lookup (as V.++ as') i)
                                (V.lookup (bs V.++ bs') ((π Perm++ τ) ⟨$⟩ʳ i))
      fs++gs i with  (toℕ i) N.<? n
      ... | yes p
         rewrite lookup-++-< as as' i p
               | lookup-++ˡ bs bs' (π ⟨$⟩ʳ (fromℕ≤ p)) = fs (fromℕ≤ p)
      ... | no ¬p
         rewrite lookup-++-≥ as as' i (≤-pred (≰⇒> ¬p))
               | lookup-++ʳ bs bs' (τ ⟨$⟩ʳ (reduce≥ i (≤-pred (≰⇒> ¬p)))) =
           gs (reduce≥ i (≤-pred (≰⇒> ¬p)))

  symmetry : {a b : obj} -> mor (tensor a b) (tensor b a)
  symmetry {n , as} {m , bs} = swapBlock n m , ids
    where
      ids : ∀ i → Category.mor C (V.lookup (as V.++ bs) i)
                                (V.lookup (bs V.++ as) (swapBlock n m ⟨$⟩ʳ i))
      ids i rewrite P.sym (lookup-swap as bs i) = Category.identity C
