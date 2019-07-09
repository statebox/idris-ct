{-# OPTIONS --cubical #-}
module FSMC where

open import Level

open import Data.List.Membership.Propositional
open import Data.Product

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Data.List
open import Cubical.Data.List.Properties

----- Helper functions

subst₂ : {A B : Set}(P : A -> B -> Set) ->
         {x x' : A}{y y' : B} -> x ≡ x' -> y ≡ y' -> P x y -> P x' y'
subst₂ P p q v = subst (λ z → P (fst z) (snd z)) (λ i → p i , q i) v

subst₂Refl : {A B : Set}(P : A -> B -> Set){x : A}{y : B}(px : P x y) ->
             subst₂ P refl refl px ≡ px
subst₂Refl P px = substRefl {B = λ z → P (fst z) (snd z)} px


subst-∙ : {A : Set}(P : A -> Set) ->
          {x x' x'' : A} (p : x ≡ x')(p' : x' ≡ x'') -> (v : P x) ->
          subst P p' (subst P p v) ≡ subst P (p ∙ p') v
subst-∙  P p p' v = J (λ z r → subst P r (subst P p v) ≡ subst P (p ∙ r) v)
                      (substRefl {B = P} (subst P p v) ∙
                       cong (λ z → subst P z v) (rUnit p)) p'

∙-natural : {A B : Set}(f : A -> B) ->
            {x x' x'' : A} -> (p : x ≡ x')(q : x' ≡ x'') ->
            (λ i → f ((p ∙ q) i)) ≡ (λ i → f (p i)) ∙ (λ i → f (q i))
∙-natural f {x} {x'} {x''} p q =
  J (λ z r → (λ i → f ((p ∙ r) i)) ≡ (λ i → f (p i)) ∙ (λ i → f (r i)))
    (cong {B = λ _ → f x ≡ f x'} (λ z → (λ i → f (z i))) (sym (rUnit p)) ∙
     rUnit (λ i → f (p i)))
    q

subst₂-∙ : {A B : Set}(P : A -> B -> Set) ->
         {x x' x'' : A}{y y' y'' : B} -> (p : x ≡ x') -> (q : y ≡ y') ->
         (p' : x' ≡ x'') -> (q' : y' ≡ y'') -> (v : P x y) ->
         subst₂ P p' q' (subst₂ P p q v) ≡ subst₂ P (p ∙ p') (q ∙ q') v
subst₂-∙ P {x} {x'} {x''} {y} {y'} {y''} p q p' q' v =
  subst-∙ _ (λ i → p i , q i)
            (λ i → p' i , q' i) v ∙
  cong₂ (λ z w → subst₂ P {y = y} {y''} z w v)
        (∙-natural proj₁ (λ i → p i , q i) (λ i → p' i , q' i))
        (∙-natural proj₂ (λ i → p i , q i) (λ i → p' i , q' i))

------ Defs category

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
    set-of-obj : isSet obj -- strict tensor
open Category

record Functor (c d : Category) : Set1 where
  open Category
  field
    mapObj  : obj c -> obj d
    mapMor  : ∀ {x y} → mor c x y -> mor d (mapObj x) (mapObj y)
    mapId   : ∀ {x} → mapMor {x} (identity c) ≡ identity d
    mapComp : ∀ {x y z} (f : mor c x y)(g : mor c y z) →
              mapMor (compose c f g) ≡ compose d (mapMor f) (mapMor g)
open Functor

module _ (c d : Category) where

  open Category

  productCat : Category
  Category.obj productCat = obj c × obj d
  Category.mor productCat (a , a') (b , b') = mor c a b × mor d a' b'
  Category.compose productCat (f , f') (g , g')
    = (compose c f g , compose d f' g')
  Category.identity productCat = (identity c , identity d)
  Category.leftIdentity productCat (f , g)
    = cong₂ _,_ (leftIdentity c f) (leftIdentity d g)
  Category.rightIdentity productCat (f , g)
    = cong₂ _,_ (rightIdentity c f) (rightIdentity d g)
  Category.associativity productCat (f , f') (g , g') (h , h')
    = cong₂ _,_ (associativity c f g h) (associativity d f' g' h')
  Category.set-of-obj productCat
    = isOfHLevelΣ 2 (set-of-obj c) λ _ → set-of-obj d


record StrictMonoidalCategory : Set1 where
  field
    category : Category
    tensor   : Functor (productCat category category) category
    unit     : obj category
    tensorIsLeftUnital  : {a : obj category} -> mapObj tensor (unit , a) ≡ a
    tensorIsRightUnital : {a : obj category} -> mapObj tensor (a , unit) ≡ a
    tensorIsAssociativeObj : {a b c : obj category} ->
                             mapObj tensor (a , mapObj tensor (b , c))
                           ≡ mapObj tensor (mapObj tensor (a , b) , c)
    tensorIsAssociativeMor
      : {a b c d e f : obj category}
      -> (g : mor category a b)
      -> (h : mor category c d)
      -> (k : mor category e f)
      ->  PathP (λ i → mor category
                           (tensorIsAssociativeObj {a} {c} {e} i)
                           (tensorIsAssociativeObj {b} {d} {f} i))
                (mapMor tensor (g , (mapMor tensor (h , k))))
                (mapMor tensor (mapMor tensor (g , h) , k))
open StrictMonoidalCategory

------ The free strict monoidal category on some generating morphisms as a HIT

module _ (V : Set)(V-set : isSet V)
         (generatingMorphisms : List ((List V) × (List V)))
         where

  _⊗_ : List V -> List V -> List V
  _⊗_ = _++_

  Unit : List V
  Unit = []

  data FreeMorphism : List V -> List V -> Set where
   GeneratingFreeMorphism    : ∀ {a b} → (a , b) ∈ generatingMorphisms
                                       -> FreeMorphism a b
   IdFreeMorphism            : ∀ {a} → FreeMorphism a a
   CompositionFreeMorphism   : ∀ {a b c} → FreeMorphism a b
                                        -> FreeMorphism b c
                                        -> FreeMorphism a c
{- -- We leave this out to save time -- no conceptual difficulty
   SymmetryFreeMorphism      : ∀ {a b} → FreeMorphism (a ⊗ b) (b ⊗ a)
-}
   JuxtapositionFreeMorphism : ∀ {a b c d} → FreeMorphism a b
                                          -> FreeMorphism c d
                                          -> FreeMorphism (a ⊗ c) (b ⊗ d)
   -- quotients composition
   FreeLeftidentity  : ∀ {a b} (f : FreeMorphism a b) →
                         CompositionFreeMorphism IdFreeMorphism f ≡ f
   FreeRightidentity : ∀ {a b} (f : FreeMorphism a b) →
                         CompositionFreeMorphism f IdFreeMorphism ≡ f
   FreeAssociativity : ∀ {a b c d}(f : FreeMorphism a b)
                                  (g : FreeMorphism b c)
                                  (h : FreeMorphism c d) →
                         CompositionFreeMorphism f (CompositionFreeMorphism g h)
                       ≡ CompositionFreeMorphism (CompositionFreeMorphism f g) h
   -- quotients tensor
   FreeTensorPreserveId : ∀ {a a'} →
                           JuxtapositionFreeMorphism
                             (IdFreeMorphism {a}) (IdFreeMorphism {a'})
                          ≡ IdFreeMorphism
   FreeTensorPreserveCompose : ∀ {a a' b b' c c'}
                                 (f : FreeMorphism a b)(f' : FreeMorphism a' b')
                                 (g : FreeMorphism b c)(g' : FreeMorphism b' c') →
                                   JuxtapositionFreeMorphism
                                     (CompositionFreeMorphism f g)
                                     (CompositionFreeMorphism f' g')
                                 ≡ CompositionFreeMorphism
                                     (JuxtapositionFreeMorphism f f')
                                     (JuxtapositionFreeMorphism g g')
   FreeTensorAssociative : ∀ {a b c d e f}
                             (g : FreeMorphism a b)
                             (h : FreeMorphism c d)
                             (k : FreeMorphism e f) →
        PathP (λ i → FreeMorphism (sym (++-assoc a c e) i) (sym (++-assoc b d f) i))
         (JuxtapositionFreeMorphism g (JuxtapositionFreeMorphism h k))
         (JuxtapositionFreeMorphism (JuxtapositionFreeMorphism g h) k)

  FreeSymMonoidal : Category
  obj FreeSymMonoidal = List V
  mor FreeSymMonoidal = FreeMorphism
  compose FreeSymMonoidal = CompositionFreeMorphism
  identity FreeSymMonoidal = IdFreeMorphism
  leftIdentity FreeSymMonoidal = FreeLeftidentity
  rightIdentity FreeSymMonoidal = FreeRightidentity
  associativity FreeSymMonoidal = FreeAssociativity
  set-of-obj FreeSymMonoidal = isOfHLevelList 0 V-set

  FreeSymMonoidal-monoidal : StrictMonoidalCategory
  category FreeSymMonoidal-monoidal = FreeSymMonoidal
  mapObj (tensor FreeSymMonoidal-monoidal) (a , b) = a ⊗ b
  mapMor (tensor FreeSymMonoidal-monoidal) (f , g)
    = JuxtapositionFreeMorphism f g
  mapId (tensor FreeSymMonoidal-monoidal) = FreeTensorPreserveId
  mapComp (tensor FreeSymMonoidal-monoidal) (f , f') (g , g')
    = FreeTensorPreserveCompose f f' g g'
  unit FreeSymMonoidal-monoidal = Unit
  tensorIsLeftUnital FreeSymMonoidal-monoidal = refl
  tensorIsRightUnital FreeSymMonoidal-monoidal {a} = ++-unit-r a
  tensorIsAssociativeObj FreeSymMonoidal-monoidal {a} {b} {c}
    = sym (++-assoc a b c)
  tensorIsAssociativeMor FreeSymMonoidal-monoidal g h k
    = FreeTensorAssociative g h k

----- Part of the universal property

module _ (V : Set)(V-set : isSet V)
         (generatingMorphisms : List ((List V) × (List V)))
         (ssmc : StrictMonoidalCategory)
         (onV : V -> obj (category ssmc)) where

  module Free = Category (FreeSymMonoidal V V-set generatingMorphisms)
  module C = Category (category ssmc)

  -- canonically extend onV to tensors
  onObj : List V -> C.obj
  onObj [] = unit ssmc
  onObj (a ∷ as) = mapObj (tensor ssmc) (onV a , onObj as)

  onObjTensor : ∀ a c →
                mapObj (tensor ssmc) (onObj a , onObj c) ≡ onObj (a ++ c)
  onObjTensor [] c = tensorIsLeftUnital ssmc
  onObjTensor (a ∷ as) c =
    sym (tensorIsAssociativeObj ssmc {onV a} {onObj as} {onObj c}) ∙
    cong (λ z →  mapObj (tensor ssmc) (onV a , z)) (onObjTensor as c)

  foldOnMorphisms :
      (onGeneratingMor :
           ∀ {a b} → (a , b) ∈ generatingMorphisms
           -> C.mor (onObj a) (onObj b))
   -> ∀ {a b} → Free.mor a b -> C.mor (onObj a) (onObj b)
  foldOnMorphisms onGeneratingMor (GeneratingFreeMorphism p)
    = onGeneratingMor p
  foldOnMorphisms onGeneratingMor IdFreeMorphism = C.identity
  foldOnMorphisms onGeneratingMor (CompositionFreeMorphism f g)
    = C.compose (foldOnMorphisms onGeneratingMor f)
                (foldOnMorphisms onGeneratingMor g)
  foldOnMorphisms onGeneratingMor (JuxtapositionFreeMorphism {a} {b} f g)
    = subst₂ C.mor (onObjTensor a _) (onObjTensor b _)
             (Functor.mapMor (tensor ssmc) (foldOnMorphisms onGeneratingMor f ,
                                            foldOnMorphisms onGeneratingMor g))
  foldOnMorphisms onGeneratingMor (FreeLeftidentity f i)
    = C.leftIdentity (foldOnMorphisms onGeneratingMor f) i
  foldOnMorphisms onGeneratingMor (FreeRightidentity f i)
    = C.rightIdentity (foldOnMorphisms onGeneratingMor f) i
  foldOnMorphisms onGeneratingMor (FreeAssociativity f g h i)
   = C.associativity (foldOnMorphisms onGeneratingMor f)
                     (foldOnMorphisms onGeneratingMor g)
                     (foldOnMorphisms onGeneratingMor h) i
  foldOnMorphisms onGeneratingMor (FreeTensorPreserveId {a = a} i) = goal i
    where goal : foldOnMorphisms onGeneratingMor
                                 (JuxtapositionFreeMorphism
                                   (IdFreeMorphism {a = a})
                                   IdFreeMorphism)
                  ≡ foldOnMorphisms onGeneratingMor
                                    (IdFreeMorphism {a = a ++ _})
          goal = J (λ _ z → subst₂ C.mor z z
                                   (mapMor (tensor ssmc)
                                           (C.identity , C.identity))
                              ≡ C.identity)
                   (subst₂Refl C.mor _ ∙ mapId (tensor ssmc))
                   (onObjTensor a _)
  foldOnMorphisms onGeneratingMor (FreeTensorPreserveCompose {a} {a'} {b} {b'} {c} {c'} f f' g g' i) = goal i
    where goal : foldOnMorphisms onGeneratingMor
                                 (JuxtapositionFreeMorphism
                                   (CompositionFreeMorphism f g)
                                   (CompositionFreeMorphism f' g'))
                 ≡ C.compose (foldOnMorphisms onGeneratingMor
                                              (JuxtapositionFreeMorphism f f'))
                             (foldOnMorphisms onGeneratingMor
                                              (JuxtapositionFreeMorphism g g'))
          goal = J (λ _ p → let a = λ i → proj₁ (p i)
                                b = λ i → proj₁ (proj₂ (p i))
                                c = λ i → proj₂ (proj₂ (p i)) in
                     subst₂ C.mor a c
                            (mapMor (tensor ssmc)
                                    (C.compose
                                      (foldOnMorphisms onGeneratingMor f)
                                      (foldOnMorphisms onGeneratingMor g) ,
                                     C.compose
                                       (foldOnMorphisms onGeneratingMor f')
                                       (foldOnMorphisms onGeneratingMor g')))
                     ≡ C.compose
                         (subst₂ C.mor a b
                           (mapMor (tensor ssmc)
                             (foldOnMorphisms onGeneratingMor f ,
                              foldOnMorphisms onGeneratingMor f')))
                         (subst₂ C.mor b c
                            (mapMor (tensor ssmc)
                              (foldOnMorphisms onGeneratingMor g ,
                               foldOnMorphisms onGeneratingMor g'))))
           (subst₂Refl C.mor _ ∙
            mapComp (tensor ssmc)
             (foldOnMorphisms onGeneratingMor f ,
              foldOnMorphisms onGeneratingMor f')
             (foldOnMorphisms onGeneratingMor g ,
              foldOnMorphisms onGeneratingMor g') ∙
            cong₂ C.compose (sym (subst₂Refl C.mor _))
                            (sym (subst₂Refl C.mor _)))
            (λ i → (onObjTensor a a' i) , (onObjTensor b b' i) , onObjTensor c c' i)
  foldOnMorphisms onGeneratingMor (FreeTensorAssociative {a} {b} {c} {d} {e} {f} ff gg hh i) = goal i
    where f' = foldOnMorphisms onGeneratingMor ff
          g' = foldOnMorphisms onGeneratingMor gg
          h' = foldOnMorphisms onGeneratingMor hh
          unfolded-goal :
            subst₂ C.mor (λ i → onObj (sym (++-assoc a c e) i))
                         (λ i → onObj (sym (++-assoc b d f) i))
                   (subst₂ C.mor (onObjTensor a (c ++ e))
                                 (onObjTensor b (d ++ f))
                           (mapMor (tensor ssmc)
                                   (f' ,
                                    subst₂ C.mor (onObjTensor c e)
                                                 (onObjTensor d f)
                                            (mapMor (tensor ssmc) (g' , h')))))
             ≡ (subst₂ C.mor (onObjTensor (a ++ c) e)
                             (onObjTensor (b ++ d) f)
                       (mapMor (tensor ssmc)
                               (subst₂ C.mor (onObjTensor a c)
                                             (onObjTensor b d)
                                       (mapMor (tensor ssmc) (f' , g')) , h')))
          unfolded-goal = -- THIS PROOF IS JUST PATH ALGEBRA, EXCEPT FOR IN TWO PLACES BELOW
            subst₂ C.mor (λ i → onObj (sym (++-assoc a c e) i))
                         (λ i → onObj (sym (++-assoc b d f) i))
                   (subst₂ C.mor (onObjTensor a (c ++ e))
                                 (onObjTensor b (d ++ f))
                            (mapMor (tensor ssmc)
                                    (f' ,
                                     subst₂ C.mor (onObjTensor c e)
                                                  (onObjTensor d f)
                                            (mapMor (tensor ssmc) (g' , h')))))
              ≡⟨ subst₂-∙ C.mor (onObjTensor a (c ++ e))
                                (onObjTensor b (d ++ f)) _ _ _ ⟩
            subst₂ C.mor (onObjTensor a (c ++ e) ∙ (λ i → onObj (sym (++-assoc a c e) i)))
                         (onObjTensor b (d ++ f) ∙ (λ i → onObj (sym (++-assoc b d f) i)))
                         (mapMor (tensor ssmc)
                                 (f' , subst₂ C.mor (onObjTensor c e)
                                                    (onObjTensor d f)
                                              (mapMor (tensor ssmc) (g' , h'))))
              ≡⟨ cong (subst₂ C.mor (onObjTensor a (c ++ e) ∙ (λ i → onObj (sym (++-assoc a c e) i)))
                                    (onObjTensor b (d ++ f) ∙ (λ i → onObj (sym (++-assoc b d f) i))))
                      (J (λ _ r → let r₀ = λ i → proj₁ (r i); r₁ = λ i → proj₂ (r i) in
                            mapMor (tensor ssmc) (f' , subst₂ C.mor r₀ r₁ (mapMor (tensor ssmc) (g' , h'))) ≡
                            subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (onObj a , z)) r₀)
                                         (cong (λ z → mapObj (tensor ssmc) (onObj b , z)) r₁)
                                         (mapMor (tensor ssmc) (f' , mapMor (tensor ssmc) (g' , h'))))
                         (cong (λ z → mapMor (tensor ssmc) (f' , z))
                               (subst₂Refl C.mor (mapMor (tensor ssmc) (g' , h'))) ∙ sym (subst₂Refl C.mor _))
                         (λ i → (onObjTensor c e i , onObjTensor d f i))) ⟩
            subst₂ C.mor (onObjTensor a (c ++ e) ∙ (λ i → onObj (sym (++-assoc a c e) i)))
                         (onObjTensor b (d ++ f) ∙ (λ i → onObj (sym (++-assoc b d f) i)))
                         (subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (onObj a , z)) (onObjTensor c e))
                                       (cong (λ z → mapObj (tensor ssmc) (onObj b , z)) (onObjTensor d f))
                                       (mapMor (tensor ssmc) (f' , mapMor (tensor ssmc) (g' , h'))))
              ≡⟨ subst₂-∙ C.mor (cong (λ z → mapObj (tensor ssmc) (onObj a , z)) (onObjTensor c e))
                                (cong (λ z → mapObj (tensor ssmc) (onObj b , z)) (onObjTensor d f)) _ _ _ ⟩
            subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (onObj a , z)) (onObjTensor c e) ∙ (onObjTensor a (c ++ e) ∙ (λ i → onObj (sym (++-assoc a c e) i))))
                         (cong (λ z → mapObj (tensor ssmc) (onObj b , z)) (onObjTensor d f) ∙ (onObjTensor b (d ++ f) ∙ (λ i → onObj (sym (++-assoc b d f) i))))
                         (mapMor (tensor ssmc) (f' , mapMor (tensor ssmc) (g' , h')))

              -- HERE IS SOME CONTENT IN THE PROOF: WE USE THAT WE HAVE A SET OF OBJECTS
              ≡⟨ cong₂ (λ z w → subst₂ C.mor {y' = onObj ((b ++ d) ++ f)} z w (mapMor (tensor ssmc) (f' , mapMor (tensor ssmc) (g' , h'))))
                       (set-of-obj (category ssmc) _ _
                                   (cong (λ z → mapObj (tensor ssmc) (onObj a , z)) (onObjTensor c e) ∙ (onObjTensor a (c ++ e) ∙ (λ i → onObj (sym (++-assoc a c e) i))))
                                   (tensorIsAssociativeObj ssmc ∙ (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) (onObjTensor a c) ∙ onObjTensor (a ++ c) e)))
                       (set-of-obj (category ssmc) _ _
                                   (cong (λ z → mapObj (tensor ssmc) (onObj b , z)) (onObjTensor d f) ∙ (onObjTensor b (d ++ f) ∙ (λ i → onObj (sym (++-assoc b d f) i))))
                                   (tensorIsAssociativeObj ssmc ∙ (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) (onObjTensor b d) ∙ onObjTensor (b ++ d)  f))) ⟩
              --------------------------------------------------------------------------

            subst₂ C.mor (tensorIsAssociativeObj ssmc ∙ (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) (onObjTensor a c) ∙ onObjTensor (a ++ c) e))
                         (tensorIsAssociativeObj ssmc ∙ (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) (onObjTensor b d) ∙ onObjTensor (b ++ d)  f))
                         (mapMor (tensor ssmc) (f' , mapMor (tensor ssmc) (g' , h')))
              ≡⟨ sym (subst₂-∙ C.mor (tensorIsAssociativeObj ssmc)
                                     (tensorIsAssociativeObj ssmc) _ _ _) ⟩
            subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) (onObjTensor a c) ∙ onObjTensor (a ++ c) e)
                         (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) (onObjTensor b d) ∙ onObjTensor (b ++ d)  f)
                         (subst₂ C.mor (tensorIsAssociativeObj ssmc)
                                       (tensorIsAssociativeObj ssmc)
                                       (mapMor (tensor ssmc) (f' , mapMor (tensor ssmc) (g' , h'))))

              -- HERE IS SOME MORE CONTENT: WE USE THAT THE TARGET CATEGORY HAS AN ASSOCIATIVE TENSOR
              ≡⟨ cong (subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) (onObjTensor a c) ∙ onObjTensor (a ++ c) e)
                                    (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) (onObjTensor b d) ∙ onObjTensor (b ++ d) f))
                      (fromPathP (tensorIsAssociativeMor ssmc f' g' h')) ⟩
              ---------------------------------------------------------------------------------------

            subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) (onObjTensor a c) ∙ onObjTensor (a ++ c) e)
                         (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) (onObjTensor b d) ∙ onObjTensor (b ++ d) f)
                         (mapMor (tensor ssmc) (mapMor (tensor ssmc) (f' , g') , h'))
              ≡⟨ sym (subst₂-∙ C.mor (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) (onObjTensor a c))
                                     (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) (onObjTensor b d))
                                     (onObjTensor (a ++ c) e)
                                     (onObjTensor (b ++ d) f)
                                     (mapMor (tensor ssmc) (mapMor (tensor ssmc) (f' , g') , h'))) ⟩
            subst₂ C.mor (onObjTensor (a ++ c) e)
                         (onObjTensor (b ++ d) f)
                         (subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) (onObjTensor a c))
                                       (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) (onObjTensor b d))
                                       (mapMor (tensor ssmc) (mapMor (tensor ssmc) (f' , g') , h')))
              ≡⟨ cong (subst₂ C.mor (onObjTensor (a ++ c) e) (onObjTensor (b ++ d) f))
                      (J (λ _ r → let r₀ = λ i → proj₁ (r i); r₁ = λ i → proj₂ (r i) in
                            subst₂ C.mor (cong (λ z → mapObj (tensor ssmc) (z , onObj e)) r₀)
                                         (cong (λ z → mapObj (tensor ssmc) (z , onObj f)) r₁)
                                         (mapMor (tensor ssmc) (mapMor (tensor ssmc) (f' , g') , h')) ≡
                            mapMor (tensor ssmc) (subst₂ C.mor r₀ r₁ (mapMor (tensor ssmc) (f' , g')) , h'))
                         (subst₂Refl C.mor _ ∙
                          cong (λ z → mapMor (tensor ssmc) (z , h'))
                               (sym (subst₂Refl C.mor (mapMor (tensor ssmc) (f' , g')))))
                         (λ i → (onObjTensor a c i , onObjTensor b d i))) ⟩
            (subst₂ C.mor (onObjTensor (a ++ c) e)
                          (onObjTensor (b ++ d) f)
                            (mapMor (tensor ssmc)
                                    (subst₂ C.mor (onObjTensor a c)
                                                  (onObjTensor b d)
                                            (mapMor (tensor ssmc) (f' , g')) ,
                                     h'))) ∎
          goal : PathP (λ i → C.mor (onObj (sym (++-assoc a c e) i))
                                    (onObj (sym (++-assoc b d f) i)))
                    (subst₂ C.mor (onObjTensor a (c ++ e))
                                  (onObjTensor b (d ++ f))
                            (mapMor (tensor ssmc)
                                    (f' ,
                                     subst₂ C.mor (onObjTensor c e)
                                                  (onObjTensor d f)
                                            (mapMor (tensor ssmc) (g' , h')))))
                    (subst₂ C.mor (onObjTensor (a ++ c) e)
                                  (onObjTensor (b ++ d) f)
                            (mapMor (tensor ssmc)
                                    (subst₂ C.mor (onObjTensor a c)
                                                  (onObjTensor b d)
                                            (mapMor (tensor ssmc) (f' , g')) ,
                                     h')))
          goal = toPathP unfolded-goal
