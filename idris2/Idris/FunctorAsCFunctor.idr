module Idris.FunctorAsCFunctor

import Basic.Category
import Basic.Functor
import Idris.TypesAsCategoryExtensional
import Utils

public export
functorOnMorphisms :
     VerifiedFunctor f
  -> (a, b : Type)
  -> ExtensionalTypeMorphism a b
  -> ExtensionalTypeMorphism (f a) (f b)
functorOnMorphisms _ _ _ (MkExtensionalTypeMorphism g) = MkExtensionalTypeMorphism (map g)

public export
functorPreserveId :
     (func : VerifiedFunctor f)
  -> (a : Type)
  -> functorOnMorphisms func a a (extIdentity a) = extIdentity (f a)
functorPreserveId _ a = funExt (\x => functorIdentity id (\v => Refl) x)

public export
functorPreserveCompose :
     (func : VerifiedFunctor f)
  -> (a, b, c : Type)
  -> (g : ExtensionalTypeMorphism a b)
  -> (h : ExtensionalTypeMorphism b c)
  -> functorOnMorphisms func a c (extCompose a b c g h)
   = extCompose (f a) (f b) (f c) (functorOnMorphisms func a b g) (functorOnMorphisms func b c h)
functorPreserveCompose func _ _ _ (MkExtensionalTypeMorphism g') (MkExtensionalTypeMorphism h')
  = funExt (\x => functorComposition x g' h')

public export
functorToCFunctor :
     {f : Type -> Type} ->
     VerifiedFunctor f
  -> CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional
              TypesAsCategoryExtensional.typesAsCategoryExtensional
functorToCFunctor func = MkCFunctor
  f
  (functorOnMorphisms func)
  (functorPreserveId func)
  (functorPreserveCompose func)