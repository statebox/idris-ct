> module WiringDiagram.DiscreteDynamicalSystem
>
> import Basic.Category
> import Basic.Functor
> import Cats.CatsAsCategory
> import WiringDiagram.WiringDiagram
>
> %access public export
> %default total
>
> -- An (X_1, X_2)-discrete dynamical system is (S, f^update, f^redOut) where
> -- S = set of states
> -- f^update : X_1 \times S -> S
> -- f^readOut : S -> X_2
>
> data DDS : Type -> Type -> Type where
>   MkDDS : (x1, x2, s : Type) -> (fupd : (x1, s) -> s) -> (frdt : s -> x2) -> DDS x1 x2
>
> data DDSMorphism : DDS x1 x2 -> DDS x1 x2 -> Type
>
> ddsIdentity : (dds : DDS x1 x2) -> DDSMorphism dds dds
>
> ddsComposition : (dds1, dds2, dds3 : DDS x1 x2) -> (DDSMorphism dds1 dds2) -> (DDSMorphism dds2 dds3) -> (DDSMorphism dds1 dds3)
>
> ddsAsCategory : (x1, x2 : Type) -> Category
> ddsAsCategory x1 x2 = MkCategory
>   (DDS x1 x2)
>   (DDSMorphism {x1} {x2})
>   ddsIdentity
>   ddsComposition
>   ?lid
>   ?rid
>   ?assoc
>
> -- Denote by DDS(X1, X2) the set (category) of (X1, X2)-discrete dynamical systems
> -- Define a W_Set algebra as follows:
> -- DDS : W_Set -> Cat
> --       X = (X_1, X_2) -> DDS(X_1, X_2)
> --       \phi : X -> Y  -> DDS_\phi : DDS(X_1, X_2) -> DDS(Y1, Y_2)
> -- Given a (X_1, X_2)-DDS (S, f^update : (X_1, S) -> S, f^readout : S -> X_2)
> -- and a wiring diagram \phi : (\phi_1 : (Y_1, X_2) -> X_1, \phi_2 : X_2 -> Y_2)
> -- we can define a (Y_1, Y_2)-DDS
> --   S -- same set of states
> --   f^update  : (Y_1, S) -> (Y_1, S, S) -> (Y_1, X_2, S) -> (X_1, S) -> S
> --   f^readout : S -> X_2 -> Y_2
>
> ddsAlgebraMapObj : (wiringDiagram : (Type, Type)) -> Category
> ddsAlgebraMapObj wiringDiagram = ddsAsCategory (fst wiringDiagram) (snd wiringDiagram)
>
> ddsAlgebraMapMorMapObj :
>      (wd1, wd2 : (Type, Type))
>   -> WiringDiagramMorphism wd1 wd2
>   -> (DDS (fst wd1) (snd wd1))
>   -> (DDS (fst wd2) (snd wd2))
> ddsAlgebraMapMorMapObj wd1 wd2 (MkWiringDiagramMorphism f1 f2) (MkDDS (fst wd1) (snd wd1) s fupd frdt) = MkDDS
>   (fst wd2)
>   (snd wd2)
>   s
>   (fupd . (pairMorphism f1 id) . tupleAssociativity . (pairMorphism id (pairMorphism frdt id)) . (pairMorphism id delta))
>   (f2 . frdt)
>
> ddsAlgebraMapMorMapMor :
>      (wd1, wd2 : (Type, Type))
>   -> (wdMorphism : WiringDiagramMorphism wd1 wd2)
>   -> (a, b : DDS (fst wd1) (snd wd1))
>   -> (DDSMorphism a b)
>   -> (DDSMorphism (ddsAlgebraMapMorMapObj wd1 wd2 wdMorphism a) (ddsAlgebraMapMorMapObj wd1 wd2 wdMorphism b))
>
> ddsAlgebraMapMor : (wd1, wd2 : (Type, Type)) -> WiringDiagramMorphism wd1 wd2 -> CFunctor (ddsAlgebraMapObj wd1) (ddsAlgebraMapObj wd2)
> ddsAlgebraMapMor wd1 wd2 wdMorphism = MkCFunctor
>   (ddsAlgebraMapMorMapObj wd1 wd2 wdMorphism)
>   (ddsAlgebraMapMorMapMor wd1 wd2 wdMorphism)
>   ?morPresId
>   ?morPresComp
>
> ddsAlgebra : CFunctor WiringDiagram.wiringDiagramCategory CatsAsCategory.catsAsCategory
> ddsAlgebra = MkCFunctor
>   ddsAlgebraMapObj
>   ddsAlgebraMapMor
>   ?presId
>   ?presComp
