> module WiringDiagram.DiscreteDynamicalSystem
>
> import Basic.Category
>
> %access public export
> %default total
>
> -- An (X_1, X_2)-discrete dynamical system is (S, f^update, f^redOut) where
> -- S = set of states
> -- f^update : S \times X_1 -> S
> -- f^readOut : S -> X_2
>
> data DDS : Type -> Type -> Type where
>   MkDDS : (X1, X2, S : Type) -> (fupd : (S, X1) -> S) -> (frdt : S -> X2) -> DDS X1 X2
>
> data DDSMorphism : (X1, X2 : Type) -> DDS X1 X2 -> DDS X1 X2 -> Type
>
> ddsAsCategory : (X1, X2 : Type) -> Category
> ddsAsCategory X1 X2 = MkCategory
>   (DDS X1 X2)
>   (DDSMorphism X1 X2)
>   ?id
>   ?comp
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

