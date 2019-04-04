> module WiringDiagram.DiscreteDynamicalSystem
>
> %access public export
> %default total
>
> -- An (X1, X2)-discrete dynamical system is (S, f^update, f^redOut) where
> -- S = set of states
> -- f^update : S \tmies X_1 -> S
> -- f?readOut : S -> X_2
>
> data DDS : Type -> Type -> Type -> Type where
>   MkDDS : (X1, X2, S : Type) -> (fupd : (S, X1) -> S) -> (frdt : S -> X2) -> DDS X1 X2 S
