> module Utils
>
> %access public export
> %default total
>
> cong2 : {f : t -> u -> v} -> a = b -> c = d -> f a c = f b d
> cong2 Refl Refl = Refl
