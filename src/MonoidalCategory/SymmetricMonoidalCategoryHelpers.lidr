> module SymmetricMonoidalCategoryHelpers
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import MonoidalCategory.MonoidalCategory
> import MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
>
> %access public export
> %default total
>
> AssociativityCoherence :
>      (cat : Category)
>   -> (associator : Associator cat {- tensor -})
>   -> Type
> AssociativityCoherence cat associator = ()
