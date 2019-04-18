> module SymmetricMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import MonoidalCategory.MonoidalCategory
> import MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
> import MonoidalCategory.SymmetricMonoidalCategoryHelpers
>
> %access public export
> %default total
>
> data SymmetricMonoidalCategory : Type where
>   MkSymmetricMonoidalCategory :
>        (monoidalCategory : MonoidalCategory)
>     -> AssociativityCoherence (cat monoidalCategory)
>                               (associator monoidalCategory)
>     -> SymmetricMonoidalCategory
