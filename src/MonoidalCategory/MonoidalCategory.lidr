> module MonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
>
> %access public export
> %default total
>
> -- we are not using a record here because compilation does not terminate in that case
> data MonoidalCategory : Type where
>   MkMonoidalCategory :
>        (cat : Category)
>     -> (tensor : CFunctor (productCategory cat cat) cat)
>     -> (unit : obj cat)
>     -> (associator : Associator cat {- tensor -})
>     -> MonoidalCategory
>
> cat : MonoidalCategory -> Category
> cat (MkMonoidalCategory innerCat _ _ _) = innerCat
>
> tensor : (mCat : MonoidalCategory) -> CFunctor (productCategory (cat mCat) (cat mCat)) (cat mCat)
> tensor (MkMonoidalCategory _ monoidalTensor _ _) = monoidalTensor
>
> unit : (mCat : MonoidalCategory) -> obj (cat mCat)
> unit (MkMonoidalCategory _ _ unit _) = unit
>
> associator : (mCat : MonoidalCategory) -> Associator (cat mCat)
> associator (MkMonoidalCategory _ _ _ associator) = associator
