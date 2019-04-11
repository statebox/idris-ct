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

-- >     -> (leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) (idFunctor cat))
-- >     -> (rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat))
-- >     -> ((a, b, c, d : obj cat) -> MonoidalPentagon cat tensor associator a b c d)
-- >     -> ((a, b : obj cat) -> MonoidalTriangle cat tensor unit associator leftunitor rightUnitor a b)

>     -> MonoidalCategory
>
> cat : MonoidalCategory -> Category
> cat (MkMonoidalCategory innerCat _ _ _ {- _ _ _ _ -}) = innerCat
>
> tensor : (mCat : MonoidalCategory) -> CFunctor (productCategory (cat mCat) (cat mCat)) (cat mCat)
> tensor (MkMonoidalCategory _ monoidalTensor _ _ {- _ _ _ _ -}) = monoidalTensor
>
> unit : (mCat : MonoidalCategory) -> obj (cat mCat)
> unit (MkMonoidalCategory _ _ unit _ {- _ _ _ _ -}) = unit
>
> associator : (mCat : MonoidalCategory) -> Associator (cat mCat) -- (tensor mCat)
> associator (MkMonoidalCategory _ _ _ associator {- _ _ _ _ -}) = associator
>

-- > leftUnitor : (mCat : MonoidalCategory) -> NaturalIsomorphism (cat mCat)
-- >                                                              (cat mCat)
-- >                                                              (leftIdTensor (cat mCat) (tensor mCat) (unit mCat))
-- >                                                              (idFunctor (cat mCat))
-- > leftUnitor (MkMonoidalCategory _ _ _ _ leftUnitor _ _ _) = leftUnitor
-- >
-- > rightUnitor : (mCat : MonoidalCategory) -> NaturalIsomorphism (cat mCat)
-- >                                                              (cat mCat)
-- >                                                              (rightIdTensor (cat mCat) (tensor mCat) (unit mCat))
-- >                                                              (idFunctor (cat mCat))
-- > rightUnitor (MkMonoidalCategory _ _ _ _ _ rightUnitor _ _) = rightUnitor
-- >
