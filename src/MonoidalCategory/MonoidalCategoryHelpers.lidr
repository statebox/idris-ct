> module MonoidalCategoryHelpers
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import Product.ProductCategory
> import Product.ProductFunctor
> import Utils
>
> %access public export
> %default total
>
> postulate
> functor3 : (cat : Category) -> CFunctor (productCategory cat (productCategory cat cat)) cat
>
> Associator :
>      (cat : Category)
>   -> Type
> Associator cat {- tensor -} = NaturalIsomorphism (productCategory cat (productCategory cat cat))
>                                            cat
>                                            (functor3 cat)
>                                            (functor3 cat)
