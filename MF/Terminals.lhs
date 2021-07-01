> {-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FunctionalDependencies#-}

> module MF.Terminals where
> import Control.Monad

> class (Read op, Read v) => Values op v | op -> v, v -> op where
>   type Val2Op v :: * 
>   ap   :: op -> v -> v -> v
>   cmp  :: Ordering -> v -> v -> Bool
>   mki  :: Integer -> v

> instance Values Op Val where
>   type Val2Op Val = Op 
>   ap Add (I a)(I b) = I $ a+b
>   ap Times (I a)(I b) = I $ a*b
>   cmp LT (I a)(I b) = a < b
>   mki = I

> instance Read Val where
>   readsPrec p i = map (\(a,b) -> (I a, b)) $ readsPrec p i

> data Op = Add | Times deriving (Eq, Read, Ord)
> data Val = I Integer deriving (Eq, Ord)

> instance Show Op where
>   show Add = "+"
>   show Times = "*"

> instance Show Val where
>   show (I n) = show n

> fromRight (Right a) = a
> fromRight (Left e) = error . show $ e
