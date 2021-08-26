> {-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FunctionalDependencies#-}

> module MF.Terminals.Values where
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
>   ap Div   (I a)(I b) = I $ a `div` b
>   ap Minus (I a)(I b) = I $ a - b 
>   cmp LT (I a)(I b) = a < b
>   cmp GT (I a)(I b) = a > b
>   cmp EQ (I a)(I b) = a == b
>   mki = I

> instance Read Val where
>   readsPrec p i = map (\(a,b) -> (I a, b)) $ readsPrec p i

> data Op = Add | Times | Div | Minus | Cons deriving (Eq, Read, Ord)
> data Val = I Integer | R Double | Nil deriving (Eq, Ord)

> instance Show Op where
>   show Add = "+"
>   show Times = "*"
>   show Div   = "/"
>   show Minus = "-"

> instance Show Val where
>   show (I n) = show n

> fromRight (Right a) = a
> fromRight (Left e) = error . show $ e
