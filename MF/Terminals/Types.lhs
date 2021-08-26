> {-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FunctionalDependencies,
>   PackageImports, AllowAmbiguousTypes, TypeApplications  #-}

> module MF.Terminals.Types where

> import MF.Terminals.Values
> import "mtl" Control.Monad.Except

> class Types op v t where -- no fundeps
>   typeOf  :: v -> t
>   tyComb  :: t -> op -> t -> Except String t
>   join :: t -> t -> Except String t


Esto hay que moverlo a otro modulo

> data Ty =
>   TyR | TyZ | Sec Ty | Ty :* Ty


> instance Types Op Val Ty where
>   typeOf (I _) = TyZ
>   typeOf (R _) = TyR
>   typeOf Nil  = Sec TyZ

>   tyComb a Cons (Sec b) = join @Op @Val a b


>   join TyR TyZ = return TyR
>   join TyZ TyR = return TyR
>   join TyZ TyZ = return TyZ
>   join TyR TyR = return TyR
>   join _ _ = throwError "incompatible types"
