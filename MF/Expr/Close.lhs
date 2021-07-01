%if False

> {-# LANGUAGE
>              TypeFamilies,
>              FlexibleContexts,
>              ScopedTypeVariables,
>              NoMonomorphismRestriction,
>              ImplicitParams,
>              ExtendedDefaultRules,
>              UnicodeSyntax,
>              DataKinds,
>              TypeApplications,
>              PartialTypeSignatures,
>              AllowAmbiguousTypes,
>              RankNTypes,
>              ScopedTypeVariables,
>              TypeSynonymInstances,
>              FlexibleInstances,
>              TemplateHaskell,
>              MultiParamTypeClasses,
>              TypeOperators,
>              ExistentialQuantification,
>              StandaloneDeriving,
>              UndecidableInstances
> #-}

%endif

> module MF.Expr.Close where

> import MF.Expr.Syn
> import MF.Terminals
> import Data.Proxy

> import Text.Parsec
> import Text.Parsec.Language
> import Text.Parsec.String
> import Text.Parsec.Expr
> import Text.Parsec.Token
> import qualified Text.Parsec.Expr as P

> import MF.Expr.Compile
> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.RecordInstances

> import MF.Core.PP
> import MF.Core.Syn

> import Data.Kind (Type)

> import GHC.Types
> import Unsafe.Coerce

> def = haskellDef
> TokenParser { parens = m_parens
>             , identifier = m_identifier
>             , symbol = m_symbol
>             , reservedOp = m_reservedOp
>             , reserved = m_reserved
>             , commaSep = m_commaSep
>             , whiteSpace = m_whiteSpace
>             , natural = m_natural
>             } = makeTokenParser def


> data SemExpr op var val call
>  = SemExpr {gop   :: op,
>             gvar  :: var,
>             gval  :: val,
>             gcall :: call}


> fl2 f e a b = f e b a


> semCompExpr = SemExpr (scomp_op) (scomp_var) (scomp_val) (scomp_call)


> pVar var p
>   = sem_Expr_Var (var p) <$> m_identifier

> pCall sem@(SemExpr op var val call) p = do
>   f <- m_identifier
>   x <- m_parens (pExpr sem p)
>   return $ sem_Expr_Call (call p) f x
 
> table op p =
>   [[P.Infix (m_reservedOp "*"
>        >> return (fl2 sem_Expr_Op (op proxyVal) Times)) AssocLeft]
>   ,[P.Infix (m_reservedOp "+"
>        >> return (fl2 sem_Expr_Op (op proxyVal) Add)) AssocLeft]
>   ]

> pVal val (p :: Proxy v) = do
>   n <- m_natural
>   return $ sem_Expr_Val (val p) (mki @_ @v n)

> pExprAux sem@(SemExpr op var val call) p =
>   choice [try (pCall sem p), pVar var p, m_parens (pExpr sem p), pVal val p]

> pExpr sem@(SemExpr op var val call) p =
>   buildExpressionParser (table op p) (pExprAux sem p) <?> "expression"

> parserExp' sem doThings s (v :: Proxy v) =
>   let fsem' = parse (pExpr sem v <* eof) "" s
>   in case fsem' of
>      (Right fsem) -> doThings fsem v -- (fsem emptyAtt #. (scomp @v))
>      (Left error) -> putStrLn . show $ error

> parserExp
>  = parserExp' semCompExpr
>    (\fsem (v ::Proxy v)-> print (printCore (fsem emptyAtt #. (scomp @v))))

> class (Values op v) => ExprClass op v semtag r where
>   var :: String -> r

> mkVal val (p :: Proxy v) n
>   = sem_Expr_Val (val p) (mki @_ @v n)
> mkOp  ope  (p :: Proxy v) l op r
>   = sem_Expr_Op (ope p) l op r
> mkVar var (p :: Proxy v) x
>   = sem_Expr_Var (var p) x
> mkCall call (p :: Proxy v) f x
>   = sem_Expr_Call (call p) f x

> semtestExpr = SemExpr (stest_op) (stest_var) (stest_val) (stest_call)

> mkValComp  = mkVal  scomp_val (Proxy @Val)
> mkOpComp   = mkOp   scomp_op  (Proxy @Val)
> mkVarComp  = mkVar  scomp_var (Proxy @Val)
> mkCallComp = mkCall scomp_call (Proxy @Val)

> interp e = e emptyAtt #. (scomp @Val)

> data Expr v
>   = Val v
>   | Op (Expr v) (Val2Op v) (Expr v)
>   | Call String (Expr v)
>   | Var String

> deriving instance (Show v, Show (Val2Op v)) => Show (Expr v)

> proxyFrom :: f a -> Proxy a
> proxyFrom _ = Proxy

> sem_Expr sem@(SemExpr op var val call) v@(Var x)
>   = sem_Expr_Var (var (proxyFrom v)) x

> sem_Expr sem@(SemExpr op var val call) e@(Val v)
>   = sem_Expr_Val (val (proxyFrom e)) v

> sem_Expr sem@(SemExpr op var val call) v@(Op l ope r)
>   = sem_Expr_Op (op (proxyFrom v)) (sem_Expr sem l)
>                        ope
>                        (sem_Expr sem r)

> sem_Expr sem@(SemExpr op var val call) v@(Call f e)
>   = sem_Expr_Call (call (proxyFrom v)) f (sem_Expr sem e)

> compile (e :: Expr Val)
>  = sem_Expr semCompExpr e emptyAtt #. (scomp @Val)
