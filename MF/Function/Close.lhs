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
>              TypeOperators
> #-}

%endif

> module MF.Function.Close where

> import MF.Expr.Syn
> import MF.Terminals
> import Data.Proxy
> import MF.Function.Syn
> import MF.Expr.Close
> import MF.Function.Compile

> import Text.Parsec
> import Text.Parsec.Language
> import Text.Parsec.String
> import Text.Parsec.Expr
> import Text.Parsec.Token
> import qualified Text.Parsec.Expr as P

> import MF.Expr.Compile
> import Language.Grammars.AspectAG

> import MF.Core.Eval --
> import MF.Core.PP
> import MF.Core.Syn
> import MF.Core.PP   -- tests

> data SemFunc eif eor top neg and comp fdef pnil pcons op var val call=
>   SemFunc { seif   :: eif,
>             seor   :: eor,
>             stop   :: top,
>             sneg   :: neg,
>             sand   :: and,
>             scomp_ :: comp,
>             sfdef  :: fdef,
>             spnil  :: pnil,
>             spcons :: pcons,
>             sexpr  :: (SemExpr op var val call)
>           }
>

> data FDef v
>   = FDef String (Ecu v)

> data Ecu v
>   = Ecu Vars (ExprG v)

> data ExprG v
>   = Or (Expr v)
>   | If  (Expr v) (Cond v) (Expr v)

> data Cond v
>   = Top
>   | Comp (Expr v) Ordering (Expr v)
>   | And (Cond v) (Cond v)
>   | Neg (Cond v)

> sem_Cond sem e@(Top :: Cond v)
>   = sem_Cond_Top (stop sem (proxyFrom e))
> sem_Cond sem e@(Neg e')
>   = sem_Cond_Neg (sneg sem (proxyFrom e)) (sem_Cond sem e')
> sem_Cond sem e@(And l r)
>   = sem_Cond_And (sand sem (proxyFrom e))
>                  (sem_Cond sem l)
>                  (sem_Cond sem r)
> sem_Cond sem e@(Comp l o r)
>   = sem_Cond_Comp  (scomp_ sem (proxyFrom e))
>                    (sem_Expr (sexpr sem) l)
>                    o
>                    (sem_Expr (sexpr sem) r)

> compileCond :: Cond Val -> CTerm Op Val
> compileCond c = sem_Cond semCompFunc c emptyAtt #. (scomp @Val)



> semCompFunc =
>    SemFunc () () scomp_top scomp_neg scomp_and  scomp_comp
>        () () ()  semCompExpr

Discutir esto

  semCompFunc = SemFunc () scompeor () () () () () () semCompExpr

> pEOr sfun p = do
>   --m_reserved "or"
>   e <- pExpr (sexpr sfun) p
>   return $ sem_ExprG_EOr (seor sfun p) e

> pTop sfun p = do
>   m_reserved "T"
>   return $ sem_Cond_Top (stop sfun p)

> pNeg sfun p = do
>   m_reserved "~"
>   c <- pCond sfun p
>   return $ sem_Cond_Neg (sneg sfun p) c

> pAnd sfun p = do
>   l <- pCond sfun p
>   m_reserved "&"
>   r <- pCond sfun p
>   return $ sem_Cond_And (sand sfun p) l r

> pOp = m_symbol "<" >> return LT

> pComp sfun p = do
>   l   <- pExpr (sexpr sfun) p
>   op  <- pOp
>   r   <- pExpr (sexpr sfun) p
>   return $ sem_Cond_Comp (scomp_ sfun p) l op r


> pCondAux sfun p = pTop sfun p  <|> pComp sfun p 
>                <|> m_parens (pCondAux sfun p)
>                <|> pCond sfun p

> pCond sfun p
>   = buildExpressionParser (tableCond sfun p) (pCondAux sfun p) <?> "condition"

> tableCond sfun p =
>   [[P.Prefix (m_reservedOp "~" >> return (sem_Cond_Neg (sneg sfun p)))],
>    [P.Infix (m_reservedOp "&" >> return (sem_Cond_And (sand sfun p))) AssocLeft]
>   ]
