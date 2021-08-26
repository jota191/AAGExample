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
>              TypeOperators, StandaloneDeriving, UndecidableInstances
> #-}

%endif

> module MF.Function.Close where

> import MF.Expr.Syn
> import MF.Terminals.Values
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

> import Data.Map

> data SemFunc eif eor top neg and comp ecu fdef pnil psnoc op var val call=
>   SemFunc { seif   :: eif,
>             seor   :: eor,
>             stop   :: top,
>             sneg   :: neg,
>             sand   :: and,
>             scomp_ :: comp,
>             sfdef  :: fdef,
>             secu   :: ecu,
>             spnil  :: pnil,
>             spsnoc  :: psnoc,
>             sexpr  :: (SemExpr op var val call)
>           }


> data FDef v
>   = FDef String (Ecu v)

> data Ecu v
>   = Ecu Vars (ExprG v)

> data ExprG v
>   = Or (Expr v)
>   | If  (Expr v) (Cond v) (ExprG v)

> data Cond v
>   = Top
>   | Comp (Expr v) Ordering (Expr v)
>   | And (Cond v) (Cond v)
>   | Neg (Cond v)

> data Program v = PNil | PSnoc (Program v) (FDef v)

> deriving instance (Show v, Show (Val2Op v)) => Show (Cond v)
> deriving instance (Show v, Show (Val2Op v)) => Show (FDef v)
> deriving instance (Show v, Show (Val2Op v)) => Show (Ecu v)
> deriving instance (Show v, Show (Val2Op v)) => Show (ExprG v)
> deriving instance (Show v, Show (Val2Op v)) => Show (Program v)

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

> sem_Program sem p@(PNil :: Program v)
>   = sem_Program_PNil (spnil sem (proxyFrom p))
> sem_Program sem pr@(PSnoc p f)
>   = sem_Program_PSnoc (spsnoc sem (proxyFrom pr)) (sem_Program sem p)(sem_FDef sem f)

> -- compileCond :: Cond Val -> CTerm Op Val
> -- compileCond c = sem_Cond semCompFunc c emptyAtt #. (scomp @Val)

 > compileExprG :: ExprG Val -> CTerm Op Val
 > compileExprG i = sem_ExprG semCompFunc i emptyAtt #. (scomp @Val)


> compileProgram :: Program Val -> Map String (CTerm Op Val)
> compileProgram p = sem_Program semCompFunc p emptyAtt #. (spcomp @Val)

> sem_ExprG sem e@(Or e')
>   = sem_ExprG_EOr (seor sem (proxyFrom e)) (sem_Expr (sexpr sem) e')
> sem_ExprG sem e@(If e' c e'')
>   = sem_ExprG_EIf (seif sem (proxyFrom e))
>                   (sem_Expr (sexpr sem) e')
>                   (sem_Cond sem c)
>                   (sem_ExprG sem e'')

> sem_Ecu sem e@(Ecu vs b) =
>   sem_Ecu_Ecu (secu sem (proxyFrom e)) vs (sem_ExprG sem b)

> sem_FDef sem f@(FDef x ecu) =
>   sem_FDef_FDef (sfdef sem (proxyFrom f)) x (sem_Ecu sem ecu)

> semCompFunc =
>   SemFunc scomp_eif scomp_eor scomp_top scomp_neg scomp_and  scomp_comp
>   sfcomp_fdef scomp_ecu spcomp_nil spcomp_snoc semCompExpr


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
>   = buildExpressionParser (tableCond sfun p) (pCondAux sfun p)
>    <?> "condition"

> tableCond sfun p =
>   [[P.Prefix (m_reservedOp "~" >> return (sem_Cond_Neg (sneg sfun p)))],
>    [P.Infix (m_reservedOp "&" >> return (sem_Cond_And (sand sfun p))) AssocLeft]
>   ]


> exampleProgram = PSnoc (PSnoc (PSnoc PNil
>   (FDef "fac" (Ecu ["n"] (If (Val (mki 1))
>                             (Comp (Var "n")
>                                   LT
>                                   (Val (mki 1)))
>                          (Or (Op (Var "n")
>                                  Times
>                              (Call "fac" (Op (Var "n")
>                                              Add
>                                              (Val (mki (-1)) ))))))))
>   )
>   (FDef "inv" (Ecu ["x"] (Or (Op (Val (mki 1)) Div (Var "x")))))
>   )
>   (FDef "succ" (Ecu ["n"] (Or (Op (Val (mki 1)) Add (Var "n")))))


> pEIfDT = do
>   e <- pExprDT
>   m_reserved "if"
>   c <- pCondDT
>   m_reserved "or"
>   tl <- choice [try pEIfDT, pEOrDT]
>   return $ If e c tl

> pEOrDT = do
>   e <- pExprDT
>   return $ Or e

> pTopDT = do
>   m_reserved "T"
>   return $ Top

> pNegDT = do
>   m_reserved "~"
>   c <- pCondDT
>   return $ Neg c

> pAndDT = do
>   l <- pCondDT
>   m_reserved "&"
>   r <- pCondDT
>   return $ And l r

> pOpDT = choice [m_symbol "<" >> return LT,
>                 m_symbol ">" >> return GT,
>                 m_symbol "==" >> return EQ
>                  ]

> pCompDT = do
>   l   <- pExprDT
>   op  <- pOpDT
>   r   <- pExprDT
>   return $ Comp l op r


> pCondAuxDT = pTopDT <|> pCompDT 
>                <|> m_parens (pCondAuxDT)
>                <|> pCondDT

> pCondDT 
>   = buildExpressionParser (tableCondDT) (pCondAuxDT)
>    <?> "condition"

> tableCondDT=
>   [[P.Prefix (m_reservedOp "~" >> return (Neg))],
>    [P.Infix (m_reservedOp "&" >> return (And)) AssocLeft]
>   ]


> pEcu = do
>   args  <- pArgs
>   m_symbol "="
>   rhs   <- choice [try pEIfDT, pEOrDT]
>   return $ Ecu args rhs

> pFuncDT = do
>   fname <- m_identifier
>   ecu  <- pEcu
>   return $ FDef fname ecu


> pArgs = do
>   m_symbol "("
>   x <- m_identifier
>   xs <- pArgList
>   m_symbol ")"
>   return (x:xs)

> pArgList =
>   choice [many1 (m_symbol "," >> m_identifier), return []]


> pProgram = Prelude.foldl (\p f -> PSnoc p f) PNil <$> many1 pFuncDT


> readProgram nam = readFile nam >>= \f ->
>   return $  parse (pProgram <* eof) nam f


> repl f = do
>   p <- readProgram f
>   case p of
>     Left e  -> print e
>     Right p -> do
>       let env = compileProgram p
>       loop env
>   where
>     loop env = do
>      l <- getLine
>      if (l=="quit") then return ()
>      else
>       case parse (pExprDT <* eof) "repl" l of
>        Left e  -> print "error" >> loop env
>        Right e -> print (reduce env (compileExpr e)) >> loop env
