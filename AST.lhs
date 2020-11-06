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

> module AST where
> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH


> $(addNont "Expr")

< nt_Expr = Label :: Label ('NT "Expr")
< type Nt_Expr = 'NT "Expr"

> $(addProd "Val" ''Nt_Expr [("val", Ter ''Int)])

< type P_Val = 'Prd "Val" Nt_Expr
< p_Val = Label :: Label ('Prd "Val" Nt_Expr)
< instance Prods Nt_Expr "Val" '[ '("v", "Int")]
< ch_v = Label :: Label ('Chi "v" P_Val (Terminal Int))


> $(addProd "Var" ''Nt_Expr [("var", Ter ''String)])

    type P_Var = 'Prd "Var" Nt_Expr
    p_Var = Label :: Label ('Prd "Var" Nt_Expr)
    instance Prods Nt_Expr "Var" '[ '("var", "String")]
    ch_var = Label :: Label ('Chi "var" P_Var (Terminal String))


> $(addProd "Add" ''Nt_Expr [("l", NonTer ''Nt_Expr),
>                            ("r", NonTer ''Nt_Expr)])

< type P_Add = 'Prd "Add" Nt_Expr
< p_Add = Label :: Label ('Prd "Add" Nt_Expr)
< instance Prods Nt_Expr "Add" '[ '("l", "Nt_Expr"),
<                                 '("r", "Nt_Expr")]
< ch_l = Label :: Label ('Chi "l" P_Add (NonTerminal Nt_Expr))
< ch_r = Label :: Label ('Chi "r" P_Add (NonTerminal Nt_Expr))

> $(closeNT ''Nt_Expr)

> $(mkSemFunc ''Nt_Expr)


    data Expr
      = Add {l :: Expr, r :: Expr} |
        Var {var :: String} |
        Val {val :: Int}
      deriving (Show, Eq, Read)

    sem_Expr asp (Add l r)
      = ((knitAspect p_Add) asp)
          (((.*.) (((.=.) ch_l) ((sem_Expr asp) l)))
             (((.*.) (((.=.) ch_r) ((sem_Expr asp) r))) emptyGenRec))
    sem_Expr asp (Var var)
      = ((knitAspect p_Var) asp)
          (((.*.) (((.=.) ch_var) (sem_Lit var))) emptyGenRec)
    sem_Expr asp (Val val)
      = ((knitAspect p_Val) asp)
          (((.*.) (((.=.) ch_val) (sem_Lit val))) emptyGenRec)

> sem_Expr_Add asp sl sr =
>  knitAspect p_Add asp $
>  ch_l .=. sl asp .*.
>  ch_r .=. sr asp .*. emptyGenRec

-- > sem_Expr_Var asp var =
-- >   knitAspect p_Var asp $
-- >   ch_var .=. sem_Lit @ String var .*. emptyGenRec

> sem_Expr_Val asp (val :: Int) =
>   knitAspect p_Val asp $
>   ch_val .=. sem_Lit @ Int val .*. emptyGenRec
