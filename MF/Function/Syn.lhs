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

> module MF.Function.Syn where
> import MF.Expr.Syn
> import Expr.Syn

> import Language.Grammars.AspectAG
> import Data.Ord
> import Data.Proxy

> type Nt_ExprG = 'NT "ExprG"
> type P_EOr = 'Prd "EOr" Nt_ExprG
> p_EOr = Label @ P_EOr
> ch_EOr_or = Label @('Chi "EOr_or" P_EOr (NonTerminal Nt_Expr))

> type P_EIf = 'Prd "EIf" Nt_ExprG
> p_EIf = Label @ P_EIf
> ch_EIf_if    = Label @('Chi "EIf_if"    P_EIf (NonTerminal Nt_Expr))
> ch_EIf_cond  = Label @('Chi "EIf_cond"  P_EIf (NonTerminal Nt_Cond))
> ch_EIf_else  = Label @('Chi "EIf_else"  P_EIf (NonTerminal Nt_ExprG))

> type Nt_Cond  = 'NT "Cond"
> type P_Top    = 'Prd "Top" Nt_Cond
> p_Top         = Label @ P_Top
> ch_Top        = Label @ ('Chi "Top" P_Top (Terminal ()))

> type P_Neg  = 'Prd "Neg" Nt_Cond
> p_Neg       = Label @ P_Neg
> ch_Neg_e    = Label @ ('Chi "Neg_e" P_Neg (NonTerminal Nt_Cond))

> type P_And  = 'Prd "And" Nt_Cond
> p_And       = Label @ P_And
> ch_And_l    = Label @ ('Chi "And_l"  P_And (NonTerminal Nt_Cond))
> ch_And_r    = Label @ ('Chi "And_r"  P_And (NonTerminal Nt_Cond))

> type P_Comp  = 'Prd "Comp" Nt_Cond
> p_Comp       = Label @ P_Comp
> ch_Comp_l    = Label @ ('Chi "Comp_l"   P_Comp (NonTerminal  Nt_Expr))
> ch_Comp_op   = Label @ ('Chi "Comp_op"  P_Comp (Terminal     Ordering))
> ch_Comp_r    = Label @ ('Chi "Comp_r"   P_Comp (NonTerminal  Nt_Expr))

> type Nt_Ecu = 'NT "Ecu"
> type P_Ecu  = 'Prd "Ecu" Nt_Ecu
> p_Ecu = Label @ P_Ecu

> type Vars = [String]
> ch_Ecu_vars = Label @ ('Chi "Ecu_vars" P_Ecu (Terminal Vars))
> ch_Ecu_body = Label @ ('Chi "Ecu_Body" P_Ecu (NonTerminal Nt_ExprG))

> type Nt_FDef = 'NT "FDef"
> type P_FDef = 'Prd "FDef" Nt_FDef
> p_FDef = Label @ P_FDef
> ch_FDef_name = Label @('Chi "FDef_name" P_FDef (Terminal String))
> ch_FDef_ecu =  Label @('Chi "FDef_ecu" P_FDef (NonTerminal Nt_Ecu))

> type Nt_Program = 'NT "Program"
> type P_ProgramSnoc = 'Prd "ProgramSnoc" Nt_Program
> p_ProgramSnoc = Label @ P_ProgramSnoc
> type P_ProgramNil  = 'Prd "ProgramNil" Nt_Program
> p_ProgramNil = Label @ P_ProgramNil

> ch_ProgramSnoc_last
>   = Label @ ('Chi "ProgramSnoc_last" P_ProgramSnoc (NonTerminal Nt_FDef))
> ch_ProgramSnoc_init
>   = Label @ ('Chi "ProgramSnoc_init" P_ProgramSnoc (NonTerminal Nt_Program))
> ch_ProgramNil
>   = Label @ ('Chi "ProgramSnoc_nil" P_ProgramNil (Terminal ()))

> sem_ExprG_EIf asp fif fcond felse =
>   knit Proxy asp (
>   ch_EIf_if .=. fif .*.
>   ch_EIf_cond .=. fcond .*.
>   ch_EIf_else .=. felse .*.
>   emptyGenRec
>   )

> sem_ExprG_EOr asp for =
>   knit Proxy asp (
>   ch_EOr_or .=. for .*.
>   emptyGenRec
>   )

> sem_Cond_Top asp {-- ft --} =
>   knit Proxy asp emptyGenRec -- (ch_Top .=. ft .*. emptyGenRec)

> sem_Cond_Neg asp fe =
>   knit Proxy asp (
>      ch_Neg_e .=. fe .*. emptyGenRec
>   )

> sem_Cond_And asp fl fr =
>   knit Proxy asp (
>   ch_And_l .=. fl .*.
>   ch_And_r .=. fr .*.
>   emptyGenRec
>    )

> sem_Cond_Comp asp fl fop fr =
>   knit Proxy asp (
>   ch_Comp_l .=. fl .*.
>   ch_Comp_op .=. sem_Lit fop .*.
>   ch_Comp_r .=. fr .*.
>   emptyGenRec
>    )

> sem_Ecu_Ecu asp fv fe =
>   knit Proxy asp (
>     ch_Ecu_vars .=. sem_Lit fv .*.
>     ch_Ecu_body .=. fe .*.
>     emptyGenRec
>   )

> sem_FDef_FDef asp fn fe = 
>   knit Proxy asp (
>     ch_FDef_name .=. sem_Lit fn .*.
>     ch_FDef_ecu .=. fe .*.
>     emptyGenRec
>   )


> sem_Program_PNil asp =
>   knit Proxy asp emptyGenRec

> sem_Program_PSnoc asp fs f =
>   knit Proxy asp (
>     ch_ProgramSnoc_init .=. fs .*.
>     ch_ProgramSnoc_last .=. f .*. 
>   emptyGenRec)
