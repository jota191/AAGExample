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

\section{Semantics definition}
\label{sec:semanticsdefinition}

With the aim to provide semantics, AGs decorate the productions of
context-free grammars with attribute computations. In the expression
language as the one defined, the usual semantics are given by the
evaluation semantics. This can be defined by using two attributes:
|eval|, to represent the result of the evaluation, and |env|, to
distribute the environment containing the values for variables. In
this section we explain how the evaluation semantics can be
implemented using our library. All the source code of this section is
part of the {\tt MF.Sem} module.

%if False

> module Expr.Eval where
> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH
> import Expr.Syn
> import Data.Proxy
> import GHC.TypeLits
> import Data.Kind
> import Data.Map as M

%endif


Attributes in \AspectAG are also defined as |Label|s. They have
attached the type of the computation that they represent.

> eval  = Label @ ('Att "eval"  Integer)
> env   = Label @ ('Att "env"   Env)

The attribute |eval| computes a value of type |Integer|. The attribute
|env| computes an environment of type |Env|.

The environment contains the value of
the variables in a scope. We use the |Map| datatype provided by the
GHC's {\tt base} library (qualified as |M|):

> type Env = M.Map String Integer

There is no information pointing that |eval| and |env| are respecively
a synthesized and inherited attributes. In \AspectAG attributes are
declared and can be used in principle with any role.

Now we can build the proper rules. To compute the attribute |eval| in
the production |p_Add| we take the values of |eval|, wich are the integers
denotated by the subexpressions, and sum them up. This is written as
follows:

> add_eval  =
>   syndefM eval p_Add
>     $    (+) @Integer
>     <$>  at ch_Add_l eval
>     <*>  at ch_Add_r eval

Attribute eval is defined using function |syndefM|, which is the
library operation to define synthesized attributes. It takes an
attribute (the one for which the semantics is being defined), a
production (where it is being defined), and the respective computation
rule for the attribute.

Using an applicative interface, we take the values of the |eval|
attibute at children |ch_Add_l| and |ch_Add_r|, and combine them with the
operator (+). In the expression |at ch_Add_l eval| (|at ch_Add_r eval|) we
pick up the attribute |eval| from the collection of synthesized
attributes of the child |ch_Add_l| (|ch_Add_r|). We refer to these collections
of attributes as attributions.

This definition expects that the |eval| attribute is defined in those
subexpressions. This is explicit on its type as a constraint. Rules
keep at type level all the information of which attributes are
computed, and which children are used. All the structure of the
grammar is known at compile time, which is used to compute precise
errors, for instance if a subexpression has no rule to compute |eval|,
a suitable type error will be rised, as we shall see later.

[MOSTRAR UN TIPO?]

In the case of literals, semantics are given by the integer that the
literal denotes. This is defined as follows:

> val_eval  =
>   syndefM eval p_Val (ter ch_Val_val)

At the |p_Val| production the value of the terminal corresponds to the
semantics of the expression. In terms of our implementation the
attribute |eval| is defined as the value of the terminal
|ch_Val_val|. The term |ter| is simply a reserved keyword in our EDSL.

Finally, with variables, the |eval| attribute is computed looking up
the environment.

> var_eval  =
>   syndefM eval p_Var (
>   do env  <- at lhs env
>      x    <- ter ch_Var_var
>      case M.lookup x env of
>        Just e -> return e
>   )

We take the inherited environment, and the variable name. Then we
lookup for the value associated to that name.  Here we use the do
notation, i.e. a monadic interface. The name |lhs| is a reserved word
like |ter| indicating that we receive the |env| attribute from the
parent\footnote{the lhs name in idiom widely used in AG systems. Note
  that parents are on the left hand side of the production in the EBNF
  notation}.

The reader could be concerned as the pattern matching we do in the
result of the lookup is not exhaustive. In fact if the environment
does not contain the variable we are looking for this would generate a
runtime failure. For brevity we will not handle name binding in this
example language. But it can be handled with another attribute, in an
orthogonal way (for instance, in a new, independent module). This new
computations could be combined with the evaluator to perform only one
traverse over the abstract syntax tree, and lazy evaluation would
prevent the evaluation of this pattern match.



We can combine all these rules in an \emph{aspect}:

> asp_eval = traceAspect (Proxy @ ('Text "eval")) $
>     add_eval .+: val_eval .+: var_eval .+: emptyAspect


The operator |(.+:)| is a combinator that adds a rule to an aspect (it
associates to the right). An aspect is a collection of rules. Here we
build an aspect with all the rules for a given attribute, but the user
can combine them in the way she wants (for example, by production).
Aspects can be orthogonal among them, or not.

Aspects keep all the information of which attributes are computed, and
which children are used, taken from the rules used to build them. All
the structure of the grammar is known at compile time, which is used
to compute precise errors.

The function |traceAspect| and also -implicitly- each application of
|syndefM| tag definitions to show more information on type
errors. This is useful to have a hint where the error was actually
introduced. For instance, note that that |asp_eval| clearly depends on
an attribute |env| with no rules attached to it at this point, so it
is not -yet- useful at all. We cannot decide locally that the
definition is wrong since the rules for |env| could be defined later
(as we will do), or perhaps in another module!  If we actually use
|asp_eval| calling it on a semantic function there will be a type
error but it will be raised on the semantic function
application. Programmers not used to library internals could find this
misleading. Showing the trace is helpful in those scenarios as we will
see in [REF]. A function |traceRule| is also provided so the user can
apply it to rules instead of aspects. Actually |traceAspect| is a sort
of mapping of |traceRule| in every rule contained in the aspect.

To define the inherited attibute |env| we use de |inhdef|
combinator. It takes three labels: an attribute, a production where
the rule is being defined, and a children to which the information is
being distributed. Then, the rule is defined. In our example we define
rules |add_env_l| and |add_env_r| to copy the environment to children
in the case of additions:

> add_env_l =
>   inhdefM env p_Add ch_Add_l (at lhs env)

> add_env_r =
>   inhdefM env p_Add ch_Add_r (at lhs env)

Then, we can combine those rules in an aspect. We add trace
information again.

> asp_env = traceAspect (Proxy @('Text "env")) $
>         add_env_l .+: add_env_r .+: emptyAspect


Finally we can combine aspects |asp_eval| and |asp_env|. For that
puropose \AspectAG provides the |(.:+:)| operator.

> asp_sem = asp_eval .:+: asp_env

Note that in this case no new tag was added to the trace, but we could.

Finally we can implement the evaluation function. Let us work with the
forestated approach, taking an |Expr| tree as an argument:

> evaluator :: Expr -> Env -> Integer
> evaluator exp envi =
>  sem_Expr asp_sem exp (env =. envi *. emptyAtt) #. eval

|sem_Expr| takes the semantic definition and an |Expr|ession to build
a semantic function. Semantic functions take an attribution (inherited
attributes for the expression) and return an attribution (synthesized
attributes). |env =. envi *. emptyAtt| is the initial synthesized
attribution, consisting in only one attribute, |eval| with the value
of |env|. The expression |env =. envi| is building an attribute while
|(*.)| is a cons-like operator. So the application
|sem_Expr asp_sem exp (env =. envi *. emptyAtt)|
computes to the synthesized attributes of the expression. In this case
it is an attribution with only one attribute |eval| containing the
result of the computation. The operator |(#.)| extracts it.

%if False

> sampleEnvAtt = env =. [("x",(4::Int))] *. emptyAtt

3 + x, deforestated

> asp_add = add_env_l .+: add_env_r .+: add_eval .+: emptyAspect
> asp_val = val_eval .+: emptyAspect
> asp_var = var_eval .+: emptyAspect

> asp_all = asp_add .:+: asp_val .:+: asp_var .:+: emptyAspect


%endif
