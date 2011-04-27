-- | Parsing and printing SMT-LIB.
module Language.SMTLIB
  (
  -- * Syntax
    Numeral
  , Symbol
  , Keyword
  , Spec_constant        (..)
  , S_expr               (..)
  , Identifier           (..)
  , Sort                 (..)
  , Attribute_value      (..)
  , Attribute            (..)
  , Qual_identifier      (..)
  , Var_binding          (..)
  , Sorted_var           (..)
  , Term                 (..)
  , Sort_symbol_decl     (..)
  , Meta_spec_constant   (..)
  , Fun_symbol_decl      (..)
  , Par_fun_symbol_decl  (..)
  , Theory_attribute     (..)
  , Theory_decl          (..)
  , Logic_attribute      (..)
  , Logic                (..)
  , Option               (..)
  , Info_flag            (..)
  , Command              (..)
  , Script               (..)
  , Gen_response         (..)
  , Error_behavior       (..)
  , Reason_unknown       (..)
  , Status               (..)
  , Info_response        (..)
  , Proof
  , Valuation_pair
  , T_valuation_pair
  , Command_response     (..)
  -- * Parsing
  , parseScript
  , parseResponses
  , parseTheory
  , parseLogic
  -- * Parsing Verification
  , checkScript
  , checkResponses
  , checkParser
  -- * For Hind
  , parseScriptFile
  , commandResponseSource
  )

  where

import Data.List hiding (group)
import System.Directory
import System.IO
import Control.Monad(unless)

import Text.Printf
import Control.Applicative hiding (many)

import qualified Data.ByteString.Char8 as B
import Data.Attoparsec hiding (string,option)
import qualified Data.Attoparsec as Atto
import qualified Data.Attoparsec.Char8 as C

import Data.Attoparsec.Iteratee
import Data.Iteratee hiding (group,length)
import Data.Iteratee.IO.Handle(enumHandle)
import Control.Exception
import Control.Monad.Trans




type Numeral      = Integer
type Symbol       = String
type Keyword      = String

data Spec_constant
  = Spec_constant_numeral     Numeral
  | Spec_constant_decimal     Rational
  | Spec_constant_hexadecimal String
  | Spec_constant_binary      [Bool]
  | Spec_constant_string      String

instance Show Spec_constant where
  show a = case a of
    Spec_constant_numeral     a -> show a
    Spec_constant_decimal     a -> show (realToFrac a :: Double)
    Spec_constant_hexadecimal a -> printf "#x%s" a
    Spec_constant_binary      a -> printf "bvbin%s[%d]" [ if a then '1' else '0' | a <- a ] (length a)
    Spec_constant_string      a -> show a

spec_constant :: SMTLIB Spec_constant
spec_constant = choice
  [ Spec_constant_numeral <$> numeral
  , Spec_constant_string <$> string
    -- FIXME: Should I really be using double?
  , Spec_constant_decimal . toRational  <$> C.double
    -- TODO: Handle Hexadecimal and Binary.
    -- , Spec_constant_hexadecimal <$> hexadecimal
    -- , Spec_constant_binary <$> hexadecimal
  ]

data S_expr
  = S_expr_constant Spec_constant
  | S_expr_symbol   Symbol
  | S_expr_keyword  Keyword
  | S_exprs         [S_expr]

instance Show S_expr where
  show a = case a of
    S_expr_constant a -> show a
    S_expr_symbol   a -> a
    S_expr_keyword  a -> a
    S_exprs         a -> group $ map show a


s_expr :: SMTLIB S_expr
s_expr = choice
  [ S_expr_constant <$> spec_constant
  , S_expr_symbol <$> symbol
  , S_expr_keyword <$> keyword
  , (left *> (S_exprs <$>  many s_expr) <* right)
  ]

data Identifier
  = Identifier  Symbol
  | Identifier_ Symbol [Numeral]

instance Show Identifier where
  show a = case a of
    Identifier  a -> a
    Identifier_ a b -> group $ ["_", a] ++ map show b

identifier :: SMTLIB Identifier
identifier = choice
  [ Identifier <$> symbol
  , left *> C.char  '_' *> (Identifier_ <$> symbol <*>  many1 numeral) <* right
  ]


data Sort
  = Sort_bool
  | Sort_identifier  Identifier
  | Sort_bitvec Numeral
  | Sort_identifiers Identifier [Sort]

instance Show Sort where
  show a = case a of
    Sort_bool -> "Bool"
    -- Z3 specific bitvec syntax
    Sort_bitvec size -> "BitVec[" ++ show size ++ "]"
    Sort_identifier  a -> show a
    Sort_identifiers a b -> group $ show a : map show b


sort' :: SMTLIB Sort
sort' = choice
  [ tok "Bool" >> return Sort_bool
  ,
    -- For z3 specific bitvec syntax.
    tok "BitVec" *> leftBracket *> (Sort_bitvec <$> numeral) <* rightBracket
  , Sort_identifier <$>  identifier
  , left *> (Sort_identifiers <$> identifier <*>  many1 sort') <* right
  ]

data Attribute_value
  = Attribute_value_spec_constant Spec_constant
  | Attribute_value_symbol        Symbol
  | Attribute_value_s_expr        [S_expr]

instance Show Attribute_value where
  show a = case a of
    Attribute_value_spec_constant a -> show a
    Attribute_value_symbol        a -> a
    Attribute_value_s_expr        a -> group $ map show a

attribute_value :: SMTLIB Attribute_value
attribute_value = choice
  [ Attribute_value_spec_constant <$> spec_constant
  , Attribute_value_symbol <$> symbol
  , left *> (Attribute_value_s_expr <$> many s_expr) <* right
  ]


data Attribute
  = Attribute        Keyword
  | Attribute_s_expr Keyword S_expr

instance Show Attribute where
  show a = case a of
    Attribute        a -> a
    Attribute_s_expr a b -> a ++ " " ++ show b

attribute :: SMTLIB Attribute
attribute = choice
  [ Attribute_s_expr <$> keyword <*> s_expr
  , Attribute <$> keyword
  ]

data Qual_identifier
  = Qual_identifier      Identifier
  | Qual_identifier_sort Identifier Sort

instance Show Qual_identifier where
  show a = case a of
    Qual_identifier      a -> show a
    Qual_identifier_sort a b -> group ["as", show a, show b]

qual_identifier :: SMTLIB Qual_identifier
qual_identifier = choice
  [ Qual_identifier <$> identifier
  , left *>  tok "as" *> (Qual_identifier_sort <$> identifier <*>  sort') <* right

  ]


data Var_binding
  = Var_binding Symbol Term

instance Show Var_binding where
  show a = case a of
    Var_binding a b -> group [a, show b]

var_binding :: SMTLIB Var_binding
var_binding = parens (Var_binding <$> symbol <*> term)


data Sorted_var
  = Sorted_var Symbol Sort

instance Show Sorted_var where
  show a = case a of
    Sorted_var a b -> group [a, show b]

sorted_var :: SMTLIB Sorted_var
sorted_var = parens (Sorted_var <$> symbol <*> sort')

data Term
  = Term_spec_constant    Spec_constant
  | Term_qual_identifier  Qual_identifier
  | Term_qual_identifier_ Qual_identifier [Term]
  | Term_distinct         Term [Term]
  | Term_let              [Var_binding] Term
  | Term_forall           [Sorted_var] Term
  | Term_exists           [Sorted_var] Term
  | Term_attributes       Term [Attribute]

instance Show Term where
  show a = case a of
    Term_spec_constant    a -> show a
    Term_qual_identifier  a -> show a
    Term_qual_identifier_ a b -> group $ show a : map show b
    Term_distinct         a b -> group $ ["distinct", show a] ++ map show b
    Term_let              a b -> group $ ["let",    group $ map show a, show b]
    Term_forall           a b -> group $ ["forall", group $ map show a, show b]
    Term_exists           a b -> group $ ["exists", group $ map show a, show b]
    Term_attributes       a b -> group $ ["!", show a] ++ map show b


term :: SMTLIB Term
term = choice
  [ Term_spec_constant <$> spec_constant
  , Term_qual_identifier <$> qual_identifier
  , parens (Term_qual_identifier_ <$> qual_identifier <*> many term)
  , parens (tok "distinct" *> (Term_distinct <$> term <*> many1 term))
  , parens (tok "let" *> (Term_let <$> (parens (many1 var_binding)) <*> term))
  , parens (tok "forall" *> (Term_forall <$> (parens (many1 sorted_var)) <*> term))
  , parens (tok "exists" *> (Term_exists <$> (parens (many1 sorted_var)) <*> term))
  , parens (C.char '!' *> (Term_attributes <$> term <*> many1 attribute))
  ]



data Sort_symbol_decl
  = Sort_symbol_decl Identifier Numeral [Attribute]

instance Show Sort_symbol_decl where
  show a = case a of
    Sort_symbol_decl a b c -> group $ [show a, show b] ++ map show c

sort_symbol_decl :: SMTLIB Sort_symbol_decl
sort_symbol_decl =
  parens (Sort_symbol_decl <$> identifier <*> numeral <*> many attribute)


data Meta_spec_constant
  = Meta_spec_constant_numeral
  | Meta_spec_constant_decimal
  | Meta_spec_constant_string

instance Show Meta_spec_constant where
  show a = case a of
    Meta_spec_constant_numeral -> "NUMERAL"
    Meta_spec_constant_decimal -> "DECIMAL"
    Meta_spec_constant_string  -> "STRING"

meta_spec_constant :: SMTLIB Meta_spec_constant
meta_spec_constant = choice
  [ do { tok "NUMERAL"; return Meta_spec_constant_numeral }
  , do { tok "DECIMAL"; return Meta_spec_constant_decimal }
  , do { tok "STRING" ; return Meta_spec_constant_string  }
  ]

data Fun_symbol_decl
  = Fun_symbol_decl_spec_constant      Spec_constant      Sort [Attribute]
  | Fun_symbol_decl_meta_spec_constant Meta_spec_constant Sort [Attribute]
  | Fun_symbol_decl                    Identifier [Sort] [Attribute]

instance Show Fun_symbol_decl where
  show a = case a of
    Fun_symbol_decl_spec_constant      a b c -> group $ [show a, show b] ++ map show c
    Fun_symbol_decl_meta_spec_constant a b c -> group $ [show a, show b] ++ map show c
    Fun_symbol_decl                    a b c -> group $ [show a] ++ map show b ++ map show c

fun_symbol_decl :: SMTLIB Fun_symbol_decl
fun_symbol_decl = choice
  [parens (Fun_symbol_decl_spec_constant <$> spec_constant <*> sort' <*> many attribute)
  , parens (Fun_symbol_decl_meta_spec_constant <$>
              meta_spec_constant <*> sort' <*> many attribute)

  ,parens (Fun_symbol_decl <$> identifier <*> many1 sort' <*> many attribute)
  ]


data Par_fun_symbol_decl
  = Par_fun_symbol_decl Fun_symbol_decl
  | Par_fun_symbol_decl_symbols [Symbol] Identifier [Sort] [Attribute]

instance Show Par_fun_symbol_decl where
  show a = case a of
    Par_fun_symbol_decl a -> show a
    Par_fun_symbol_decl_symbols a b c d -> group ["par", group $ map show a, group $ [show b] ++ map show c ++ map show d]

par_fun_symbol_decl :: SMTLIB Par_fun_symbol_decl
par_fun_symbol_decl = choice
  [ Par_fun_symbol_decl <$> fun_symbol_decl
  , parens (tok "par" *>
     (Par_fun_symbol_decl_symbols <$> (parens $ many1 symbol) <*>
                                   (left *> identifier) <*>
                                   many1 sort' <*>
                                   (many attribute <* right)))
  ]


data Theory_attribute
  = Theory_attribute_sorts [Sort_symbol_decl]
  | Theory_attribute_funs  [Par_fun_symbol_decl]
  | Theory_attribute_sorts_desc String
  | Theory_attribute_funs_desc  String
  | Theory_attribute_definition String
  | Theory_attribute_values     String
  | Theory_attribute_notes      String
  | Theory_attribute            Attribute

instance Show Theory_attribute where
  show a = case a of
    Theory_attribute_sorts      a -> ":sorts " ++ group (map show a)
    Theory_attribute_funs       a -> ":funs "  ++ group (map show a)
    Theory_attribute_sorts_desc a -> ":sorts-description " ++ show a
    Theory_attribute_funs_desc  a -> ":funs-description "  ++ show a
    Theory_attribute_definition a -> ":definition "        ++ show a
    Theory_attribute_values     a -> ":values "            ++ show a
    Theory_attribute_notes      a -> ":notes "             ++ show a
    Theory_attribute            a -> show a

theory_attribute :: SMTLIB Theory_attribute
theory_attribute = choice
  [ do { kw "sorts"; left; a <- many1 sort_symbol_decl; right; return $ Theory_attribute_sorts a }
  , do { kw "funs";  left; a <- many1 par_fun_symbol_decl; right; return $ Theory_attribute_funs a }
  , do { kw "sorts-description"; a <- string; return $ Theory_attribute_sorts_desc a }
  , do { kw ":funs-description"; a <- string; return $ Theory_attribute_funs_desc a }
  , do { kw ":definition"; a <- string; return $ Theory_attribute_definition a }
  , do { kw ":values"; a <- string; return $ Theory_attribute_values a }
  , do { kw ":notes"; a <- string; return $ Theory_attribute_notes a }
  , attribute >>= return . Theory_attribute
  ]

data Theory_decl
  = Theory_decl Symbol [Theory_attribute]

instance Show Theory_decl where
  show a = case a of
    Theory_decl a b -> group $ ["theory", show a] ++ map show b

theory_decl :: SMTLIB Theory_decl
theory_decl =
  parens $ tok "theory" *> (Theory_decl <$> symbol  <*> many theory_attribute)



data Logic_attribute
  = Logic_attribute_theories   [Symbol]
  | Logic_attribute_language   String
  | Logic_attribute_extensions String
  | Logic_attribute_values     String
  | Logic_attribute_notes      String
  | Logic_attribute            Attribute

instance Show Logic_attribute where
  show a = case a of
    Logic_attribute_theories    a -> ":theories " ++ group (map show a)
    Logic_attribute_language    a -> ":language "   ++ show a
    Logic_attribute_extensions  a -> ":extensions " ++ show a
    Logic_attribute_values      a -> ":values "     ++ show a
    Logic_attribute_notes       a -> ":notes "      ++ show a
    Logic_attribute             a -> show a

logic_attribute :: SMTLIB Logic_attribute
logic_attribute = choice
  [ do { kw "theories"; left; a <- many1 symbol; right; return $ Logic_attribute_theories a }
  , do { kw "language"; left; a <- string; right; return $ Logic_attribute_language a }
  , do { kw "extensions"; left; a <- string; right; return $ Logic_attribute_extensions a }
  , do { kw "values"; left; a <- string; right; return $ Logic_attribute_values a }
  , do { kw "notes"; left; a <- string; right; return $ Logic_attribute_notes a }
  , attribute >>= return . Logic_attribute
  ]

data Logic
  = Logic Symbol [Logic_attribute]

instance Show Logic where
  show a = case a of
    Logic a b -> group $ ["logic", a] ++ map show b

logic :: SMTLIB Logic
logic = do { left; tok "logic"; a <- symbol; b <- many1 logic_attribute; right; return $ Logic a b }

data Option
  = Print_success       Bool
  | Expand_definitions  Bool
  | Interactive_mode    Bool
  | Produce_proofs      Bool
  | Produce_unsat_cores Bool
  | Produce_models      Bool
  | Produce_assignments Bool
  | Regular_output_channel String
  | Diagnostic_output_channel String
  | Random_seed Int
  | Verbosity Int
  | Option_attribute Attribute

instance Show Option where
  show a = case a of
    Print_success             a -> ":print-success "             ++ showBool a
    Expand_definitions        a -> ":expand-definitions "        ++ showBool a
    Interactive_mode          a -> ":interactive-mode "          ++ showBool a
    Produce_proofs            a -> ":produce-proofs "            ++ showBool a
    Produce_unsat_cores       a -> ":produce-unsat-cores "       ++ showBool a
    Produce_models            a -> ":produce-models "            ++ showBool a
    Produce_assignments       a -> ":produce-assignments "       ++ showBool a
    Regular_output_channel    a -> ":regular-output-channel "    ++ show a
    Diagnostic_output_channel a -> ":diagnostic-output-channel " ++ show a
    Random_seed               a -> ":random-seed "               ++ show a
    Verbosity                 a -> ":verbosity "                 ++ show a
    Option_attribute          a -> show a

option :: SMTLIB Option
option = choice
  [ do { tok ":print-success";       a <- b_value; return $ Print_success       a }
  , do { tok ":expand-definitions";  a <- b_value; return $ Expand_definitions  a }
  , do { tok ":interactive-mode";    a <- b_value; return $ Interactive_mode    a }
  , do { tok ":produce-proofs";      a <- b_value; return $ Produce_proofs      a }
  , do { tok ":produce-unsat-cores"; a <- b_value; return $ Produce_unsat_cores a }
  , do { tok ":produce-models";      a <- b_value; return $ Produce_models      a }
  , do { tok ":produce-assignments"; a <- b_value; return $ Produce_assignments a }
  , do { tok ":regular-output-channel";    a <- string; return $ Regular_output_channel    a }
  , do { tok ":diagnostic-output-channel"; a <- string; return $ Diagnostic_output_channel a }
  , do { tok ":random-seed"; a <- numeral; return $ Random_seed $ fromIntegral a }
  , do { tok ":verbosity";   a <- numeral; return $ Verbosity   $ fromIntegral a }
  , attribute >>= return . Option_attribute
  ]

data Info_flag
  = Error_behavior
  | Name
  | Authors
  | Version
  | Status
  | Reason_unknown
  | Info_flag Keyword
  | All_statistics

instance Show Info_flag where
  show a = case a of
    Error_behavior -> ":error-behavior"
    Name           -> ":name"
    Authors        -> ":authors"
    Version        -> ":version"
    Status         -> ":status"
    Reason_unknown -> ":reason-unknown"
    Info_flag    a -> a
    All_statistics -> ":all-statistics"

info_flag :: SMTLIB Info_flag
info_flag = choice
  [ do { kw "error-behavior"; return Error_behavior }
  , do { kw "name"          ; return Name           }
  , do { kw "authors"       ; return Authors        }
  , do { kw "version"       ; return Version        }
  , do { kw "status"        ; return Status         }
  , do { kw "reason-unknown"; return Reason_unknown }
  , do { kw "all-statistics"; return All_statistics }
  , keyword >>= return . Info_flag
  ]

data Command
  = Set_logic Symbol
  | Set_option Option
  | Set_info Attribute
  | Declare_sort Symbol Numeral
  | Define_sort  Symbol [Symbol] Sort
  | Declare_fun  Symbol [Sort] Sort
  | Define_fun   Symbol [Sorted_var] Sort Term
  | Push Int
  | Pop  Int
  | Assert Term
  | Check_sat
  | Get_assertions
  | Get_proof
  | Get_unsat_core
  | Get_value [Term]
  | Get_assignment
  | Get_option Keyword
  | Get_info Info_flag
  | Exit

instance Show Command where
  show a = case a of
    Set_logic    a -> group ["set-logic", a]
    Set_option   a -> group ["set-option", show a]
    Set_info     a -> group ["set-info", show a]
    Declare_sort a b -> group ["declare-sort", a, show b]
    Define_sort  a b c -> group ["define-sort", a, group (map show b), show c]
    Declare_fun  a b c -> group ["declare-fun", a, group (map show b), show c]
    Define_fun   a b c d -> group ["define-fun", a, group (map show b), show c, show d]
    Push a -> group ["push", show a]
    Pop  a -> group ["pop",  show a]
    Assert a -> group ["assert", show a]
    Check_sat -> group ["check-sat"]
    Get_assertions -> group ["get-assertions"]
    Get_proof      -> group ["get-proof"]
    Get_unsat_core -> group ["get-unsat-core"]
    Get_value a -> group ["get-value", group $ map show a]
    Get_assignment -> group ["get-assignment"]
    Get_option a -> group ["get-option", a]
    Get_info   a -> group ["get-info", show a]
    Exit -> group ["exit"]

command :: SMTLIB Command
command = choice
  [ do { left; tok "set-logic"; a <- symbol; right; return $ Set_logic a }
  , do { left; tok "set-option"; a <- option; right; return $ Set_option a }
  , do { left; tok "set-info"; a <- attribute; right; return $ Set_info a }
  , do { left; tok "declare-sort"; a <- symbol; b <- numeral; right; return $ Declare_sort a b }
  , do { left; tok "define-sort"; a <- symbol; left; b <- many symbol; right; c <- sort'; right; return $ Define_sort a b c }
  , do { left; tok "declare-fun"; a <- symbol; left; b <- many sort'; right; c <- sort'; right; return $ Declare_fun a b c }
  , do { left; tok "define-fun"; a <- symbol; left; b <- many sorted_var; right; c <- sort'; d <- term; right; return $ Define_fun a b c d }
  , do { left; tok "push"; a <- numeral; right; return $ Push $ fromIntegral a }
  , do { left; tok "pop"; a <- numeral; right; return $ Pop $ fromIntegral a }
  , do { left; tok "assert"; a <- term; right; return $ Assert a }
  , do { left; tok "check-sat"; right; return $ Check_sat }
  , do { left; tok "get-assertions"; right; return $ Get_assertions }
  , do { left; tok "get-proof"; right; return $ Get_proof }
  , do { left; tok "get-unsat-core"; right; return $ Get_unsat_core }
  , do { left; tok "get-value"; left; a <- many1 term; right; right; return $ Get_value a }
  , do { left; tok "get-assignment"; right; return $ Get_assignment }
  , do { left; tok "get-option"; a <- keyword; right; return $ Get_option a }
  , do { left; tok "get-info"; a <- info_flag; right; return $ Get_info a }
  , do { left; tok "exit"; right; return $ Exit }
  ]

data Script = Script [Command]

instance Show Script where
  show (Script a) = unlines $ map show a

script :: SMTLIB Script
script = Script <$> many command <* whiteSpace  <* eof


data Gen_response
  = Unsupported
  | Success
  | Error String

instance Show Gen_response where
  show a = case a of
    Unsupported  -> "unsupported"
    Success      -> "success"
    Error a      -> group ["error", show a]

gen_response :: SMTLIB Gen_response
gen_response = choice
  [ pure Unsupported <$> tok "unsupported"
  , pure Success <$> tok "success"
  , parens $ Error <$> (tok "error" *> string)
  --do { left; tok "error"; a <- string; right; return $ Error a }
  ]



data Error_behavior
  = Immediate_exit
  | Continued_execution

instance Show Error_behavior where
  show a = case a of
    Immediate_exit      -> "immediate-exit"
    Continued_execution -> "continued-execution"

error_behavior :: SMTLIB Error_behavior
error_behavior = choice
  [ do { tok "immediate-exit"; return Immediate_exit }
  , do { tok "continued-execution"; return Continued_execution }
  ]

data Reason_unknown
  = Timeout
  | Memout
  | Incomplete

instance Show Reason_unknown where
  show a = case a of
    Timeout    -> "timeout"
    Memout     -> "memout"
    Incomplete -> "incomplete"

reason_unknown :: SMTLIB Reason_unknown
reason_unknown = choice
  [ do { tok "timeout"; return Timeout }
  , do { tok "memout"; return Memout }
  , do { tok "incomplete"; return Incomplete }
  ]

data Status
  = Sat
  | Unsat
  | Unknown

instance Show Status where
  show a = case a of
    Sat     -> "sat"
    Unsat   -> "unsat"
    Unknown -> "unknown"

status :: SMTLIB Status
status = choice
  [ do { tok "sat"; return Sat }
  , do { tok "unsat"; return Unsat }
  , do { tok "unknown"; return Unknown }
  ]

data Info_response
  = Info_response_error_behavior Error_behavior
  | Info_response_name    String
  | Info_response_authors String
  | Info_response_version String
  | Info_response_status  Status
  | Info_response_reason_unknown Reason_unknown
  | Info_response_attribute Attribute

instance Show Info_response where
  show a = case a of
    Info_response_error_behavior a -> ":error-behavior " ++ show a
    Info_response_name           a -> ":name "           ++ show a
    Info_response_authors        a -> ":authors "        ++ show a
    Info_response_version        a -> ":version "        ++ show a
    Info_response_status         a -> ":status "         ++ show a
    Info_response_reason_unknown a -> ":reason-unknown " ++ show a
    Info_response_attribute      a -> show a

info_response :: SMTLIB Info_response
info_response = choice
  [ do { kw "error-behavior"; a <- error_behavior; return $ Info_response_error_behavior a }
  , do { kw "name"; a <- string; return $ Info_response_name a }
  , do { kw "authors"; a <- string; return $ Info_response_authors a }
  , do { kw "version"; a <- string; return $ Info_response_version a }
  , do { kw "status"; a <- status; return $ Info_response_status a }
  , do { kw "reason-unknown"; a <- reason_unknown; return $ Info_response_reason_unknown a }
  , do attribute >>= return . Info_response_attribute
  ]

type Proof            = S_expr
type Valuation_pair   = (Term, Term)
type T_valuation_pair = (Symbol, Bool)

data Command_response
  = Gen_response  Gen_response
  | Info_response Info_response
  | Gi_response   [Info_response]
  | Cs_response   Status
  | Ga_response   [Term]
  | Gp_response   Proof
  | Guc_response  [Symbol]
  | Gv_response   [Valuation_pair]
  | Gta_response  [T_valuation_pair]

instance Show Command_response where
  show a = case a of
    Gen_response  a -> show a
    Info_response a -> show a
    Gi_response   a -> group $ map show a
    Cs_response   a -> show a
    Ga_response   a -> group $ map show a
    Gp_response   a -> show a
    Guc_response  a -> group $ map show a
    Gv_response   a -> group $ [ group [(show a), (show b)] | (a, b) <- a ]
    Gta_response  a -> group $ [ group [(show a), (showBool b)] | (a, b) <- a ]

command_response :: SMTLIB Command_response
command_response = choice
  [ Gen_response <$> gen_response
  , Info_response <$> info_response
  , parens $ Gi_response <$> many1 info_response
  , Cs_response <$> status
  , parens $ Ga_response <$>  (many term)
  , Gp_response <$> s_expr
  , parens $ Guc_response <$> many symbol
  , parens $ (Gv_response <$> many1 ((,) <$> term  <*> term))
  , parens $ Gta_response <$> many (parens $  (,) <$> symbol <*> b_value)
  ]

responses :: SMTLIB [Command_response]
responses =  many command_response --  <* eof

group :: [String] -> String
group a = "( " ++ intercalate " " a ++ " )"

showBool :: Bool -> String
showBool a = if a then "true" else "false"

type SMTLIB a = Parser a


left :: SMTLIB Char
left = whiteSpace >> C.char '('

right :: SMTLIB Char
right = whiteSpace >> C.char ')'

leftBracket,rightBracket :: SMTLIB Char
leftBracket = whiteSpace >> C.char '['
rightBracket = whiteSpace >> C.char ']'

parens p = left >> p <* right
eof = whiteSpace >> endOfInput

numeral :: SMTLIB Numeral
numeral = do
  whiteSpace
  n <- C.number
  case n of
    C.I i -> return i
    _ -> fail ""

comment = C.skipSpace >>
          C.char ';' >> skipWhile (not . C.isEndOfLine) >> C.endOfLine >>
          do {end <- atEnd; unless end whiteSpace}


whiteSpace = C.skipSpace >> (Atto.option () comment)
-- FIXME: This doen't handle escapes correctly.
string :: SMTLIB String
string = do
  whiteSpace
  B.unpack <$> (doubleQuote *> C.takeWhile (not . (== '"')) <* doubleQuote)
  where doubleQuote = C.char '"'



symbol :: SMTLIB Symbol
symbol = do
    whiteSpace -- C.skipSpace
    B.unpack <$> C.takeWhile1 isSymbolChar

isSymbolChar x = C.isAlpha_ascii x || C.isDigit x || isOther x
  where isOther = C.inClass "+-/*=%?!.$_~&^<>@"


keyword :: SMTLIB Keyword
keyword = do
  whiteSpace
  C.char ':'
  (':':) <$> symbol

kw :: String -> SMTLIB ()
kw s = do
  whiteSpace
  C.char ':'
  tok s



b_value :: SMTLIB Bool
b_value = choice
  [ do { tok "true"; return True }
  , do { tok "false"; return False }
  ]

tok t = do
  s <- symbol
  unless (s == t) $ fail "token did not match"





-- | Lazily parses an SMT-LIB command script.
parseScript :: B.ByteString -> Either String Script
parseScript s = parseOnly script s

-- | Lazily parses an SMT-LIB command responses.
parseResponses :: B.ByteString -> Result [Command_response]
parseResponses s = parse responses s

-- | Lazily parses an SMT-LIB theory declaration.
parseTheory :: B.ByteString -> Result Theory_decl
parseTheory s = parse theory_decl s


-- | Lazily parses an SMT-LIB logic.
parseLogic :: B.ByteString -> Result Logic
parseLogic s = parse logic s



-- | Checks the parsing of a command file with the given parser
-- checkScript :: FilePath -> IO Bool
checkFile parser file = do
  cnts <- B.readFile file
  let orig = clean cnts
      parsed = parseOnly parser cnts
  case parsed of
    Left _ -> do
      writeFile (file ++ ".fail") $ show parsed
      return False
    Right val
          | orig == clean (B.pack $ show val) -> return True
          | otherwise ->  do
                     B.putStrLn orig
                     B.putStrLn cleanedval
                     writeFile (file ++ ".fail") $ show val
                     return False
      where cleanedval = clean $ B.pack $ show val

-- | Checks the parsing of a command script.
checkScript :: FilePath -> IO Bool
checkScript = checkFile script

-- | Checks the parsing of command responses.
checkResponses :: FilePath -> IO Bool
checkResponses = checkFile responses

clean :: B.ByteString -> B.ByteString
clean = B.filter (not . flip elem " \t\r\n")  . B.unlines . map (B.takeWhile (/= ';')) . B.lines


-- | Recursively searches current directory for *.smt2 files to test the parser.
checkParser :: IO ()
checkParser = do
  result <- checkDir "."
  if result
    then putStrLn "\nall tests passed\n"
    else putStrLn "\nTESTS FAILED\n"
  where
  checkDir :: FilePath -> IO Bool
  checkDir dir = getDirectoryContents dir >>= mapM checkFile >>= return . and
    where
    checkFile :: FilePath -> IO Bool
    checkFile file = do
      let f = dir ++ "/" ++ file
      a <- doesDirectoryExist f
      if (a && notElem file [".", ".."])
        then checkDir f
        else if (isSuffixOf ".smt2" f)
          then do
            putStr $ "testing file " ++ f ++ " ... "
            hFlush stdout
            pass <- checkScript f
            putStrLn (if pass then "pass" else "FAIL")
            hFlush stdout
            return pass
          else return True



-- Parse a script file.
parseScriptFile :: FilePath -> IO (Either String Script)
parseScriptFile path = do
  cnts <- B.readFile path
  return $ parseOnly script cnts


-- Iteratee based file parsing The following doesn't work, because it seems to
-- block consuming the EOF when running in ghci or if compiled with -threaded. Perhaps related
-- to this bug: http://hackage.haskell.org/trac/ghc/ticket/5060
--parseScriptFile :: FilePath -> IO Script
--parseScriptFile = fileDriver (parserToIteratee script)


-- Process a stream of command responses from the handle, invoking the parameter
-- action on each response.
commandResponseSource handle action =
    enumHandle 1 handle (responseIteratee command_response) >>= run >> return ()
  where responseIteratee p = icont (f (parse p)) Nothing
        f k (EOF Nothing) =
          case feed (k B.empty) B.empty of
            -- Ignore EOF errors? FIXME: Horrible Hack.
            Atto.Fail _ [] _ -> icont (f k)
            Atto.Fail _ err dsc -> throwErr (toException $ ParseError err ("eof: " ++ dsc))
            Atto.Partial _ -> throwErr (toException EofException)
            Atto.Done rest v
              | B.null rest -> idone v (EOF Nothing)
              | otherwise -> idone v (Chunk rest)
        f _ (EOF (Just e)) = throwErr e
        f k (Chunk s)
          | B.null s = icont (f k) Nothing
          | otherwise = do
              case k s of
                Atto.Fail _ err dsc -> throwErr (toException $ ParseError err ("chunk: " ++ dsc))
                Atto.Partial k' -> icont (f k') Nothing
                Atto.Done rest v -> do
                       lift $ action v
                       icont (f (\bs -> feed (parse command_response rest) bs)) Nothing
