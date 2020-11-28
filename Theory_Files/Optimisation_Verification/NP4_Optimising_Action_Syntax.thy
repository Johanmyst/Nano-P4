theory NP4_Optimising_Action_Syntax
  imports
  Complex_Main
(*
    This file will contain a minimalistic syntax for P4's actions. Concepts like a switch are
    left out because they can also be modelled with e.g. an if-else chain.

    P4 actions are code fragments that can read and write the data being processed. They are
    the main construct by which the control-plane can influence the behaviour of the data-plane.
 *)
begin

(* Syntactic sugar in the syntax *)
type_synonym vname = string
type_synonym identifier = string

(* Variable or custom type names *)
datatype name = VarName identifier (* Denoting a variable name *)
  | TypeName identifier (* Denoting the name of a type *)

(* The base types found in P4 from which derived types can be constructed *)
datatype baseType = BBOOL bool
  | BIINT int (* Infinite-precision integer, converted by compiler to UINT or SINT *)
  | BUINT nat
  | BSINT int
  | BVINT nat (* Variable-width bit-string, limited operations supported *)
  | BERROR "identifier list" (* List of error strings *)
  | BMATCH "identifier list" (* List of criteria to match against in match-action table *)
  | BSTRING string (* String, no operations supported, used to directly pass to target *)

(* Expressions hold the main computational code of P4's actions *)
datatype expression = BASE baseType
  | TernExpr expression expression expression (* expr1 ? expr 2 : expr 3 *)
  | NamedVar vname (* Named variable *)
  | UNA_LNE expression (* Unary logical negation: ! expr *)
  | UNA_COM expression (* Unary one's complement: ~ expr *)
  | UNA_NEG expression (* Unary negative: - expr *)
  | UNA_POS expression (* Unary positive (useless): + expr *)
  | BIN_MUL expression expression (* binary multiplication: expr * expr *)
  | BIN_DIV expression expression (* binary division: expr / expr *)
  | BIN_MOD expression expression (* binary modulo: expr % expr *)
  | BIN_ADD expression expression (* binary addition: expr + expr *)
  | BIN_MIN expression expression (* binary minus: expr - expr *)
  | BIN_AND expression expression (* binary logical and: expr & expr *)
  | BIN_XOR expression expression (* binary logical xor: expr ^ expr *)
  | BIN_LOR expression expression (* binary logical or: expr | expr *)
  | BIN_LEQ expression expression (* binary less or equal: expr \<le> expr *)
  | BIN_GEQ expression expression (* binary greater or equal: expr \<ge> expr *)
  | BIN_LES expression expression (* binary less than: expr < expr *)
  | BIN_GRE expression expression (* binary greater than: expr > expr *)
  | BIN_NEQ expression expression (* binary not equal: expr != expr *)
  | BIN_EQU expression expression (* binary equal: expr == expr *)
  | BIN_FAN expression expression (* binary fast and: expr && expr *)
  | BIN_FOR expression expression (* binary fast or: expr || expr *)

datatype statOrDecl = EmptyStat
  | ExitStat
  | ConditionalStat expression statOrDecl statOrDecl (* Conditional statement *)
  | BlockStat "statOrDecl list" (* List of statements *)
  | AssignmentStat vname expression (* Assign a value to an lvalue *)
  | VariableDecl vname "expression option" (* Declare a new variable *)
  | ConstantDecl vname expression (* Declare a new constant *)

end