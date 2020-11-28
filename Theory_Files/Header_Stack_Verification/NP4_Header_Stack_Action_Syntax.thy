theory NP4_Header_Stack_Action_Syntax
  imports
  Complex_Main
(*  This file is an extension of a more simplistic semantics of P4 applications. Its purpose is
    to highlight the triviality of verifying/ensuring safety properties in an application. Here,
    as an example, it is shown that ruling out out-of-bounds accesses are trivial to ensure.
    
    P4 has no notion of typical C-like lists. P4 does have a stack of headers. These are commonly
    used in parsing, like with MLPS labels existing in a stack. A header stack has to be defined
    in size at compile-time. As such the size is known at verification-time, and these files show
    the triviality of ensuring that a read action can't be performed out-of-bounds. This is
    achieved by tailoring the semantics to not be defined for out-of-bounds cases. *)
begin

(* Syntactic sugar in the syntax *)
type_synonym vname = string
type_synonym identifier = string

(* Variable or custom type names *)
datatype name = VarName identifier (* Denoting a variable name *)
  | TypeName identifier (* Denoting the name of a type *)

(* The base types found in P4 from which derived types can be constructed *)
datatype baseType = BBOOL bool
  | BSBIT nat
  | BIINT int (* Infinite-precision integer, converted by compiler to UINT or SINT *)
  | BUINT nat
  | BSINT int
  | BVINT nat (* Variable-width bit-string, limited operations supported *)
  | BERROR "identifier list" (* List of error strings *)
  | BMATCH "identifier list" (* List of criteria to match against in match-action table *)
  | BSTRING string (* String, no operations supported, used to directly pass to target *)
  | BHEADER "(identifier * identifier) list"
  | BHSTACK "((identifier * identifier) list) list"

(* Expressions hold the main computational code of P4's actions *)
datatype expression = BASE baseType
  | TernExpr expression expression expression (* expr1 ? expr 2 : expr 3 *)
  | StckIdx expression nat (* Access into header stack: expr [ n ] *)
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

datatype lvalue = NameLVal vname (* Variable name assignment *)
  | MemberLVal lvalue vname (* Member value assignment *)

datatype statOrDecl = EmptyStat
  | ExitStat
  | ConditionalStat expression statOrDecl statOrDecl (* Conditional statement *)
  | BlockStat "statOrDecl list" (* List of statements *)
  | AssignmentStat lvalue expression (* Assign a value to an lvalue *)
  | VariableDecl lvalue "expression option" (* Declare a new variable *)
  | ConstantDecl lvalue expression (* Declare a new constant *)

end