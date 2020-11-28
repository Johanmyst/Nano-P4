theory NP4_Struct_Action_Syntax
  imports
  Complex_Main
(*  These files contain a minimalistic semantics of P4's action constructs. These files
    specifically extend the previously implemented simple semantics with more complex
    datastructures, in this case the struct datastructure. P4 knows structs, headers,
    enums, header unions and stacks, and tuples. The struct type however is the most
    general of these. Showing that structs are verifiable thus also shows that headers
    (and thus header unions and header stacks), enums, and tuples can be verified using
    Isabelle/HOL. *)
begin

(* Syntactic sugar in the syntax *)
type_synonym vname = string
type_synonym identifier = string

(* Variable or custom type names *)
datatype name = VarName identifier (* Denoting a variable name *)
  | TypeName identifier (* Denoting the name of a type *)

datatype basicType = BBOOL bool
  | BIINT int (* Infinite-precision integer, converted by compiler to UINT or SINT *)
  | BUINT nat
  | BSINT int
  | BVINT nat (* Variable-width bit-string, limited operations supported *)
  | BERROR "identifier list" (* List of error strings *)
  | BMATCH "identifier list" (* List of criteria to match against in match-action table *)
  | BSTRING string (* String, no operations supported, used to directly pass to target *)
(* Derived types are formed from the basetypes above. In regular P4 derived types can
contain further derived types (e.g. a struct can contain a struct) but here this is
omitted and derived types can exclusively be constructed from basetypes. *)
  | DSTRUCT "(identifier * vname * basicType option) list" (* typename * membername * value (heterogeneous) *)

(* Expressions hold the main computational code of P4's actions *)
datatype expression = BASE basicType
  | TernExpr expression expression expression (* expr1 ? expr 2 : expr 3 *)
  | NamedVar vname (* Named variable *)
  | ExprMem expression vname (* Access member of derived type: struct . name *)
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