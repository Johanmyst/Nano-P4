theory NP4_Simple_Action_Values
  imports
  NP4_Simple_Action_Syntax
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Word/Word_Bitwise"
(*  These files contain a minimalistic semantics of P4's action constructs. More complex concepts
    like switch statements are left out. The purpose of this verification effort is to showcase
    the viability of using Isabelle/HOL to verify P4 applications. These files focus on the
    action constructs.

    P4 actions are the code fragments that can read and write data being processed. The action
    constructs are where sequential code resides in P4. To this end the action constructs are the
    main way by which the control-plane can influence the behaviour of the data-plane.

    To this end these files define a small-step semantics of the P4 actions. Then a typing
    environment is built upon this, and the statements are extended with a termination-counter.
    These are used to prove properties like termination, determinism, progression,
    preservation, and more. The semantics can also be used to analyse reachability properties.
    Well-defined and well-typed P4 programs will yield a derivation tree, where as ill-defined
    or ill-typed P4 programs will yield no such tree. *)
begin

(* ============================================================================================================== *)
(*                                              VALUE MAPPINGS                                                    *)
(* ============================================================================================================== *)

(* Contains the value of a single bit, can be cast between bool *)
datatype sbit = ZERO | ONE

(* Mapping to concrete value *)
datatype val = SBIT sbit
  | UINT nat
  | SINT int
  | IINT int
  | VINT nat
  | BOOL bool
  | STRING string
  | ERROR "identifier list"
  | MATCH "identifier list"

(* State is a mapping from variable names to values *)
type_synonym state = "vname \<Rightarrow> val"

(* ============================================================================================================== *)
(*                                              HELPER FUNCTIONS                                                  *)
(* ============================================================================================================== *)

(* Convert a basetype to a concrete value used for converting the entries of derived types. *)
fun baseToVal :: "baseType \<Rightarrow> val" where
    "baseToVal (BBOOL b)       = (BOOL b)"
  | "baseToVal (BSBIT 0)       = (SBIT ZERO)"
  | "baseToVal (BSBIT (Suc n)) = (SBIT ONE)"
  | "baseToVal (BIINT n)       = (IINT n)"
  | "baseToVal (BUINT n)       = (UINT n)"
  | "baseToVal (BSINT n)       = (SINT n)"
  | "baseToVal (BVINT n)       = (VINT n)"
  | "baseToVal (BERROR e)      = (ERROR e)"
  | "baseToVal (BMATCH m)      = (MATCH m)"
  | "baseToVal (BSTRING s)     = (STRING s)"

(* ============================================================================================================== *)
(*                                   CONCRETE VALUE EVALUATION FUNCTIONS                                          *)
(* ============================================================================================================== *)

inductive eval :: "expression \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
(* =============== Base types =============== *)
    RBOOL:    "eval (BASE (BBOOL b))      s (BOOL b)"
  | RBIT0:    "eval (BASE (BSBIT 0))       s (SBIT ZERO)"
  | RBIT1:    "eval (BASE (BSBIT (Suc n))) s (SBIT ONE)"
  | RIINT:    "eval (BASE (BIINT n))      s (IINT n)"
  | RUINT:    "eval (BASE (BUINT n))      s (UINT n)"
  | RSINT:    "eval (BASE (BSINT n))      s (SINT n)"
  | RVINT:    "eval (BASE (BVINT n))      s (VINT n)"
  | RERROR:   "eval (BASE (BERROR e))     s (ERROR e)"
  | RMATCH:   "eval (BASE (BMATCH m))     s (MATCH m)"
  | RSTRING:  "eval (BASE (BSTRING str))  s (STRING str)"
(* =============== Miscellaneous expressions =============== *)
  | TERNTRUE:  "eval e1 s (BOOL b) \<Longrightarrow> b = True \<Longrightarrow> eval e2 s v \<Longrightarrow> eval (TernExpr e1 e2 e3) s v"
  | TERNFALSE: "eval e1 s (BOOL b) \<Longrightarrow> b = False \<Longrightarrow> eval e3 s v \<Longrightarrow> eval (TernExpr e1 e2 e3) s v"
(* =============== Variable mapping  =============== *)
  | NAMEDVAR: "eval (NamedVar varName) s (s varName)"
(* =============== Operations that yield a single bit (SBIT)  =============== *)
          (* Empty for now *)
(* =============== Operations that yield a boolean (BOOL)  =============== *)
  | ULNEB: "eval e1 s (BOOL b) \<Longrightarrow> eval (UNA_LNE e1) s (BOOL (\<not>b))"
    (* Boolean operations *)
  | BEQUB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (b1 = b2))"
(* Boolean equality check yields derivation error; code cannot be generated for inductive predicate eval *)
(*  | BNEQB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_NEQ e1 e2) s (BOOL (b1 \<noteq> b2))" *)
  | BFANB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_FAN e1 e2) s (BOOL (b1 \<and> b2))"
  | BFORB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_FOR e1 e2) s (BOOL (b1 \<or> b2))"
    (* Signed integer opreations *)
  | BEQUS: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (n1 = n2))"
  | BNEQS: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_NEQ e1 e2) s (BOOL (n1 \<noteq> n2))"
  | BLEQS: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_LEQ e1 e2) s (BOOL (n1 \<le> n2))"
  | BGEQS: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_GEQ e1 e2) s (BOOL (n1 \<ge> n2))"
  | BLESS: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_LES e1 e2) s (BOOL (n1 < n2))"
  | BGRES: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_GRE e1 e2) s (BOOL (n1 > n2))"
    (* Unsigned integer opreations *)
  | BEQUU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (n1 = n2))"
  | BNEQU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_NEQ e1 e2) s (BOOL (n1 \<noteq> n2))"
  | BLEQU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_LEQ e1 e2) s (BOOL (n1 \<le> n2))"
  | BGEQU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_GEQ e1 e2) s (BOOL (n1 \<ge> n2))"
  | BLESU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_LES e1 e2) s (BOOL (n1 < n2))"
  | BGREU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_GRE e1 e2) s (BOOL (n1 > n2))"
    (* Infinite precision integer opreations *)
  | BEQUI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (n1 = n2))"
  | BNEQI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_NEQ e1 e2) s (BOOL (n1 \<noteq> n2))"
  | BLEQI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_LEQ e1 e2) s (BOOL (n1 \<le> n2))"
  | BGEQI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_GEQ e1 e2) s (BOOL (n1 \<ge> n2))"
  | BLESI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_LES e1 e2) s (BOOL (n1 < n2))"
  | BGREI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_GRE e1 e2) s (BOOL (n1 > n2))"
    (* Variable size bitstring opreations *)
  | BEQUV: "eval e1 s (VINT n1) \<Longrightarrow> eval e2 s (VINT n2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (n1 = n2))"
  | BNEQV: "eval e1 s (VINT n1) \<Longrightarrow> eval e2 s (VINT n2) \<Longrightarrow> eval (BIN_NEQ e1 e2) s (BOOL (n1 \<noteq> n2))"
(* =============== Operations that yield an unsigned integer (UINT)  =============== *)
  | UNEGU: "eval e1 s (UINT n1) \<Longrightarrow> eval (UNA_NEG e1) s (UINT n1)" (* Incorrect but w/e for now *)
  | UPOSU: "eval e1 s (UINT n1) \<Longrightarrow> eval (UNA_POS e1) s (UINT n1)"
  | UCOMU: "eval e1 s (UINT n1) \<Longrightarrow> eval (UNA_COM e1) s (UINT n1)" (* (nat (NOT (int n1))))" Incorrect but w/e *)
  | BADDU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_ADD e1 e2) s (UINT (n1 + n2))"
  | BMINU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_MIN e1 e2) s (UINT (n1 - n2))"
  | BANDU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_AND e1 e2) s (UINT (nat ((int n1) AND (int n2))))"
  | BXORU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_XOR e1 e2) s (UINT (nat ((int n1) XOR (int n2))))"
  | BLORU: "eval e1 s (UINT n1) \<Longrightarrow> eval e2 s (UINT n2) \<Longrightarrow> eval (BIN_LOR e1 e2) s (UINT (nat ((int n1) OR (int n2))))"
(* =============== Operations that yield a signed integer (SINT)  =============== *)
  | UNEGS: "eval e1 s (SINT n1) \<Longrightarrow> eval (UNA_NEG e1) s (SINT (-n1))"
  | UPOSS: "eval e1 s (SINT n1) \<Longrightarrow> eval (UNA_POS e1) s (SINT n1)"
  | BADDS: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_ADD e1 e2) s (SINT (n1 + n2))"
  | BMINS: "eval e1 s (SINT n1) \<Longrightarrow> eval e2 s (SINT n2) \<Longrightarrow> eval (BIN_MIN e1 e2) s (SINT (n1 - n2))"
(* =============== Operations that yield an infinite-precision integer (IINT)  =============== *)
  | UNEGI: "eval e1 s (IINT n1) \<Longrightarrow> eval (UNA_NEG e1) s (IINT (-n1))"
  | UPOSI: "eval e1 s (IINT n1) \<Longrightarrow> eval (UNA_POS e1) s (IINT n1)"
  | BADDI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_ADD e1 e2) s (IINT (n1 + n2))"
  | BMINI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_MIN e1 e2) s (IINT (n1 - n2))"
  | BMULI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_MUL e1 e2) s (IINT (n1 * n2))"
  | BDIVI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_DIV e1 e2) s (IINT (n1 div n2))"
  | BMODI: "eval e1 s (IINT n1) \<Longrightarrow> eval e2 s (IINT n2) \<Longrightarrow> eval (BIN_MOD e1 e2) s (IINT (n1 mod n2))"
(* =============== Operations that yield a variable-width integer (VINT)  =============== *)
      (* Empty for now *)

inductive_cases [elim!]: "eval (BASE b) s v" "eval (TernExpr e1 e2 e3) s v" "eval (NamedVar i) s v"
"eval (UNA_LNE e) s v" "eval (UNA_COM e) s v" "eval (UNA_NEG e) s v" "eval (UNA_POS e) s v" "eval (BIN_MUL e1 e2) s v"
"eval (BIN_DIV e1 e2) s v" "eval (BIN_MOD e1 e2) s v" "eval (BIN_ADD e1 e2) s v" "eval (BIN_MIN e1 e2) s v" "eval (BIN_AND e1 e2) s v"
"eval (BIN_XOR e1 e2) s v" "eval (BIN_LOR e1 e2) s v" "eval (BIN_LEQ e1 e2) s v" "eval (BIN_GEQ e1 e2) s v" "eval (BIN_LES e1 e2) s v"
"eval (BIN_GRE e1 e2) s v" "eval (BIN_NEQ e1 e2) s v" "eval (BIN_EQU e1 e2) s v" "eval (BIN_FAN e1 e2) s v" "eval (BIN_FOR e1 e2) s v"

lemma eval_deterministic: "(eval e s v) \<Longrightarrow> (eval e s v') \<Longrightarrow> (v = v')"
  apply (induction arbitrary: v' rule: eval.induct)
                      apply (blast+)
  done

code_pred eval .

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. (UINT 0)"
syntax
  "_State" :: "updbinds \<Rightarrow> 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

end
