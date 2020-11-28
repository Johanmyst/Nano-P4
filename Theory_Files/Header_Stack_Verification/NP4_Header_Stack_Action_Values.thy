theory NP4_Header_Stack_Action_Values
  imports
  NP4_Header_Stack_Action_Syntax
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Word/Word_Bitwise"
(*  This file is an extension of a more simplistic semantics of P4 applications. Its purpose is
    to highlight the triviality of verifying/ensuring safety properties in an application. Here,
    as an example, it is shown that ruling out out-of-bounds accesses are trivial to ensure.
    
    P4 has no notion of typical C-like lists. P4 does have a stack of headers. These are commonly
    used in parsing, like with MLPS labels existing in a stack. A header stack has to be defined
    in size at compile-time. As such the size is known at verification-time, and these files show
    the triviality of ensuring that a read action can't be performed out-of-bounds. This is
    achieved by tailoring the semantics to not be defined for out-of-bounds cases. *)
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
  | HEADER "(identifier * identifier) list"
  | HSTACK "((identifier * identifier) list) list"

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
  | "baseToVal (BHEADER l)     = (HEADER l)"
  | "baseToVal (BHSTACK l)     = (HSTACK l)"

(* ============================================================================================================== *)
(*                                   CONCRETE VALUE EVALUATION FUNCTIONS                                          *)
(* ============================================================================================================== *)

inductive eval :: "expression \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
(* =============== Base types =============== *)
    RBASE:    "eval (BASE b) s (baseToVal b)"
(* =============== Miscellaneous expressions =============== *)
  | TERNTRUE:  "eval e1 s (BOOL b) \<Longrightarrow> b = True \<Longrightarrow> eval e2 s v \<Longrightarrow> eval (TernExpr e1 e2 e3) s v"
  | TERNFALSE: "eval e1 s (BOOL b) \<Longrightarrow> b = False \<Longrightarrow> eval e3 s v \<Longrightarrow> eval (TernExpr e1 e2 e3) s v"
  | STCKIDX:   "eval e1 s (HSTACK l) \<Longrightarrow> n < length l \<Longrightarrow> eval (StckIdx e1 n) s (HEADER (l ! n))" (* Header access iff n < len l *)
(* =============== Variable mapping  =============== *)
  | NAMEDVAR: "eval (NamedVar varName) s (s varName)"
(* =============== Operations that yield a single bit (SBIT)  =============== *)
          (* Empty for now *)
(* =============== Operations that yield a boolean (BOOL)  =============== *)
  | ULNEB: "eval e1 s (BOOL b) \<Longrightarrow> eval (UNA_LNE e1) s (BOOL (\<not>b))"
    (* Boolean operations *)
  | BEQUB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (b1 = b2))"
  | BNEQB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_NEQ e1 e2) s (BOOL (b1 \<noteq> b2))"
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

inductive_cases [elim!]: "eval (BASE b) s v" "eval (TernExpr e1 e2 e3) s v" "eval (NamedVar i) s v" "eval (StckIdx i n) s v"
"eval (UNA_LNE e) s v" "eval (UNA_COM e) s v" "eval (UNA_NEG e) s v" "eval (UNA_POS e) s v" "eval (BIN_MUL e1 e2) s v"
"eval (BIN_DIV e1 e2) s v" "eval (BIN_MOD e1 e2) s v" "eval (BIN_ADD e1 e2) s v" "eval (BIN_MIN e1 e2) s v" "eval (BIN_AND e1 e2) s v"
"eval (BIN_XOR e1 e2) s v" "eval (BIN_LOR e1 e2) s v" "eval (BIN_LEQ e1 e2) s v" "eval (BIN_GEQ e1 e2) s v" "eval (BIN_LES e1 e2) s v"
"eval (BIN_GRE e1 e2) s v" "eval (BIN_NEQ e1 e2) s v" "eval (BIN_EQU e1 e2) s v" "eval (BIN_FAN e1 e2) s v" "eval (BIN_FOR e1 e2) s v"

(* Shows there is always a header in the header stack index access. *)
lemma header_or_nothing: "eval (StckIdx e n) s v \<Longrightarrow> (\<exists>i. v = (HEADER i))"
  by blast

lemma eval_deterministic: "(eval e s v) \<Longrightarrow> (eval e s v') \<Longrightarrow> (v' = v)"
  apply (induction arbitrary: v' rule: eval.induct)
                      apply (blast+)
  done

end
