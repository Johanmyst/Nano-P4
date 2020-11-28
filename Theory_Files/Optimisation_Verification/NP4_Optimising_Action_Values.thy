theory NP4_Optimising_Action_Values
  imports
  NP4_Optimising_Action_Syntax
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Word/Word_Bitwise"
(*
    This file contains the concrete values and their encapsulation as used by
    P4 and the P4 action constructs. This includes the evaluation functions.
*)
begin

(* ============================================================================================================== *)
(*                                              VALUE MAPPINGS                                                    *)
(* ============================================================================================================== *)

(* Mapping to concrete value *)
datatype val = UINT nat
  | SINT int
  | IINT int
  | VINT nat
  | BOOL bool
  | STRING string
  | ERROR "identifier list"
  | MATCH "identifier list"

(* State is a mapping from variable names to values *)
type_synonym state = "vname \<Rightarrow> val"

(* Tab is a table of values that contain a constant *)
type_synonym tab = "vname \<Rightarrow> val option"

(* ============================================================================================================== *)
(*                                              HELPER FUNCTIONS                                                  *)
(* ============================================================================================================== *)

(* Convert a basetype to a concrete value used for converting the entries of derived types. *)
fun baseToVal :: "baseType \<Rightarrow> val" where
    "baseToVal (BBOOL b)        = (BOOL b)"
  | "baseToVal (BIINT n)        = (IINT n)"
  | "baseToVal (BUINT n)        = (UINT n)"
  | "baseToVal (BSINT n)        = (SINT n)"
  | "baseToVal (BVINT n)        = (VINT n)"
  | "baseToVal (BERROR e)       = (ERROR e)"
  | "baseToVal (BMATCH m)       = (MATCH m)"
  | "baseToVal (BSTRING s)      = (STRING s)"

fun valToBase :: "val \<Rightarrow> baseType" where
    "valToBase (BOOL b)        = (BBOOL b)"
  | "valToBase (IINT n)        = (BIINT n)"
  | "valToBase (UINT n)        = (BUINT n)"
  | "valToBase (SINT n)        = (BSINT n)"
  | "valToBase (VINT n)        = (BVINT n)"
  | "valToBase (ERROR e)       = (BERROR e)"
  | "valToBase (MATCH m)       = (BMATCH m)"
  | "valToBase (STRING s)      = (BSTRING s)"

(* ============================================================================================================== *)
(*                                   CONCRETE VALUE EVALUATION FUNCTIONS                                          *)
(* ============================================================================================================== *)

inductive eval :: "expression \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"
  where
(* =============== Base types =============== *)
    RBOOL:    "eval (BASE (BBOOL b))      s (BOOL b)"
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

lemmas eval_induct = eval.induct[split_format(complete)]
declare eval.intros[simp, intro]

inductive_cases [elim!]: "eval (BASE b) s v" "eval (TernExpr e1 e2 e3) s v" "eval (NamedVar i) s v"
"eval (UNA_LNE e) s v" "eval (UNA_COM e) s v" "eval (UNA_NEG e) s v" "eval (UNA_POS e) s v" "eval (BIN_MUL e1 e2) s v"
"eval (BIN_DIV e1 e2) s v" "eval (BIN_MOD e1 e2) s v" "eval (BIN_ADD e1 e2) s v" "eval (BIN_MIN e1 e2) s v" "eval (BIN_AND e1 e2) s v"
"eval (BIN_XOR e1 e2) s v" "eval (BIN_LOR e1 e2) s v" "eval (BIN_LEQ e1 e2) s v" "eval (BIN_GEQ e1 e2) s v" "eval (BIN_LES e1 e2) s v"
"eval (BIN_GRE e1 e2) s v" "eval (BIN_NEQ e1 e2) s v" "eval (BIN_EQU e1 e2) s v" "eval (BIN_FAN e1 e2) s v" "eval (BIN_FOR e1 e2) s v"

lemma eval_deterministic: "(eval e s v) \<Longrightarrow> (eval e s v') \<Longrightarrow> (v = v')"
  apply (induction arbitrary: v' rule: eval.induct)
                      apply (blast+)
  done

(* ============================================================================================================== *)
(*                                  OPTIMISED VALUE EVALUATION FUNCTIONS                                          *)
(* ============================================================================================================== *)

fun efold :: "expression \<Rightarrow> tab \<Rightarrow> expression"
  where
(* =============== Base types  =============== *)
    "efold (BASE bVal) _ = (BASE bVal)"
(* =============== Variable mapping  =============== *)
  | "efold (NamedVar vName) t = (case t vName of
            None \<Rightarrow> NamedVar vName
          | Some vVal \<Rightarrow> BASE (valToBase vVal))"
(* =============== Miscellaneous expressions =============== *)
  | "efold (TernExpr e1 e2 e3) t = (case efold e1 t of
            BASE (BBOOL True) \<Rightarrow> e2
          | BASE (BBOOL False) \<Rightarrow> e3
          | e1' \<Rightarrow> TernExpr e1' e2 e3)"
(* =============== Unary operators =============== *)
  | "efold (UNA_LNE e1) t = (case efold e1 t of
            BASE (BBOOL b) \<Rightarrow> BASE (BBOOL (\<not>b))
          | e1' \<Rightarrow> UNA_LNE e1')"
  | "efold (UNA_NEG e1) t = (case efold e1 t of
            BASE (BUINT n1) \<Rightarrow> BASE (BUINT (n1))
          | BASE (BSINT n1) \<Rightarrow> BASE (BSINT (-n1))
          | BASE (BIINT n1) \<Rightarrow> BASE (BIINT (-n1))
          | e1' \<Rightarrow> UNA_NEG e1')"
  | "efold (UNA_POS e1) t = (case efold e1 t of
            BASE (BUINT n1) \<Rightarrow> BASE (BUINT (n1))
          | BASE (BSINT n1) \<Rightarrow> BASE (BSINT (n1))
          | BASE (BIINT n1) \<Rightarrow> BASE (BIINT (n1))
          | e1' \<Rightarrow> UNA_POS e1')"
  | "efold (UNA_COM e1) t = (case efold e1 t of
            BASE (BUINT n1) \<Rightarrow> BASE (BUINT (n1))
          | e1' \<Rightarrow> UNA_COM e1')"
(* =============== Binary operators =============== *)
  | "efold (BIN_EQU e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BBOOL b1), BASE (BBOOL b2)) \<Rightarrow> BASE (BBOOL (b1 = b2))
          | (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BBOOL (n1 = n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BBOOL (n1 = n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BBOOL (n1 = n2))
          | (BASE (BVINT n1), BASE (BVINT n2)) \<Rightarrow> BASE (BBOOL (n1 = n2))
          | (e1', e2') \<Rightarrow> BIN_EQU e1' e2')"
  | "efold (BIN_NEQ e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BBOOL b1), BASE (BBOOL b2)) \<Rightarrow> BASE (BBOOL (b1 \<noteq> b2))
          | (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<noteq> n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<noteq> n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<noteq> n2))
          | (BASE (BVINT n1), BASE (BVINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<noteq> n2))
          | (e1', e2') \<Rightarrow> BIN_NEQ e1' e2')"
  | "efold (BIN_FAN e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BBOOL b1), BASE (BBOOL b2)) \<Rightarrow> BASE (BBOOL (b1 \<and> b2))
          | (e1', e2') \<Rightarrow> BIN_FAN e1' e2')"
  | "efold (BIN_FOR e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BBOOL b1), BASE (BBOOL b2)) \<Rightarrow> BASE (BBOOL (b1 \<or> b2))
          | (e1', e2') \<Rightarrow> BIN_FOR e1' e2')"
  | "efold (BIN_LEQ e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<le> n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<le> n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<le> n2))
          | (BASE (BVINT n1), BASE (BVINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<le> n2))
          | (e1', e2') \<Rightarrow> BIN_LEQ e1' e2')"
  | "efold (BIN_GEQ e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<ge> n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<ge> n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<ge> n2))
          | (BASE (BVINT n1), BASE (BVINT n2)) \<Rightarrow> BASE (BBOOL (n1 \<ge> n2))
          | (e1', e2') \<Rightarrow> BIN_GEQ e1' e2')"
  | "efold (BIN_LES e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BBOOL (n1 < n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BBOOL (n1 < n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BBOOL (n1 < n2))
          | (BASE (BVINT n1), BASE (BVINT n2)) \<Rightarrow> BASE (BBOOL (n1 < n2))
          | (e1', e2') \<Rightarrow> BIN_LES e1' e2')"
  | "efold (BIN_GRE e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BBOOL (n1 > n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BBOOL (n1 > n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BBOOL (n1 > n2))
          | (BASE (BVINT n1), BASE (BVINT n2)) \<Rightarrow> BASE (BBOOL (n1 > n2))
          | (e1', e2') \<Rightarrow> BIN_GRE e1' e2')"
  | "efold (BIN_ADD e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BSINT (n1 + n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BUINT (n1 + n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BIINT (n1 + n2))
          | (e1', e2') \<Rightarrow> BIN_ADD e1' e2')"
  | "efold (BIN_MIN e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BSINT n1), BASE (BSINT n2)) \<Rightarrow> BASE (BSINT (n1 - n2))
          | (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BUINT (n1 - n2))
          | (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BIINT (n1 - n2))
          | (e1', e2') \<Rightarrow> BIN_MIN e1' e2')"
  | "efold (BIN_AND e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BUINT (nat ((int n1) AND (int n2))))
          | (e1', e2') \<Rightarrow> BIN_AND e1' e2')"
  | "efold (BIN_XOR e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BUINT (nat ((int n1) XOR (int n2))))
          | (e1', e2') \<Rightarrow> BIN_XOR e1' e2')"
  | "efold (BIN_LOR e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BUINT n1), BASE (BUINT n2)) \<Rightarrow> BASE (BUINT (nat ((int n1) OR (int n2))))
          | (e1', e2') \<Rightarrow> BIN_LOR e1' e2')"
  | "efold (BIN_MUL e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BIINT (n1 * n2))
          | (e1', e2') \<Rightarrow> BIN_MUL e1' e2')"
  | "efold (BIN_DIV e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BIINT (n1 div n2))
          | (e1', e2') \<Rightarrow> BIN_DIV e1' e2')"
  | "efold (BIN_MOD e1 e2) t = (case (efold e1 t, efold e2 t) of
            (BASE (BIINT n1), BASE (BIINT n2)) \<Rightarrow> BASE (BIINT (n1 mod n2))
          | (e1', e2') \<Rightarrow> BIN_MOD e1' e2')"

(* ============================================================================================================== *)
(*                                       OPTIMISATION FUNCTION PROOFS                                             *)
(* ============================================================================================================== *)

definition "approx t s \<longleftrightarrow> (\<forall>vName v. t vName = Some v \<longrightarrow> s vName = v)"

lemma approx_map_le:
  "approx t2 s \<Longrightarrow> t1 \<subseteq>\<^sub>m t2 \<Longrightarrow> approx t1 s"
  by (metis (mono_tags, lifting) approx_def domIff map_le_def option.distinct(1))

lemma approx_empty [simp]:
  "approx Map.empty = (\<lambda>_. True)"
  by (auto simp: approx_def)

theorem eval_efold[simp]: "approx t s \<Longrightarrow> (eval e s v = eval (efold e t) s v)"
  sorry
end
