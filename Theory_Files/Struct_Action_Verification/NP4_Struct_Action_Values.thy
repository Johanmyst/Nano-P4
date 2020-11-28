theory NP4_Struct_Action_Values
  imports
  NP4_Struct_Action_Syntax
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Word/Word_Bitwise"
(*  These files contain a minimalistic semantics of P4's action constructs. These files
    specifically extend the previously implemented simple semantics with more complex
    datastructures, in this case the struct datastructure. P4 knows structs, headers,
    enums, header unions and stacks, and tuples. The struct type however is the most
    general of these. Showing that structs are verifiable thus also shows that headers
    (and thus header unions and header stacks), enums, and tuples can be verified using
    Isabelle/HOL. *)
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
  | STRUCT "(identifier * vname * val option) list" (* Heterogeneous named struct *)

(* State is a mapping from variable names to values *)
type_synonym state = "vname \<Rightarrow> val"

(* ============================================================================================================== *)
(*                                         BASE CONVERSION FUNCTIONS                                              *)
(* ============================================================================================================== *)

fun
  (* Structs have base types in them, so convert the contents of a struct to vals recursively *)
  structEntryToVal :: "(identifier * vname * basicType option) \<Rightarrow> (identifier * vname * val option)"
and
  baseToVal :: "basicType \<Rightarrow> val"
  where
    (* Map a single struct entry (containing basic types) to vals *)
    "structEntryToVal (tName, vName, None)      = (tName, vName, None)"
  | "structEntryToVal (tName, vName, Some bVal) = (tName, vName, Some (baseToVal bVal))"
    (* Map the remaining basic types to vals *)
  | "baseToVal (BBOOL b)         = (BOOL b)"
  | "baseToVal (BIINT n)         = (IINT n)"
  | "baseToVal (BUINT n)         = (UINT n)"
  | "baseToVal (BSINT n)         = (SINT n)"
  | "baseToVal (BVINT n)         = (VINT n)"
  | "baseToVal (BERROR e)        = (ERROR e)"
  | "baseToVal (BMATCH m)        = (MATCH m)"
  | "baseToVal (BSTRING s)       = (STRING s)"
  | "baseToVal (DSTRUCT entries) = (STRUCT (map structEntryToVal entries))" (* Recurse on structs *)

fun
  (* Helper function to go the other way from above (back to base type from val for struct entries) *)
  structEntryToBase :: "(identifier * vname * val option) \<Rightarrow> (identifier * vname * basicType option)"
and
  valToBase :: "val \<Rightarrow> basicType"
  where
    (* Map a single struct entry (containing a val) to basic types *)
    "structEntryToBase (tName, vName, None)       = (tName, vName, None)"
  | "structEntryToBase (tName, vName, Some vVal) = (tName, vName, Some (valToBase vVal))"
    (* Map the remaining vals to basic types *)
  | "valToBase (BOOL b)         = (BBOOL b)"
  | "valToBase (IINT n)         = (BIINT n)"
  | "valToBase (UINT n)         = (BUINT n)"
  | "valToBase (SINT n)         = (BSINT n)"
  | "valToBase (VINT n)         = (BVINT n)"
  | "valToBase (ERROR e)        = (BERROR e)"
  | "valToBase (MATCH m)        = (BMATCH m)"
  | "valToBase (STRING s)       = (BSTRING s)"
  | "valToBase (STRUCT entries) = (DSTRUCT (map structEntryToBase entries))" (* Recurse on structs *)

(* ============================================================================================================== *)
(*                                         STRUCT EQUIVALENCE PROOFS                                              *)
(* ============================================================================================================== *)

(* Converting to val and back to base is the same *)
lemma equiv1: "valToBase (baseToVal b) = b"
proof (induction b)
  case (DSTRUCT x)
  note ih = this(1)
  then show ?case
    apply (simp)
    apply (rule list.map_cong[of _ _ _ id, simplified])
     apply (rule refl)
    using ih
    by (smt comp_def option.set_intros snd_conv snds.intros structEntryToBase.simps(1) structEntryToBase.simps(2) structEntryToVal.elims)
qed simp+

(* Converting to base and back to val is the same *)
lemma equiv2: "baseToVal (valToBase v) = v"
proof (induction v)
  case (STRUCT x)
  note ih = this(1)
  then show ?case
    apply (simp)
    apply (rule list.map_cong[of _ _ _ id, simplified])
     apply (rule refl)
    using ih
    by (smt comp_apply option.set_intros prod_set_simps(2) singletonI structEntryToBase.cases structEntryToBase.simps(1) structEntryToBase.simps(2) structEntryToVal.simps(1) structEntryToVal.simps(2))
qed simp+

(* ============================================================================================================== *)
(*                                       STRUCT MEMBER ACCESS FUNCTIONS                                           *)
(* ============================================================================================================== *)

(* Update the named member field of a struct. Iterates through fields of enum and stores the already-seen values
   in the buildup field. When field is found will combine buildup and remainder after updating and return. *)
fun updateStruct :: "val \<Rightarrow> val \<Rightarrow> ((identifier * vname * (val option)) list) \<Rightarrow> identifier \<Rightarrow> val option" where
    "updateStruct (STRUCT struct) newVal buildup valName = (case struct of
        ([])                    \<Rightarrow> None
      | ((tp, nm, vl) # remain) \<Rightarrow> if (nm = valName) then Some (STRUCT (buildup @ ((tp, nm, Some newVal) # remain))) else (updateStruct (STRUCT remain) newVal ((tp, nm, vl) # buildup) valName))"
  | "updateStruct _ _ _ _ = None"

(* Will retrieve named member field's value of a struct or enum (all datatypes with named member fields) *)
fun getStructMem :: "val \<Rightarrow> vname \<Rightarrow> val option" where
    "getStructMem (STRUCT []) vName = None"
  | "getStructMem (STRUCT ((tp, nm, None) # rst)) vName = (getStructMem (STRUCT rst) vName)"
  | "getStructMem (STRUCT ((tp, nm, Some vl) # rst)) vName = (if nm = vName then (Some vl) else (getStructMem (STRUCT rst) vName))"
  | "getStructMem _ vName = None"

lemma struct_mem_determ: "getStructMem strct vName = v \<Longrightarrow> getStructMem strct vName = v' \<Longrightarrow> v' = v"
  by simp

(* ============================================================================================================== *)
(*                                   CONCRETE VALUE EVALUATION FUNCTIONS                                          *)
(* ============================================================================================================== *)

inductive eval :: "expression \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
(* =============== Base types =============== *)
    RBASE: "eval (BASE b) s (baseToVal b)"
(* =============== Miscellaneous expressions =============== *)
  | TERNTRUE:  "eval e1 s (BOOL b) \<Longrightarrow> b = True \<Longrightarrow> eval e2 s v \<Longrightarrow> eval (TernExpr e1 e2 e3) s v"
  | TERNFALSE: "eval e1 s (BOOL b) \<Longrightarrow> b = False \<Longrightarrow> eval e3 s v \<Longrightarrow> eval (TernExpr e1 e2 e3) s v"
  | STRUCTMEM: "eval e1 s (STRUCT entries) \<Longrightarrow> getStructMem (STRUCT entries) varName = (Some v) \<Longrightarrow> eval (ExprMem e1 varName) s v"
(* =============== Variable mapping  =============== *)
  | NAMEDVAR: "eval (NamedVar varName) s (s varName)"
(* =============== Operations that yield a single bit (SBIT)  =============== *)
          (* Empty for now *)
(* =============== Operations that yield a boolean (BOOL)  =============== *)
  | ULNEB: "eval e1 s (BOOL b) \<Longrightarrow> eval (UNA_LNE e1) s (BOOL (\<not>b))"
    (* Boolean operations *)
  | BEQUB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (b1 = b2))"
(* Very strange but boolean inequality breaks code generation? *)
(*  | BNEQB: "eval e1 s (BOOL b1) \<Longrightarrow> eval e2 s (BOOL b2) \<Longrightarrow> eval (BIN_EQU e1 e2) s (BOOL (b1 \<noteq> b2))" *)
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

declare eval.intros[simp, intro]
lemmas eval_induct = eval.induct[split_format(complete)]

inductive_cases [elim!]: "eval (BASE b) s v" "eval (TernExpr e1 e2 e3) s v" "eval (NamedVar i) s v"
"eval (UNA_LNE e) s v" "eval (UNA_COM e) s v" "eval (UNA_NEG e) s v" "eval (UNA_POS e) s v" "eval (BIN_MUL e1 e2) s v"
"eval (BIN_DIV e1 e2) s v" "eval (BIN_MOD e1 e2) s v" "eval (BIN_ADD e1 e2) s v" "eval (BIN_MIN e1 e2) s v" "eval (BIN_AND e1 e2) s v"
"eval (BIN_XOR e1 e2) s v" "eval (BIN_LOR e1 e2) s v" "eval (BIN_LEQ e1 e2) s v" "eval (BIN_GEQ e1 e2) s v" "eval (BIN_LES e1 e2) s v"
"eval (BIN_GRE e1 e2) s v" "eval (BIN_NEQ e1 e2) s v" "eval (BIN_EQU e1 e2) s v" "eval (BIN_FAN e1 e2) s v" "eval (BIN_FOR e1 e2) s v"
"eval (ExprMem e i) s v"

lemma eval_deterministic: "(eval e s v) \<Longrightarrow> (eval e s v') \<Longrightarrow> (v' = v)"
proof (induction arbitrary: v' rule: eval_induct)
  case (STRUCTMEM e1 s entries varName v)
  note th = this(4)
  then show ?case
    using STRUCTMEM.IH STRUCTMEM.hyps(2) by auto
qed blast+

lemma if_mem_exprMem: "eval expr s strct \<Longrightarrow> getStructMem strct vName = Some v \<Longrightarrow> eval (ExprMem expr vName) s v"
  by (smt STRUCTMEM getStructMem.elims option.distinct(1))

code_pred eval .

(* ============================================================================================================== *)
(*                                                 STATE MAPPING                                                  *)
(* ============================================================================================================== *)

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. (UINT 0)"
syntax
  "_State" :: "updbinds \<Rightarrow> 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

end
