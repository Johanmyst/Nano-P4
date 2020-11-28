theory NP4_Direction_Semantics
  imports
  Complex_Main
  NP4_Direction_Values
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
    or ill-typed P4 programs will yield no such tree.

    Note: the state is a mapping from vnames to values (vals) *)

begin
(* ============================================================================================================== *)
(*                                      SMALL STEP SEMANTICS RULES                                                *)
(* ============================================================================================================== *)

(* The way P4 statements update the state and progress. The natural number included is to prove
   that computation always progresses. With every step of the computation this number always
   decreases, indicating progression and ultimately termination. Note that method invocations and
   switch statements are omitted as these can be modelled with the present statements as well. *)
inductive small_step :: "(statOrDecl * state * nat) \<Rightarrow> (statOrDecl * state * nat) \<Rightarrow> bool"
 (infix "\<leadsto>" 55) where
    Exit:       "(ExitStat, s, n) \<leadsto> (EmptyStat, s, n-1)"
  | CondTrue:   "eval e s (BOOL True) \<Longrightarrow> ((ConditionalStat e stmt1 stmt2), s, n) \<leadsto> (stmt1, s, n-1)"
  | CondFalse:  "eval e s (BOOL False) \<Longrightarrow> ((ConditionalStat e stmt1 stmt2), s, n) \<leadsto> (stmt2, s, n-1)"
  | EmptyBlock: "(BlockStat [], s, n) \<leadsto> (EmptyStat, s, n-1)" 
  | EmptyFirst: "(BlockStat (EmptyStat # rest), s, n) \<leadsto> (BlockStat rest, s, n-1)"
  | FullBlock:  "(stmt, s, n) \<leadsto> (stmt', s', n') \<Longrightarrow> n' \<le> n \<Longrightarrow> (BlockStat (stmt # rest), s, n) \<leadsto> (BlockStat (stmt' # rest), s', n')"
  | Assign:     "eval e s v \<Longrightarrow> (AssignmentStat (NameLVal vName) e, s, n) \<leadsto> (EmptyStat, s (vName := v), n-1)"
  | VarDecl:    "(VariableDecl (NameLVal vName) (None), s, n) \<leadsto> (EmptyStat, s, n-1)"
  | VarInit:    "eval e s v \<Longrightarrow> (VariableDecl (NameLVal vName) (Some e), s, n) \<leadsto> (EmptyStat, s (vName := v), n-1)"
  | ConstInit:  "eval e s v \<Longrightarrow> (ConstantDecl (NameLVal vName) e, s, n) \<leadsto> (EmptyStat, s (vName := v), n-1)"

declare small_step.intros[simp, intro]

inductive_cases [elim!]: "(EmptyStat, s, n) \<leadsto> ct" "(ExitStat, s, n) \<leadsto> ct" "(ConditionalStat e stmt1 stmt2, s, n) \<leadsto> ct"
  "(BlockStat stmts, s, n) \<leadsto> ct" "(AssignmentStat l e, s, n) \<leadsto> ct" "(VariableDecl l e, s, n) \<leadsto> ct" "(ConstantDecl l e, s, n) \<leadsto> ct"

lemmas small_step_induct = small_step.induct[split_format(complete)]

lemma small_step_deterministic: "cs \<leadsto> cs' \<Longrightarrow> cs \<leadsto> cs'' \<Longrightarrow> cs' = cs''"
proof (induction arbitrary: cs'' rule: small_step.induct)
next case (CondTrue e s stmt1 stmt2 n) thus ?case using eval_deterministic by auto
next case (CondFalse e s stmt1 stm2 n stmt2) thus ?case using eval_deterministic by auto
next case (Assign e s v vName n) thus ?case using eval_deterministic by auto
next case (VarDecl vName s n) thus ?case using eval_deterministic by auto
next case (VarInit e s v vName n) thus ?case using eval_deterministic by auto
next case (ConstInit e s v vName n) thus ?case using eval_deterministic by auto
qed auto

lemma step_equal_or_smaller: "(c, s, n) \<leadsto> (c', s', n') \<Longrightarrow> n' \<le> n"
  apply (induction c rule: statOrDecl.induct)
  apply (auto)
  done

lemma bigger_no_progress: "n' > n \<Longrightarrow> \<not>((c, s, n) \<leadsto> (c', s', n'))"
  by (meson leD step_equal_or_smaller)

abbreviation equiv_stmt :: "statOrDecl \<Rightarrow> statOrDecl \<Rightarrow> bool" (infix "~" 50) where
  "c ~ c' \<equiv> (\<forall>s t. ((c, s) \<leadsto> t) = ((c', s) \<leadsto> t))"

lemma equiv_refl:  "c ~ c" by simp
lemma equiv_sym:   "(c ~ c') = (c' ~ c)" by auto
lemma equiv_trans: "(c ~ c') \<Longrightarrow> (c' ~ c'') \<Longrightarrow> (c ~ c'')" by simp

code_pred small_step .

(* ============================================================================================================== *)
(*                                        REFLEXIVE TRANSITIVE CLOSURE                                            *)
(* ============================================================================================================== *)

(* Define the reflexive transitive closure on the signature of the small-step semantics. *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "('a \<Rightarrow> 'a \<Rightarrow> bool)" where
refl:   "star r x x" |
step:   "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

hide_fact (open) refl step

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply (assumption)
  apply (metis star.step)
  done

lemmas star_induct = star.induct[of "r:: 'a*'b*'c \<Rightarrow> 'a*'b*'c \<Rightarrow> bool", split_format(complete)]

declare star.refl[simp, intro]

lemma star_step1[simp, intro]: "r x y \<Longrightarrow> star r x y"
  by (metis star.refl star.step)

code_pred star .

(* The reflexive transitive closure of the small step function yields whether a state is reachable in any number of
   steps from the starting state and thereby models complete execution. *)
abbreviation small_steps :: "(statOrDecl * state * nat) \<Rightarrow> (statOrDecl * state * nat) \<Rightarrow> bool" (infix "\<leadsto>*" 55)
  where "x \<leadsto>* y \<equiv> star small_step x y"

(* ============================================================================================================== *)
(*                                       REDUCING NUMBER PROGRESS PROOFS                                          *)
(* ============================================================================================================== *)

lemma star_equal_or_smaller: "(c, s, n) \<leadsto>* (c', s', n') \<Longrightarrow> n' \<le> n"
proof (induction rule: star_induct)
     case (refl a a b) thus ?case by simp
next case (step a a b a a b a a b) thus ?case by (meson dual_order.trans step_equal_or_smaller)
qed

lemma star_bigger: "n' > n \<Longrightarrow> \<not>((c, s, n) \<leadsto>* (c', s', n'))"
  by (meson leD star_equal_or_smaller)

fun small_steps_n :: "(statOrDecl * state * nat) \<Rightarrow> nat \<Rightarrow> (statOrDecl * state * nat) \<Rightarrow> bool" ("_ \<leadsto>'(_') _" [55,0,55] 55)
  where
    "(cs \<leadsto>(0) cs') = (cs' = cs)"
  | "(cs \<leadsto>(Suc n) cs'') = (\<exists>cs'. cs \<leadsto> cs' \<and> cs' \<leadsto>(n) cs'')"

lemma steps_n_if_star: "cs \<leadsto>* cs' \<Longrightarrow> \<exists>n. cs \<leadsto>(n) cs'"
proof (induction rule: star.induct)
  case (refl x) thus ?case using small_steps_n.simps(1) by blast
next
  case (step x y z) thus ?case using small_steps_n.simps(2) by blast
qed

lemma star_if_steps_n: "cs \<leadsto>(n) cs' \<Longrightarrow> cs \<leadsto>* cs'"
  apply (induction n arbitrary: cs)
  apply (simp)
  apply (meson small_steps_n.simps(2) star.simps)
  done

lemma steps_n_decreases: "(c, s, n) \<leadsto>(x) (c', s', n') \<Longrightarrow> n' \<le> n"
  using star_equal_or_smaller star_if_steps_n by blast

lemma steps_n_bigger: "n' > n \<Longrightarrow> \<not>((c, s, n) \<leadsto>(x) (c', s', n'))"
  by (meson leD steps_n_decreases)

(* ============================================================================================================== *)
(*                                          TYPING SYSTEM DEFINITION                                              *)
(* ============================================================================================================== *)

datatype ty = SBITty | UINTty | SINTty | IINTty | VINTty | BOOLty | STRINGty | ERRORty | MATCHty

(* Helper function to yield type from val object *)
fun getValType :: "val \<Rightarrow> ty" where
    "getValType (SBIT s) = SBITty"
  | "getValType (UINT n) = UINTty"
  | "getValType (SINT n) = SINTty"
  | "getValType (IINT n) = IINTty"
  | "getValType (VINT n) = VINTty"
  | "getValType (BOOL b) = BOOLty"
  | "getValType (STRING s) = STRINGty"
  | "getValType (ERROR e) = ERRORty"
  | "getValType (MATCH m) = MATCHty"

(* Mapping from a variable name to a type symbol *)
type_synonym typeEnv = "vname \<Rightarrow> ty"

(* The typing environment for expressions. If a case is defined it implies the expression is well-typed
   given the context of the typing environment. *)
inductive exprTyping :: "typeEnv \<Rightarrow> expression \<Rightarrow> ty \<Rightarrow> bool" ("(1_/ \<turnstile>/ (_ ::/ _))" [50,0,50] 50) where
(* =============== Base types =============== *)
    BIT_ty:    "\<Gamma> \<turnstile> (BASE (BSBIT b))   :: SBITty"
  | UINT_ty:   "\<Gamma> \<turnstile> (BASE (BUINT n))   :: UINTty"
  | SINT_ty:   "\<Gamma> \<turnstile> (BASE (BSINT n))   :: SINTty"
  | IINT_ty:   "\<Gamma> \<turnstile> (BASE (BIINT n))   :: IINTty"
  | VINT_ty:   "\<Gamma> \<turnstile> (BASE (BVINT n))   :: VINTty"
  | BOOL_ty:   "\<Gamma> \<turnstile> (BASE (BBOOL b))   :: BOOLty"
  | STRING_ty: "\<Gamma> \<turnstile> (BASE (BSTRING s)) :: STRINGty"
  | ERROR_ty:  "\<Gamma> \<turnstile> (BASE (BERROR e))  :: ERRORty"
  | MATCH_ty:  "\<Gamma> \<turnstile> (BASE (BMATCH m))  :: MATCHty"
(* =============== Miscellaneous expressions =============== *)
  | TERNEXPR_ty: "\<Gamma> \<turnstile> e1 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: \<tau> \<Longrightarrow> \<Gamma> \<turnstile> e3 :: \<tau> \<Longrightarrow> \<Gamma> \<turnstile> TernExpr e1 e2 e3 :: \<tau>"
(* =============== Variable mapping  =============== *)
  | VAR_ty: "\<Gamma> \<turnstile> NamedVar vName :: \<Gamma> vName"
(* =============== Operations that yield a single bit (SBIT)  =============== *)
          (* Empty for now *)
(* =============== Operations that yield a boolean (BOOL)  =============== *)
    (* Boolean operations *)
  | ULNEB_ty: "\<Gamma> \<turnstile> e1 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> UNA_LNE e1 :: BOOLty"
  | BEQUB_ty: "\<Gamma> \<turnstile> e1 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> BIN_EQU e1 e2 :: BOOLty"
(* Boolean equality check yields derivation error; code cannot be generated for inductive predicate eval *)
(*| BNEQB_ty: "\<Gamma> \<turnstile> e1 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> BIN_NEQ e1 e2 :: BOOLty" *)
  | BFANB_ty: "\<Gamma> \<turnstile> e1 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> BIN_FAN e1 e2 :: BOOLty"
  | BFORB_ty: "\<Gamma> \<turnstile> e1 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: BOOLty \<Longrightarrow> \<Gamma> \<turnstile> BIN_FOR e1 e2 :: BOOLty"
    (* Signed integer operations *)
  | BEQUS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_EQU e1 e2 :: BOOLty"
  | BNEQS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_NEQ e1 e2 :: BOOLty"
  | BLEQS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_LEQ e1 e2 :: BOOLty"
  | BGEQS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_GEQ e1 e2 :: BOOLty"
  | BLESS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_LES e1 e2 :: BOOLty"
  | BGRES_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_GRE e1 e2 :: BOOLty"
    (* Unsigned integer operations *)
  | BEQUU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_EQU e1 e2 :: BOOLty"
  | BNEQU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_NEQ e1 e2 :: BOOLty"
  | BLEQU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_LEQ e1 e2 :: BOOLty"
  | BGEQU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_GEQ e1 e2 :: BOOLty"
  | BLESU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_LES e1 e2 :: BOOLty"
  | BGREU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_GRE e1 e2 :: BOOLty"
    (* Infinite precision integer operations *)
  | BEQUI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_EQU e1 e2 :: BOOLty"
  | BNEQI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_NEQ e1 e2 :: BOOLty"
  | BLEQI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_LEQ e1 e2 :: BOOLty"
  | BGEQI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_GEQ e1 e2 :: BOOLty"
  | BLESI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_LES e1 e2 :: BOOLty"
  | BGREI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_GRE e1 e2 :: BOOLty"
    (* Variable size bitstring operations *)
  | BEQUV_ty: "\<Gamma> \<turnstile> e1 :: VINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: VINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_EQU e1 e2 :: BOOLty"
  | BNEQV_ty: "\<Gamma> \<turnstile> e1 :: VINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: VINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_NEQ e1 e2 :: BOOLty"
(* =============== Operations that yield an unsigned integer (UINT)  =============== *)
  | UNEGU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> UNA_NEG e1 :: UINTty"
  | UPOSU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> UNA_POS e1 :: UINTty"
  | UCOMU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> UNA_COM e1 :: UINTty"
  | BADDU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_ADD e1 e2 :: UINTty"
  | BMINU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_MIN e1 e2 :: UINTty"
  | BANDU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_AND e1 e2 :: UINTty"
  | BXORU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_XOR e1 e2 :: UINTty"
  | BLORU_ty: "\<Gamma> \<turnstile> e1 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: UINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_LOR e1 e2 :: UINTty"
(* =============== Operations that yield a signed integer (SINT)  =============== *)
  | UNEGS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> UNA_NEG e1 :: SINTty"
  | UPOSS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> UNA_POS e1 :: SINTty"
  | BADDS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_ADD e1 e2 :: SINTty"
  | BMINS_ty: "\<Gamma> \<turnstile> e1 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: SINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_MIN e1 e2 :: SINTty"
(* =============== Operations that yield an infinite-precision integer (IINT)  =============== *)
  | UNEGI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> UNA_NEG e1 :: IINTty"
  | UPOSI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> UNA_POS e1 :: IINTty"
  | BADDI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_ADD e1 e2 :: IINTty"
  | BMINI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_MIN e1 e2 :: IINTty"
  | BMULI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_MUL e1 e2 :: IINTty"
  | BDIVI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_DIV e1 e2 :: IINTty"
  | BMODI_ty: "\<Gamma> \<turnstile> e1 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> e2 :: IINTty \<Longrightarrow> \<Gamma> \<turnstile> BIN_MOD e1 e2 :: IINTty"
(* =============== Operations that yield a variable-width integer (VINT)  =============== *)
          (* Empty for now *)

declare exprTyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> BASE b :: \<tau>" "\<Gamma> \<turnstile> UNA_LNE e1 :: \<tau>" "\<Gamma> \<turnstile> UNA_COM e1 :: \<tau>" "\<Gamma> \<turnstile> UNA_NEG e1 :: \<tau>" "\<Gamma> \<turnstile> UNA_POS e1 :: \<tau>"
  "\<Gamma> \<turnstile> BIN_DIV e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_MOD e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_ADD e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_MIN e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_AND e1 e2 :: \<tau>"
  "\<Gamma> \<turnstile> BIN_XOR e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_LOR e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_LEQ e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_GEQ e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_LES e1 e2 :: \<tau>"
  "\<Gamma> \<turnstile> BIN_GRE e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_NEQ e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_EQU e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_FAN e1 e2 :: \<tau>" "\<Gamma> \<turnstile> BIN_FOR e1 e2 :: \<tau>"
  "\<Gamma> \<turnstile> BIN_MUL e1 e2 :: \<tau>" "\<Gamma> \<turnstile> TernExpr e1 e2 e3 :: \<tau>" "\<Gamma> \<turnstile> NamedVar v :: \<tau>"

lemma expr_typing_deterministic: "\<Gamma> \<turnstile> e :: t \<Longrightarrow> \<Gamma> \<turnstile> e :: t' \<Longrightarrow> t' = t"
  apply (induction arbitrary: t' rule: exprTyping.induct)
    apply (blast+)
  done

code_pred exprTyping .

(* The typing environment for statements. If a case is defined it implies the statement is well-typed
   given the context of the typing environment. *)
inductive stmtTyping :: "typeEnv \<Rightarrow> statOrDecl \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
    Empty_ty: "\<Gamma> \<Turnstile> EmptyStat"
  | Exit_ty: "\<Gamma> \<Turnstile> ExitStat"
  | Conditional_ty: "\<Gamma> \<turnstile> e :: (BOOLty) \<Longrightarrow> \<Gamma> \<Turnstile> stmt1 \<Longrightarrow> \<Gamma> \<Turnstile> stmt2 \<Longrightarrow> \<Gamma> \<Turnstile> (ConditionalStat e stmt1 stmt2)"
  | Block_Empty_ty: "\<Gamma> \<Turnstile> (BlockStat [])"
  | BlockFull_ty: "\<Gamma> \<Turnstile> stmt \<Longrightarrow> \<Gamma> \<Turnstile> (BlockStat rest) \<Longrightarrow> \<Gamma> \<Turnstile> (BlockStat (stmt # rest))"
  | Assign_ty: "\<Gamma> \<turnstile> e :: \<Gamma> (vName) \<Longrightarrow> \<Gamma> \<Turnstile> (AssignmentStat (NameLVal vName) e)"
  | VarDecl_ty: "\<Gamma> \<Turnstile> (VariableDecl (NameLVal vName) (None))"
(* Remove \<Gamma> (vName) in below with just \<tau> because they should allow to change the type *)
  | VarInit_ty: "\<Gamma> \<turnstile> e :: \<Gamma> (vName) \<Longrightarrow> \<Gamma> \<Turnstile> (VariableDecl (NameLVal vName) (Some e))"
  | ConstInit_ty: "\<Gamma> \<turnstile> e :: \<Gamma> (vName) \<Longrightarrow> \<Gamma> \<Turnstile> (ConstantDecl (NameLVal vName) (e))"

declare stmtTyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<Turnstile> ExitStat" "\<Gamma> \<Turnstile> ConditionalStat e stmt1 stmt2" "\<Gamma> \<Turnstile> BlockStat l" "\<Gamma> \<Turnstile> AssignmentStat n e" "\<Gamma> \<Turnstile> VariableDecl n e"
  "\<Gamma> \<Turnstile> ConstantDecl n e"

(* The typing environment for the state. It states that a state is correctly typed if and only if the type
   of all variables in the state correspond with the typing environment. *)
definition stateTyping :: "typeEnv \<Rightarrow> state \<Rightarrow> bool" (infix "\<TTurnstile>" 50)
  where "\<Gamma> \<TTurnstile> s \<longleftrightarrow> (\<forall>x. getValType (s x) = \<Gamma> x)"

code_pred stmtTyping .

(* ============================================================================================================== *)
(*                                            TYPING SYSTEM PROOF                                                 *)
(* ============================================================================================================== *)

(* Prove that if the type of a particular variable is a given type, there always exists a concrete value with the
   matching type to satisfy the constraint. *)
lemma type_eq_SBIT[simp]:   "getValType v = SBITty    \<longleftrightarrow> (\<exists>b. v = SBIT b)" by   (cases v) simp_all
lemma type_eq_UINT[simp]:   "getValType v = UINTty    \<longleftrightarrow> (\<exists>i. v = UINT i)" by   (cases v) simp_all
lemma type_eq_SINT[simp]:   "getValType v = SINTty    \<longleftrightarrow> (\<exists>i. v = SINT i)" by   (cases v) simp_all
lemma type_eq_IINT[simp]:   "getValType v = IINTty    \<longleftrightarrow> (\<exists>i. v = IINT i)" by   (cases v) simp_all
lemma type_eq_VINT[simp]:   "getValType v = VINTty    \<longleftrightarrow> (\<exists>i. v = VINT i)" by   (cases v) simp_all
lemma type_eq_BOOL[simp]:   "getValType v = BOOLty    \<longleftrightarrow> (\<exists>i. v = BOOL i)" by   (cases v) simp_all
lemma type_eq_STRING[simp]: "getValType v = STRINGty  \<longleftrightarrow> (\<exists>i. v = STRING i)" by (cases v) simp_all
lemma type_eq_ERROR[simp]:  "getValType v = ERRORty   \<longleftrightarrow> (\<exists>i. v = ERROR i)" by  (cases v) simp_all
lemma type_eq_MATCH[simp]:  "getValType v = MATCHty   \<longleftrightarrow> (\<exists>i. v = MATCH i)" by  (cases v) simp_all

(* Theorem to state that if expression are well-typed, the result is necessarily also well-typed. *)
theorem expr_preservation: "\<Gamma> \<turnstile> expr :: \<tau> \<Longrightarrow> eval expr s v \<Longrightarrow> \<Gamma> \<TTurnstile> s \<Longrightarrow> getValType v = \<tau>"
  apply (induction arbitrary: v rule: exprTyping.induct)
    apply (fastforce simp: stateTyping_def)+
  done

lemma expr_progress: "\<Gamma> \<turnstile> e :: \<tau> \<Longrightarrow> \<Gamma> \<TTurnstile> s \<Longrightarrow> \<exists>v. eval e s v"
proof (induction rule: exprTyping.induct)
     case (BIT_ty \<Gamma> b) thus ?case by (metis RBIT0 RBIT1 old.nat.exhaust)
next case (UINT_ty \<Gamma> n) thus ?case using RUINT by blast
next case (SINT_ty \<Gamma> n) thus ?case using RSINT by blast
next case (IINT_ty \<Gamma> n) thus ?case using RIINT by blast
next case (VINT_ty \<Gamma> n) thus ?case using RVINT by blast
next case (BOOL_ty \<Gamma> b) thus ?case using RBOOL by blast
next case (STRING_ty \<Gamma> s) thus ?case using RSTRING by blast
next case (ERROR_ty \<Gamma> e) thus ?case using RERROR by blast
next case (MATCH_ty \<Gamma> m) thus ?case using RMATCH by blast
next case (TERNEXPR_ty \<Gamma> e1 e2 \<tau> e3) thus ?case by (metis TERNFALSE TERNTRUE expr_preservation type_eq_BOOL)
next case (VAR_ty \<Gamma> vName) thus ?case using NAMEDVAR by blast 
next case (ULNEB_ty \<Gamma> e1) thus ?case by (metis ULNEB expr_preservation type_eq_BOOL)
next case (BEQUB_ty \<Gamma> e1 e2) thus ?case by (metis BEQUB expr_preservation type_eq_BOOL)
next case (BFANB_ty \<Gamma> e1 e2) thus ?case by (metis BFANB expr_preservation type_eq_BOOL)
next case (BFORB_ty \<Gamma> e1 e2) thus ?case by (metis BFORB expr_preservation type_eq_BOOL)
next case (BEQUS_ty \<Gamma> e1 e2) thus ?case by (metis BEQUS expr_preservation type_eq_SINT)
next case (BNEQS_ty \<Gamma> e1 e2) thus ?case by (metis BNEQS expr_preservation type_eq_SINT)
next case (BLEQS_ty \<Gamma> e1 e2) thus ?case by (metis BLEQS expr_preservation type_eq_SINT)
next case (BGEQS_ty \<Gamma> e1 e2) thus ?case by (metis BGEQS expr_preservation type_eq_SINT)
next case (BLESS_ty \<Gamma> e1 e2) thus ?case by (metis BLESS expr_preservation type_eq_SINT)
next case (BGRES_ty \<Gamma> e1 e2) thus ?case by (metis BGRES expr_preservation type_eq_SINT)
next case (BEQUU_ty \<Gamma> e1 e2) thus ?case by (metis BEQUU expr_preservation type_eq_UINT)
next case (BNEQU_ty \<Gamma> e1 e2) thus ?case by (metis BNEQU expr_preservation type_eq_UINT)
next case (BLEQU_ty \<Gamma> e1 e2) thus ?case by (metis BLEQU expr_preservation type_eq_UINT)
next case (BGEQU_ty \<Gamma> e1 e2) thus ?case by (metis BGEQU expr_preservation type_eq_UINT)
next case (BLESU_ty \<Gamma> e1 e2) thus ?case by (metis BLESU expr_preservation type_eq_UINT)
next case (BGREU_ty \<Gamma> e1 e2) thus ?case by (metis BGREU expr_preservation type_eq_UINT)
next case (BEQUI_ty \<Gamma> e1 e2) thus ?case by (metis BEQUI expr_preservation type_eq_IINT)
next case (BNEQI_ty \<Gamma> e1 e2) thus ?case by (metis BNEQI expr_preservation type_eq_IINT)
next case (BLEQI_ty \<Gamma> e1 e2) thus ?case by (metis BLEQI expr_preservation type_eq_IINT)
next case (BGEQI_ty \<Gamma> e1 e2) thus ?case by (metis BGEQI expr_preservation type_eq_IINT)
next case (BLESI_ty \<Gamma> e1 e2) thus ?case by (metis BLESI expr_preservation type_eq_IINT)
next case (BGREI_ty \<Gamma> e1 e2) thus ?case by (metis BGREI expr_preservation type_eq_IINT)
next case (BEQUV_ty \<Gamma> e1 e2) thus ?case by (metis BEQUV expr_preservation type_eq_VINT)
next case (BNEQV_ty \<Gamma> e1 e2) thus ?case by (metis BNEQV expr_preservation type_eq_VINT)
next case (UNEGS_ty \<Gamma> e1) thus ?case by (metis UNEGS expr_preservation type_eq_SINT)
next case (UPOSS_ty \<Gamma> e1) thus ?case by (metis UPOSS expr_preservation type_eq_SINT)
next case (BADDS_ty \<Gamma> e1 e2) thus ?case by (metis BADDS expr_preservation type_eq_SINT)
next case (BMINS_ty \<Gamma> e1 e2) thus ?case by (metis BMINS expr_preservation type_eq_SINT)
next case (UNEGU_ty \<Gamma> e1) thus ?case by (metis UNEGU expr_preservation type_eq_UINT)
next case (UPOSU_ty \<Gamma> e1) thus ?case by (metis UPOSU expr_preservation type_eq_UINT)
next case (UCOMU_ty \<Gamma> e1) thus ?case by (metis UCOMU expr_preservation type_eq_UINT)
next case (BADDU_ty \<Gamma> e1 e2) thus ?case by (metis BADDU expr_preservation type_eq_UINT)
next case (BMINU_ty \<Gamma> e1 e2) thus ?case by (metis BMINU expr_preservation type_eq_UINT)
next case (BANDU_ty \<Gamma> e1 e2) thus ?case by (metis BANDU expr_preservation type_eq_UINT)
next case (BXORU_ty \<Gamma> e1 e2) thus ?case by (metis BXORU expr_preservation type_eq_UINT)
next case (BLORU_ty \<Gamma> e1 e2) thus ?case by (metis BLORU expr_preservation type_eq_UINT)
next case (UNEGI_ty \<Gamma> e1) thus ?case by (metis UNEGI expr_preservation type_eq_IINT)
next case (UPOSI_ty \<Gamma> e1) thus ?case by (metis UPOSI expr_preservation type_eq_IINT)
next case (BADDI_ty \<Gamma> e1 e2) thus ?case by (metis BADDI expr_preservation type_eq_IINT)
next case (BMINI_ty \<Gamma> e1 e2) thus ?case by (metis BMINI expr_preservation type_eq_IINT)
next case (BMULI_ty \<Gamma> e1 e2) thus ?case by (metis BMULI expr_preservation type_eq_IINT)
next case (BDIVI_ty \<Gamma> e1 e2) thus ?case by (metis BDIVI expr_preservation type_eq_IINT)
next case (BMODI_ty \<Gamma> e1 e2) thus ?case by (metis BMODI expr_preservation type_eq_IINT)
qed

theorem progress: "\<Gamma> \<Turnstile> c \<Longrightarrow> \<Gamma> \<TTurnstile> s \<Longrightarrow> c \<noteq> EmptyStat \<Longrightarrow> \<exists>cs'. (c, s, n) \<leadsto> cs'"
proof (induction rule: stmtTyping.induct)
     case (Conditional_ty \<Gamma> e stmnt1 stmnt2) thus ?case by (smt CondFalse CondTrue expr_preservation expr_progress type_eq_BOOL)
next case (BlockFull_ty \<Gamma> firstStat remainder) thus ?case by (metis (full_types) EmptyFirst FullBlock old.prod.exhaust step_equal_or_smaller)
next case (Block_Empty_ty \<Gamma>) thus ?case using expr_progress by blast
next case (Assign_ty \<Gamma> e vName) thus ?case using expr_progress by blast
next case (VarInit_ty \<Gamma> e vName) thus ?case using expr_progress by blast
next case (ConstInit_ty \<Gamma> e vName) thus ?case using expr_progress by blast
qed blast+

theorem state_preservation: "(c, s, n) \<leadsto> (c', s', n') \<Longrightarrow> \<Gamma> \<Turnstile> c \<Longrightarrow> \<Gamma> \<TTurnstile> s \<Longrightarrow> \<Gamma> \<TTurnstile> s'"
proof (induct rule: small_step_induct)
     case (Assign e s v vName n) thus ?case using expr_preservation stateTyping_def by fastforce
next case (VarDecl vName s n) thus ?case using expr_preservation stateTyping_def by fastforce
next case (VarInit e s v vName n) thus ?case using expr_preservation stateTyping_def by fastforce
next case (ConstInit e s v vName n) thus ?case using expr_preservation stateTyping_def by fastforce
qed blast+

theorem stmt_preservation: "(c, s, n) \<leadsto> (c', s', n') \<Longrightarrow> \<Gamma> \<Turnstile> c \<Longrightarrow> \<Gamma> \<Turnstile> c'"
proof (induction rule: small_step_induct)
  case (FullBlock stmt s n stmt' s' n' rest) thus ?case
  proof -
    have "\<Gamma> \<Turnstile> stmt" using FullBlock.prems by blast
    then have "\<Gamma> \<Turnstile> stmt'" by (simp add: FullBlock.IH \<open>\<Gamma> \<Turnstile> stmt\<close>)
    then have "\<Gamma> \<Turnstile> (BlockStat (stmt # rest))" by (simp add: FullBlock.prems)
    then have "\<Gamma> \<Turnstile> (BlockStat (stmt' # rest))" using \<open>\<Gamma> \<Turnstile> stmt'\<close> by blast
    thus ?case by auto
  qed
qed auto

theorem type_sound: "(c, s, n) \<leadsto>* (c', s', n') \<Longrightarrow> \<Gamma> \<Turnstile> c \<Longrightarrow> \<Gamma> \<TTurnstile> s \<Longrightarrow> c' \<noteq> EmptyStat \<Longrightarrow> \<exists>cs''. (c', s', n') \<leadsto> cs''"
proof (induction rule: star_induct)
     case (refl a a b) thus ?case using progress by auto
next case (step a a b a a b a a b) thus ?case using state_preservation stmt_preservation by auto
qed

(* ============================================================================================================== *)
(*                                           FINAL STATE PROPERTIES                                               *)
(* ============================================================================================================== *)

(* Final state is defined as the state from which there is nowhere to go anymore *)
definition "final cs \<longleftrightarrow> (\<nexists>cs'. cs \<leadsto> cs')"

lemma EmptyFinal: "c = EmptyStat \<Longrightarrow> final (c, s, n)" using final_def by blast
lemma FinalEmpty: "final (c, s, n) \<Longrightarrow> \<Gamma> \<Turnstile> c \<Longrightarrow> \<Gamma> \<TTurnstile> s \<Longrightarrow> c = EmptyStat" using final_def progress by blast


(* ============================================================================================================== *)
(*                                          REACHABILITY PROPERTIES                                               *)
(* ============================================================================================================== *)

definition reachable :: "statOrDecl \<Rightarrow> statOrDecl set" where
  "reachable c = {c'. \<exists>s s' n n'. (c, s, n) \<leadsto>* (c', s', n')}"

end