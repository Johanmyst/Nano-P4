theory NP4_Parser_Semantics
  imports
    Complex_Main
    NP4_Parser_Values
(*  These files are an effort to verify the state machines found in P4's parsers. The P4
    parsers are based on state-machines that incrementally convert a byte-stream into
    usable programmeable P4 objects and structs. At every step a packet is processed
    further and ultimately the packet is parsed into P4 objects.

    The packets and incoming datastream are outside of the scope of this verification
    effort as they only exist at runtime. This verification effort is aimed at compile-
    -time verification, and as such disregards the actual packets.

    Instead this effort aims to analyse the parser itself, and observe things like what
    states are reachable, what the minimal parser is, and which program states (i.e.
    variables and their values) the parser can reach. Note that for this end a
    minimalistic big-step semantics is defined, and proven to be equivalent to a small
    step semantics for additional proof strength. *)
begin

(* ============================================================================================================== *)
(*                                          BIG STEP SEMANTIC RULES                                               *)
(* ============================================================================================================== *)

fun big_step :: "(statement * varState) \<Rightarrow> varState" where
    BEmpty: "big_step (EmptyStat, s) = s"
  | BDecl:  "big_step ((VarDecl vName expr), s) = s (vName := (eval expr s))"

lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive small_step :: "(statement * varState) \<Rightarrow> (statement * varState) \<Rightarrow> bool" (infix "\<leadsto>" 55) where
    SDcl:   "((VarDecl vName expr), s) \<leadsto> (EmptyStat, s (vName := (eval expr s)))"

code_pred small_step .

declare small_step.intros [intro, simp]

lemmas small_step_induct = small_step.induct[split_format(complete)]

inductive_cases SEmpt[elim!]: "(EmptyStat, s) \<leadsto> ct"
inductive_cases SDcl[elim!]:  "(VarDecl n e, s) \<leadsto> ct"

(* ============================================================================================================== *)
(*                                             SEMANTIC PROOFS                                                    *)
(* ============================================================================================================== *)

lemma big_step_deterministic: "big_step (stmt, s) = s' \<Longrightarrow> big_step (stmt, s) = s'' \<Longrightarrow> s'' = s'"
  by simp

lemma small_step_deterministic: "small_step (stmt, s) = cs' \<Longrightarrow> small_step (stmt, s) = cs'' \<Longrightarrow> cs'' = cs'"
  by simp

(* ============================================================================================================== *)
(*                                  BIG AND SMALL STEP SEMANTIC EQUIVALENCE                                       *)
(* ============================================================================================================== *)

abbreviation equiv_stmt :: "statement \<Rightarrow> statement \<Rightarrow> bool" (infix "~" 50) where
  "c ~ c' \<equiv> (\<forall>s t. (big_step (c, s) = t) = (big_step (c', s) = t))"
lemma sim_refl:  "c ~ c" by simp
lemma sim_sym:   "(c ~ c') = (c' ~ c)" by auto
lemma sim_trans: "c ~ c' \<Longrightarrow> c' ~ c'' \<Longrightarrow> c ~ c''" by auto

abbreviation small_steps :: "(statement * varState) \<Rightarrow> (statement * varState) \<Rightarrow> bool" (infix "\<leadsto>*" 55) where
  "x \<leadsto>* y \<equiv> star small_step x y"

lemma big_to_small: "(big_step cs = t) \<Longrightarrow> cs \<leadsto>* (EmptyStat, t)"
  by (metis big_step.elims small_step.intros star.simps)

lemma small1_to_big: "cs \<leadsto> cs' \<Longrightarrow> (big_step cs' = t) \<Longrightarrow> (big_step cs = t)"
  using small_step.simps by auto

lemma small_to_big: "cs \<leadsto>* (EmptyStat, t) \<Longrightarrow> (big_step cs = t)"
  by (metis (full_types) NP4_Parser_Semantics.BDecl NP4_Parser_Semantics.BEmpty SEmpt small_step.simps star.cases)

theorem big_iff_small: "(big_step cs = t) = cs \<leadsto>* (EmptyStat, t)"
  using big_to_small small_to_big by blast

(* ============================================================================================================== *)
(*                                         VARIABLE STATE (PROGRAM STATE)                                         *)
(* ============================================================================================================== *)

(* Calculates what state a state ends up in after a list of statements *)
fun get_varState :: "varState \<Rightarrow> statement list \<Rightarrow> varState" where
    "get_varState s [] = s"
  | "get_varState s (x # xs) = get_varState (big_step (x, s)) xs"

(* ============================================================================================================== *)
(*                                               HELPER FUNCTIONS                                                 *)
(* ============================================================================================================== *)

fun get_only_pState :: "(parserState * varState) \<Rightarrow> parserState" where "get_only_pState (pS, vS) = pS"
fun get_only_vState :: "(parserState * varState) \<Rightarrow> varState" where "get_only_vState (pS, vS) = vS"

(* Get all states from a parser data type *)
fun get_parser_states :: "parser \<Rightarrow> parserState set" where
    "get_parser_states (Parser pName stmts sList) = set sList"

lemma sub_self: "(get_parser_states p) \<subseteq> (get_parser_states p)" by simp
lemma sub_self_any: "(get_parser_states p) \<subseteq> ((get_parser_states p) \<union> anyState)" by simp
lemma sub_self_reject: "(get_parser_states p) \<subseteq> ((get_parser_states p) \<union> {State ''reject'' [] []})" by auto

(* ============================================================================================================== *)
(*                                       PARSER STATE (STATE MACHINE STATE)                                       *)
(* ============================================================================================================== *)

(* Find a state with a particular name in a list of states (finds the first one) *)
fun get_state :: "parserState list \<Rightarrow> name \<Rightarrow> parserState option" where
    "get_state [] _ = None"
  | "get_state ((State sName1 stmts ts) # xs) sName2 = (if sName1 = sName2 then Some (State sName1 stmts ts) else get_state xs sName2)"

lemma always_in_sList: "get_state sList pName = Some pState \<longrightarrow> pState \<in> (set sList)"
  apply (induction sList)
   apply (simp)
  apply (metis get_state.simps(2) insert_iff list.simps(15) option.inject parserState.exhaust)
  done

(* Returns a boolean whether a particular state is in a state set *)
fun state_in_list :: "parserState \<Rightarrow> parserState set \<Rightarrow> bool" where
    "state_in_list findState allStates = (findState \<in> allStates)"

lemma state_in_list_always: "\<forall>x \<in> allS. state_in_list x allS = True"
  by simp

(* ============================================================================================================== *)
(*                                         STATE FILTERING (PARSER STATES)                                        *)
(* ============================================================================================================== *)

fun filter_states :: "parserState set \<Rightarrow> parserState list \<Rightarrow> parserState list" where
    "filter_states allS [] = []"
  | "filter_states allS (x # xs) = (if (x \<in> allS) then (x # (filter_states allS xs)) else (filter_states allS xs))"

lemma set_state_filter[simp]: "set (filter_states allS pList) = {x. x \<in> (set pList) \<and> x \<in> allS}"
  by (induction pList) auto

lemma in_all: "x \<in> allS \<Longrightarrow> x \<in> set (filter_states allS [x])" by simp
lemma not_all: "x \<notin> allS \<Longrightarrow> x \<notin> set (filter_states allS [x])" by simp

lemma in_both: "x \<in> allS \<Longrightarrow> x \<in> set pList \<Longrightarrow> x \<in> set (filter_states allS pList)"
  by (induct pList) auto
lemma not_in_pList: "x \<in> allS \<Longrightarrow> x \<notin> set pList \<Longrightarrow> x \<notin> set (filter_states allS pList)"
  by (induct pList) auto

lemma in_filter_in_all: "x \<in> set (filter_states allS pList) \<Longrightarrow> x \<in> allS"
  by auto
lemma in_filter_in_pList: "x \<in> set (filter_states allS pList) \<Longrightarrow> x \<in> set pList"
  by auto

lemma filter_sub1: "set (filter_states allS pList) \<subseteq> allS"
  by auto
lemma filter_sub2: "set (filter_states allS pList) \<subseteq> set pList"
  by auto

lemma empty_allS: "filter_states {} pList = []"
  by (induct pList) auto
lemma empty_pList: "filter_states allS [] = []"
  by auto

lemma not_in_all: "x \<in> set pList \<Longrightarrow> x \<notin> allS \<Longrightarrow> x \<notin> set (filter_states allS pList)"
  using in_filter_in_all by blast

lemma filter_determ: "filter_states allS pList = v \<Longrightarrow> filter_states allS pList = v' \<Longrightarrow> v' = v"
  by auto

lemma same_equal: "set (filter_states (set pList) pList) = set pList"
  by simp

lemma filter_twice1:
  assumes "filter_states allS pList = v" and "filter_states allS v = v'"
  shows "set v' = set v"
  using assms
proof -
  have "\<forall>x \<in> set v. x \<in> allS"
    using assms in_filter_in_all by blast
  moreover have "\<forall>x \<in> set v'. x \<in> allS"
    using assms(2) in_filter_in_all by blast
  moreover have "\<forall>x \<in> set v'. x \<in> set v"
    using assms(2) by fastforce
  moreover have "set v' = set v"
    using assms(1) assms(2) by force
  ultimately show ?thesis
    by auto
qed

lemma filter_twice2:
  assumes "filter_states allS pList = v" and "filter_states (set v) pList = v'"
  shows "set v' = set v"
  using assms
proof -
  have "\<forall>x \<in> set v. x \<in> allS"
    using assms in_filter_in_all by blast
  moreover have "\<forall>x \<in> set v'. x \<in> allS"
    using assms(2) calculation filter_sub1 by blast
  moreover have "\<forall>x \<in> set v'. x \<in> set v"
    using assms(2) by fastforce
  moreover have "set v' = set v"
    using assms(1) assms(2) by force
  ultimately show ?thesis
    by auto
qed

lemma filter_twice3: "set (filter_states allS pList) = set (filter_states (set (filter_states allS pList)) (filter_states allS pList))"
  by (metis filter_twice1 filter_twice2)

(* ============================================================================================================== *)
(*                                           ITERATING OVER PARSER STATES                                         *)
(* ============================================================================================================== *)

(* Iterate over all states reachable from a given cState and returns them as a list. *)
fun iterate_states :: "parserState \<Rightarrow> parserState list \<Rightarrow> parserState list" where
    "iterate_states cState [] = [cState]"
  | "iterate_states cState ((State sName stmts tList) # xs) = ((iterate_states (State sName stmts tList) tList) @ (iterate_states cState xs))"

(* Iterate over all reachable states but also filter them to only be those in the list of all states. *)
fun iterate_all :: "parserState set \<Rightarrow> parserState \<Rightarrow> parserState list \<Rightarrow> parserState list" where
    "iterate_all allS cState tList = filter_states allS (iterate_states cState tList)"

lemma iterate_determ: "iterate_all allS pS tList = v \<Longrightarrow> iterate_all allS pS tList = v' \<Longrightarrow> v' = v"
  by simp

lemma always_in_allS: "x \<in> set (iterate_all allStates currState transList) \<Longrightarrow> x \<in> allStates"
  by simp

(* ============================================================================================================== *)
(*                                           GETTING ALL REACHABLE STATES                                         *)
(* ============================================================================================================== *)

(* Get all reachable states from a particular state. The starting state can also be None, in which case an empty list is given *)
fun get_start_reachables :: "parserState set \<Rightarrow> parserState option \<Rightarrow> parserState list" where
    "get_start_reachables allS None = []"
  | "get_start_reachables allS (Some (State sName stmts tList)) = iterate_all allS (State sName stmts tList) tList"

lemma always_in_reachables: "set (get_start_reachables allS pS) \<subseteq> allS"
  by (metis always_in_allS empty_iff empty_set get_start_reachables.elims subsetI)

(* Get the list of all reachable states and append the reject state to it since it is always reachable. *)
fun reachable_list :: "parserState set \<Rightarrow> parserState option \<Rightarrow> parserState list" where
    "reachable_list allS pS = (State ''reject'' [] []) # (get_start_reachables allS pS)"

lemma reachable_pair_lnone: "reachable_list a None = [State ''reject'' [] []]"
  by simp

lemma always_in_pair_list: "set (reachable_list allS pS) \<subseteq> (allS \<union> {State ''reject'' [] []})"
  using always_in_reachables by auto
lemma with_reject1: "(\<forall>pS. allS = reachable_list a pS \<longrightarrow> (State ''reject'' [] []) \<in> (set allS))"
  by (metis list.set_intros(1) reachable_list.elims)

lemma reachable_list_sub: "set (reachable_list allS cState) \<subseteq> (allS \<union> {State ''reject'' [] []})"
  by (meson always_in_pair_list)

(* Get the list of allre achable states and append the reject state. Return the resulting set. *)
fun reachable_set :: "parserState set \<Rightarrow> parserState option \<Rightarrow> parserState set" where
    "reachable_set allS pS = set (reachable_list allS pS)"

lemma always_in_pair_set: "reachable_set allS pS \<subseteq> (allS \<union> {State ''reject'' [] []})"
  using always_in_pair_list by auto
lemma with_reject2: "(\<forall>pS. allS = reachable_set a pS \<longrightarrow> (State ''reject'' [] []) \<in> allS)"
  by (metis reachable_set.elims with_reject1)

lemma reachable_pair_snone: "reachable_set a None = {State ''reject'' [] []}" by simp

lemma reachable_set_sub: "reachable_set allS cState \<subseteq> (allS \<union> {State ''reject'' [] []})"
  by (meson always_in_pair_set)

(* ============================================================================================================== *)
(*                                      GETTING ALL REACHABLE STATES FROM PARSER                                  *)
(* ============================================================================================================== *)

(* Get all reachable states from a parser and return them as a set *)
fun parser_reachable :: "parser \<Rightarrow> parserState set" where
  "parser_reachable (Parser pName stmts sList) = set (reachable_list (set sList) (get_state sList ''start''))"

lemma reachable_sub: "parser_reachable p \<subseteq> (get_parser_states p \<union> {State ''reject'' [] []})"
  by (metis always_in_pair_set get_parser_states.simps parser_reachable.elims reachable_set.elims)

lemma always_reachable: "(State ''reject'' [] []) \<in> set (reachable_list (set sList) (get_state sList sName))"
  by simp

lemma reject_always_reachable: "(\<forall>p. (State ''reject'' [] []) \<in> parser_reachable p)"
  by (metis always_reachable parser_reachable.elims)

(* ============================================================================================================== *)
(*                                     GETTING ALL UNREACHABLE STATES FROM PARSER                                 *)
(* ============================================================================================================== *)

(* Get all unreachable states from a parser and return them as a set *)
fun parser_unreachable :: "parser \<Rightarrow> parserState set" where
    "parser_unreachable (Parser pName stmts []) = {}"
  | "parser_unreachable (Parser pName stmts sList) = (set sList) - (parser_reachable (Parser pName stmts sList))"

lemma unreachable_sub: "parser_unreachable p \<subseteq> get_parser_states p"
  by (smt Diff_iff empty_iff get_parser_states.simps parser_unreachable.elims subsetI)

lemma reject_never_unreachable: "(\<forall>p. (State ''reject'' [] []) \<notin> parser_unreachable p)"
  using parser_unreachable.elims by auto

(* ============================================================================================================== *)
(*                                               REACHABILITY PROOFS                                              *)
(* ============================================================================================================== *)

lemma reachable_or_unreachable: "x \<in> get_parser_states p \<longrightarrow> (x \<in> parser_reachable p \<or> x \<in> parser_unreachable p)"
  by (smt Diff_iff empty_set get_parser_states.simps parser_unreachable.elims)

lemma reachable_unreachable: "(parser_reachable p \<union> parser_unreachable p) = (get_parser_states p \<union> {State ''reject'' [] []})"
  by (smt Un_Diff_cancel2 Un_insert_left empty_set get_parser_states.simps insert_absorb list.simps(15) parser_reachable.elims parser_unreachable.elims reachable_sub reject_always_reachable sup.absorb_iff1 sup_bot.left_neutral sup_commute)

lemma reachable_not1: "pS \<in> (parser_reachable p) \<longrightarrow> pS \<notin> (parser_unreachable p)"
  by (metis Diff_iff empty_iff parser_unreachable.elims)
lemma unreachable_not1: "pS \<in> (parser_unreachable p) \<longrightarrow> pS \<notin> (parser_reachable p)"
  using reachable_not1 by blast

lemma reachable_not2: "pS \<in> (get_parser_states p) \<and> pS \<notin> (parser_reachable p) \<longrightarrow> pS \<in> (parser_unreachable p)"
  using reachable_or_unreachable by blast
lemma unreachable_not2: "pS \<in> (get_parser_states p) \<and> pS \<notin> (parser_unreachable p) \<longrightarrow> pS \<in> (parser_reachable p)"
  using reachable_not2 by blast

lemma reachable_not_unreachable: "pS \<in> (get_parser_states p) \<longrightarrow> (pS \<in> (parser_reachable p) \<longleftrightarrow> pS \<notin> (parser_unreachable p))"
  using reachable_not1 reachable_not2 by blast
lemma unreachable_not_reachable: "pS \<in> (get_parser_states p) \<longrightarrow> (pS \<notin> (parser_reachable p) \<longleftrightarrow> pS \<in> (parser_unreachable p))"
  using reachable_not2 reachable_not1 by blast

(* ============================================================================================================== *)
(*                                               FILTERING THE PARSER                                             *)
(* ============================================================================================================== *)

fun filter_parser :: "parser \<Rightarrow> parser" where
    "filter_parser (Parser pName stmts []) = (Parser pName stmts [])"
  | "filter_parser (Parser pName stmts sList) = (Parser pName stmts (remdups (reachable_list (set sList) (get_state sList ''start''))))"

definition reachable :: "parser \<Rightarrow> parserState \<Rightarrow> bool" where
    "reachable prsr pState \<equiv> (pState : (parser_reachable prsr))"

lemma all_reachable: "\<forall>ps \<in> (parser_reachable p). reachable p ps"
  using reachable_def by auto

(* ============================================================================================================== *)
(*                                        GETTING CORRESPONDING PROGRAM STATES                                    *)
(* ============================================================================================================== *)

fun iterate_pairs :: "parserState set \<Rightarrow> varState \<Rightarrow> parserState \<Rightarrow> parserState list \<Rightarrow> (parserState * varState) set" where
    "iterate_pairs allS vState cState [] = (if cState \<in> allS then {(cState, vState)} else {})"
  | "iterate_pairs allS vState cState ((State sName stmts tList) # xs) = (iterate_pairs allS (get_varState vState stmts) (State sName stmts tList) tList) \<union> (iterate_pairs allS vState cState xs)"

fun get_pair_reachables :: "parserState set \<Rightarrow> (parserState option * varState) \<Rightarrow> (parserState * varState) set" where
    "get_pair_reachables allS (None, s) = {}"
  | "get_pair_reachables allS (Some (State sName stmts tList), vState) = iterate_pairs allS (get_varState vState stmts) (State sName stmts tList) tList"

fun get_pair_set :: "parserState set \<Rightarrow> (parserState option * varState) \<Rightarrow> (parserState * varState) set" where
    "get_pair_set allS (pS, vState) = {(State ''reject'' [] [], <>)} \<union> (get_pair_reachables allS (pS, vState))"

fun get_all_var_states :: "parser \<Rightarrow> varState \<Rightarrow> (parserState * varState) set" where
    "get_all_var_states (Parser pName stmts allS) vState = get_pair_set (set allS) ((get_state allS ''start''), (get_varState vState stmts))"

fun get_var_states :: "parser \<Rightarrow> varState \<Rightarrow> (parserState * varState) set" where
    "get_var_states p vState = get_all_var_states (filter_parser p) vState"

end