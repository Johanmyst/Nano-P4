theory NP4_Parser_Values
  imports
    Complex_Main
    NP4_Parser_Syntax
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
(*                                          CONCRETE VALUE MAPPING                                                *)
(* ============================================================================================================== *)

datatype val = BOOL bool
  | UINT nat
  | SINT int

type_synonym varState = "vname \<Rightarrow> val"

fun eval :: "expression \<Rightarrow> varState \<Rightarrow> val" where
    RBOOL: "eval (BASE (BBOOL b)) s = (BOOL b)"
  | RUINT: "eval (BASE (BUINT n)) s = (UINT n)"
  | RSINT: "eval (BASE (BSINT n)) s = (SINT n)"
  | RVALU: "eval (VAR vName) s = s vName"

lemma eval_deterministic: "(eval e s) = v \<Longrightarrow> (eval e s) = v' \<Longrightarrow> v' = v"
  by simp

(* ============================================================================================================== *)
(*                                              SYNTACTIC SUGAR                                                   *)
(* ============================================================================================================== *)

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. (UINT 0)"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

(* ============================================================================================================== *)
(*                                       REFLEXIVE TRANSITIVE CLOSURE                                             *)
(* ============================================================================================================== *)

inductive
    star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

hide_fact (open) refl step

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof (induction rule: star.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis star.step)
qed

lemmas star_induct = star.induct[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

declare star.refl[simp,intro]

lemma star_step1[simp, intro]: "r x y \<Longrightarrow> star r x y"
  by (metis star.refl star.step)

code_pred star .

end
  