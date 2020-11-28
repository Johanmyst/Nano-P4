theory NP4_Parser_Syntax
  imports Complex_Main
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

type_synonym name = string
type_synonym vname = string

datatype baseType = BBOOL bool
  | BUINT nat
  | BSINT int

datatype expression = BASE baseType
  | VAR vname

datatype statement = EmptyStat
  | VarDecl vname expression

(* The parser states contain their name, statements, and which states are reachable
   from the parser state. *)
datatype parserState = State name "statement list" "parserState list"

(* The parser itself contains its name, statements, and list of all states in the parser. *)
datatype parser = Parser name "statement list" "parserState list"

end