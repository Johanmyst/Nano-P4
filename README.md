# Nano P4
Nano P4 is a formalisation effort of P4_16 using the Isabelle/HOL proof assistant. This project is developed as part of a master's thesis project for the Computer Science master (Computer Systems Security track) of the University of Amsterdam and the Vrije University Amsterdam.

# Thesis Abstract:
> P4 is a novel programming language that makes the dataplane programmable at line-rate speeds; bringing unparalleled customisability. This flexibility also leaves considerable room for error. Bugs and mistakes can fundamentally change the meaning of a program and lead to potentially exploitable vulnerabilities.
>
> We present Nano P4: A novel approach for the formalisation and verification of P4 and P4 applications leveraging the Isabelle/HOL proof assistant. We provide a small-step semantics of P4 actions, including numerous correctness proofs and a strict typing system. We show that our semantics can be used to formally reason about properties of P4 and P4 applications, including termination or the prevention of usage of uninitialised variables. Moreover, we show that our semantics can be used to reason about the correctness of program transformations, such as verified optimisation routines. Additionally we provide a formalisation of P4's parser state machines and show that Nano P4 can be used to reason about reachability properties and parser optimisations.
>
> With Nano P4 we show that it is possible to use the Isabelle/HOL proof assistant to formalise and verify P4 and P4 applications and show that Nano P4 is a versatile and powerful tool to reason about P4 and P4 applications.
