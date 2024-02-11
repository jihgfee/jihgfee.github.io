From actris.channel Require Import proofmode.
(** 

  ===================================================================
                                Actris:
        Mechanised "system-generic" verification framework for
  message passing in the Iris separation logic based on session types
  ===================================================================

  Actris is a multi-faceted system used to:
  1. Prove expressive session type style program logic specifications for
     reliable channel operations
  2. Use the specifications to prove "partial correctness" of programs with
     message passing: The program does not crash, but it might not terminate.
  3. Derive session type system using the technique of semantic typing
  4. Tooling for doing all of this in Coq

  This demonstration:
  - What is Actris
  - How to mechanise proofs of programs with Actris in Coq

  ====================
  Instantiating Actris
  ====================
  
  Actris is "system-generic" and applies to any* implementation of
  atomic reliable communication.
    * Proof pending

  1. Define operational semantics for language

  2. Instantiate Iris with language

  3. Implement bi-directional reliable communication channels (if not primitive)

  4. Prove Actris program logic specifications using Iris and Actris framework
     - send
     - receive
     - channel endpoint linking

  5a. Verify programs using the Iris and Actris specifications
  
  5b. Derive semantic session type system based on Actris rules using semantic typing


  Existing language instantiations of Actris:

  - HeapLang: OCaml-like language + shared memory concurrency [POPL'20, LMCS'22]
    + Channels implemented via bidirectional buffers and locks 
    + Semantic type system: equi-recursion, polymorphism, async subtyping [CPP'21]

  - AnerisLang: UDP-based distributed system with HeapLang nodes [ICFP'23b]
    + Channels implemented via UDP using retransmissions and
      duplication-protection

  
  Variants of the Actris framework:
  
  - MiniActris: Actris in shared-memory concurrency from first principles [ICFP'23a]
    + Channels defined using one-shot channels based on mutable references

  - LinearActris: Actris in shared-memory concurrency with deadlock freedom [POPL'24]
    + Channels are primitive in the language
    + Logic is linear
    + Semantic type system: equi-recursion, polymorphism, async subtyping

  ==============================
  Dependent Separation Protocols
  ==============================
  
  Session Types + Separation Logic = Dependent Separation Protocols:

  prot :=   ! (xs:τs) < v > { P } . prot
          | ? (xs:τs) < v > { P } . prot
          | end

  Note: We often write ! (xs:τs) < v > . prot ≜ (xs:τs) < v > { True } . prot

  Examples: 
  - ! <40> . ? <42> . end
  - ! (x:Z) <x> . ? (y:Z) <y> { y = x + 2 } . end
  - ! (l1 l2 : loc) (x : Z) < (l1,l2) > { l1 ↦ x } . ? < () > { l ↦ (x+2) } . end

  - ? (v : val) < v > . end


  Dependent separation protocols permits semantic session types
  via semantic typing [CPP'21]

  [[ ! A . S ]] ≜ ! (v:val) <v> { [[ A ]] v } . [[ S ]]
  [[ ? A . S ]] ≜ ? (v:val) <v> { [[ A ]] v } . [[ S ]]

  =====================
  Actris specifications
  =====================

  v ∈ Val  ::= () | i | b | l | rec f x := e | ..
  e ∈ Expr ::= v | x | ref e | ! e | e1 ← e2 | fork {e} | ...

  Implemented channel primitives:
  send e1 e2 | recv e1 | fork_chan e


  Channel endpoint ownership: c ↣ prot


  Weakest preconditions:

             binder for the return value
             /
     WP e { w, Q }
       /        \
     program    postcondition


  If WP e { w, Q } then
  - Safety: The program e never gets stuck (crashes)
  - Postcondition validity: If the program terminates with value v, then Q[v/w]

  
  Send rule:
  c ↣ (! (xs:τs) < v > { P } . prot) ∗ P[ts/xs]
  ---------------------------------------------
    WP send c (v[ts/xs]) { c ↣ prot[ts/xs] }

  Receive rule:
                  c ↣ (? (xs:τs) < v > { P } . prot)
  ---------------------------------------------------------------------
  WP recv c { w, ∃ (ys:τs), w = v[ys/xs] ∗ P[ys/xs] ∗ c ↣ prot[ys/xs] }

  Channel creation rule:
        ∀ c2, c2 ↣ (dual prot) -∗ WP e c2 { True }
  ------------------------------------------------------
  WP fork_chan (λ c2. e) { w, ∃ c1. w = c1 ∗ c1 ↣ prot }

  ====
  Misc
  ====

  To install: `opam install coq-actris`
  Homepage: https://iris-project.org/actris/

*)

(** Dependent value exchange *)

(** 
    Coq notation for HeapLang primitives
    λ       |     _      |       λ      |      ;      |      x
    λ:      |     <>     |       λ:     |      ;;     |      "x"
    
    #x:         Coercion of Coq value x into a value of HeapLang
*)
Definition prog : val := λ: <>,
  let: "c1" := fork_chan (λ: "c2", let: "x" := recv "c2" in
                                   send "c2" ("x"+#2)) in
  send "c1" #40;; recv "c1".

Section proof.
  (** Iris boiler-plate *)
  Context `{!heapGS Σ, !chanG Σ}.

  (** 
    Coq notation for dependent separation protocols:
    ! (xs:τs) < v > { P } . prot        |    end
    <!(xs:τs)> MSG v {{ P }} ; prot     |    END
    
    iProto Σ:   Type of dependent separation protocols in Coq
  *)
  Definition prot : iProto Σ :=
    <! (x : Z)> MSG #x; <?> MSG #(x + 2); END.

  Lemma prog_spec : ⊢ WP prog #() {{ v, ⌜v = #42⌝ }}.
  Proof.
    unfold prog.
    wp_fork_chan prot.
    - wp_recv (x) as "_". wp_send with "[//]". done.
    - wp_send with "[//]". wp_recv as "_". done.
  Qed.

End proof.

(** Linear resource and implicit exchange *)

Definition prog_ref : val := λ: <>,
  let: "c1" :=
    fork_chan (λ: "c2",
                 let: "l" := recv "c2" in
                 "l" <- (!"l"+#2);;
                 send "c2" #()) in
  let: "l" := ref #40 in send "c1" "l";; recv "c1";; !"l".

Section proof.
  Context `{!heapGS Σ, !chanG Σ}.

  Definition prot_ref : iProto Σ :=
    <! (l : loc) (x : Z)> MSG #l {{ l ↦ #x }};
    <?> MSG #() {{ l ↦ #(x + 2) }};
    END.

  Lemma prog_ref_spec : ⊢ WP prog_ref #() {{ v, ⌜v = #42⌝ }}.
  Proof.
    unfold prog_ref.
    wp_fork_chan prot_ref.
    - wp_recv (l x) as "Hl". wp_load. wp_store.
      wp_send with "[$Hl]". done.
    - wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl". wp_load. done.
  Qed.

End proof.

(** Recursion *)

Definition prog_ref_rec : val := λ: <>,
  let: "c1" :=
    fork_chan (λ: "c2",
                 (rec: "f" "c2" :=
                    let: "l" := recv "c2" in
                    "l" <- (!"l"+#2);;
                    send "c2" #();;
                    "f" "c2") "c2") in
  let: "l1" := ref #18 in let: "l2" := ref #20 in
  send "c1" "l1";; recv "c1";;
  send "c1" "l2";; recv "c1";;
  (!"l1" + !"l2").

Section proof.
  Context `{!heapGS Σ, !chanG Σ}.

  Definition prot_ref_rec_aux (rec : iProto Σ) : iProto Σ :=
    <! (l : loc) (x : Z)> MSG #l {{ l ↦ #x }};
    <?> MSG #() {{ l ↦ #(x + 2) }};
    rec.
  Instance prot_ref_rec_contractive : Contractive prot_ref_rec_aux.
  Proof. solve_proto_contractive. Qed.
  Definition prot_ref_rec : iProto Σ := fixpoint prot_ref_rec_aux.
  Global Instance prot_ref_rec_unfold :
    ProtoUnfold prot_ref_rec (prot_ref_rec_aux prot_ref_rec).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

  Lemma prog_ref_rec_spec : ⊢ WP prog_ref_rec #() {{ v, ⌜v = #42⌝ }}.
  Proof.
    unfold prog_ref_rec.
    wp_fork_chan prot_ref_rec.
    - do 2 wp_pure _. iLöb as "IH".
      wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]".
      do 2 wp_pure _. iApply "IH". done.
    - wp_alloc l1 as "Hl1". wp_alloc l2 as "Hl2".
      wp_send with "[$Hl1]". wp_recv as "Hl1".
      wp_send with "[$Hl2]". wp_recv as "Hl2".
      wp_load. wp_load. wp_pures. done.
  Qed.

End proof.

(** Asynchronous subtyping *)
(** ?A . !B . S  <:  !B . ? A . S *)

Definition prog_ref_rec_swap : val := λ: <>,
  let: "c1" :=
    fork_chan (λ: "c2",
                 (rec: "go" "c2" :=
                    let: "l" := recv "c2" in
                    "l" <- (!"l"+#2);;
                    send "c2" #();;
                    "go" "c2") "c2") in
  let: "l1" := ref #18 in let: "l2" := ref #20 in
  send "c1" "l1";; send "c1" "l2";; (** <- Immediately send twice! *)
  recv "c1";; recv "c1";; (!"l1" + !"l2").

Section proof.
  Context `{!heapGS Σ, !chanG Σ}.
  
  Lemma prog_ref_rec_swap_spec :
    ⊢ WP prog_ref_rec_swap #() {{ v, ⌜v = #42⌝ }}.
  Proof.
    unfold prog_ref_rec_swap.
    wp_fork_chan prot_ref_rec.
    - do 2 wp_pure _. iLöb as "IH".
      wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]".
      do 2 wp_pure _. by iApply "IH".
    - wp_alloc l1 as "Hl1". wp_alloc l2 as "Hl2".
      wp_send with "[$Hl1]". wp_send with "[$Hl2]".
      wp_recv as "Hl1". wp_recv as "Hl2".
      wp_load. wp_load. wp_pures. done.
  Qed.

End proof.

(** 
  ======================
  Semantic Session Types
  ======================

  Actris permits semantic session type systems via semantic typing [CPP'21]

  [[ chan S ]]  ≜ λ v. v ↣ S
  [[ ! A . S ]] ≜ ! (v:val) <v> { [[ A ]] v } . [[ S ]]
  [[ ? A . S ]] ≜ ? (v:val) <v> { [[ A ]] v } . [[ S ]]

  [[ |- e : A ]] ≜ WP e { w, [[ A ]] w }

  Typing rules for channel operations follow almost directly from Actris rules

  ================
  Deadlock Freedom
  ================

  Actris + connectivity graphs = program logic for deadlock freedom [POPL'24]
  
  Change 1: Make the logic linear instead of affine
  Change 2: Enforce structural concurrency: e.g. using fork_chan
  Change 3: Remove Iris invariants 

  ====
  Misc
  ====

  To install: `opam install coq-actris`
  Homepage: https://iris-project.org/actris/

*)
