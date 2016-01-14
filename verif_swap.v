(*
To process this file you need to install Compcert and VST:
http://vst.cs.princeton.edu/
 *)

(*The original code of swap is in swap.c *)
(*The translated code of swap is found in swap.v*)
Load swap.
Require Import floyd.proofauto. 
Require Import floyd.extract_smt.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

(*Hoare style specification of the function swap*)
(* WITH close specifies the quantified variables*)
(* PRE specidies the precondition which includes PROP LOCAL and SEP*)
(* POST specidies the postcondition which includes PROP LOCAL and SEP*)
Definition swap_spec :=
 DECLARE _swap
  WITH a: val, sh: share, contents: list int, i : Z, j : Z, size: Z
  PRE  [ _a OF (tptr tint), _i OF tint, _j OF tint  ]
  PROP(writable_share sh; 0 <= i < size;  0 <= j < size; 0 <= size <= Int.max_signed)
  LOCAL(temp _a a; temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)))
  SEP (data_at sh (tarray tint size) (map Vint contents) a)
  POST [ tvoid]
   EX contents': list int,
   PROP(Znth i contents' Int.zero = Znth j contents Int.zero;
        Znth j contents' Int.zero = Znth i contents Int.zero)
   LOCAL()
   SEP (data_at sh (tarray tint size) (map Vint contents') a).

(* The specification of main is irrelevant*)
Definition main_spec := 
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

(* Define the global variables and all the functions specifications of the program*)
Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=
  swap_spec :: main_spec :: nil.

(* Behold the verification of the swap function *)
(* The comments correspond to steps in the swap function 
   or subgoals extracted to the SMT solver *)
(* All the admits correspond to steps we manually extract
   into CVC4 to verify automatically *)
(* If CVC4 produced proof winesses, we could reflect them back
   and use them to complete the this machine-checked proof. *)
Lemma body_swap : semax_body Vprog Gprog f_swap swap_spec.
Proof.
  start_function.
  forward. (* t1 = a[i];*)
  entailer.
  rewrite Znth_map with (d':=Int.zero); auto. cancel.
  extract_smt. (*SMT solve *) admit.
  forward.  (*t2 = a[j];*)
  entailer.
  rewrite Znth_map with (d':=Int.zero); auto. cancel.
  extract_smt. (*SMT solve *) admit.
  forward. (* a[i] = t2*)
  forward. (* a[j] = t1*)
  (*Postcondition*)
  unfold POSTCONDITION, abbreviate.
  forward.
  Exists (upd_Znth j
            (upd_Znth i contents
               (Znth j contents Int.zero))
            (Znth i contents Int.zero)).
  entailer; simpl.
  rewrite Znth_map with (d':=Int.zero).
  rewrite Znth_map with (d':=Int.zero); simpl.
  rewrite upd_Znth_map. 
  rewrite upd_Znth_map. 
  entailer.
  (* The three subgoals described in the report
     come out of the following extraction: *)
  extract_smt. (*SMT solve*) admit.
  extract_smt. (*SMT solve*) admit.
  extract_smt. (*SMT solve*) admit.
Qed.