Load swap.
Require Import floyd.proofauto. 
Require Import floyd.extract_smt.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.


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

Definition main_spec := 
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.


Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=
  swap_spec :: main_spec :: nil.

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
  extract_smt. (*SMT solve*) admit.
  extract_smt. (*SMT solve*) admit.
  extract_smt. (*SMT solve*) admit.
Qed.