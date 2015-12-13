
Load readwrite.
Require Import floyd.proofauto. 
Require Import floyd.extract_smt.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.


Local Open Scope logic.


Definition test1_spec :=
 DECLARE _first_test
  WITH a: val, sh: share, contents: list int, i : Z, size: Z
  PRE  [ _a OF (tptr tint), _i OF tint  ]
  PROP(writable_share sh; 0 <= i <= size; i < size; 0 <= size <= Int.max_signed)
  LOCAL(temp _a a; temp _i (Vint (Int.repr i)))
  SEP (data_at sh (tarray tint size) (map Vint contents) a)
  POST [ tint]
   EX contents': list int,
   PROP()
   LOCAL(temp ret_temp (Vint Int.one) )
   SEP (data_at sh (tarray tint size) (map Vint contents') a).
 

Definition test2_spec :=
  DECLARE _second_test
            WITH i : Z 
                       PRE  [_i OF tint  ]
                       PROP(0 <= i < 10) LOCAL(temp _i (Vint (Int.repr i))) SEP ()
   POST [ tint]
       PROP() LOCAL(temp ret_temp (Vint Int.one) ) SEP ()
. 


Definition main_spec := 
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.


Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=
  test1_spec :: test2_spec :: main_spec :: nil.

Lemma body_test1: semax_body Vprog Gprog f_first_test test1_spec.
Proof.
  start_function.
  forward. (* a[i] = 1;*)  
  forward. (* temp = a[i]; *)
  simpl; intros.
  entailer. (*Remove the local variables*)
  rewrite upd_Znth_map; rewrite Znth_map with (d':=Int.zero); simpl.
  cancel.
  extract_smt. (*Solved in SMT*) admit.
  
  forward. (*Return temp*)
  Exists (upd_Znth i contents (Int.one)).
  rewrite upd_Znth_map. entailer.
  rewrite <- H2.
  extract_smt. (*Solve in SMT*) admit.
Qed.  

Lemma body_test2: semax_body Vprog Gprog f_second_test test2_spec.
Proof.
  start_function.
  forward.
  
  Definition init_Inv n sh contents size := 
    EX i: Z,
          PROP  (0 <= i <= size)
                LOCAL (temp _a a)
                SEP   (data_at sh (tarray tint size) (map Vint contents) a).
  forward_while (reverse_Inv sh contents).
  