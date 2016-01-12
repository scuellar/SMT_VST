Add LoadPath "../CompCert-2.5" as compcert.
Add LoadPath "../VST".
Require Import compcert.lib.Coqlib.
Require Import msl.Coqlib2.
Require Import List.
Import ListNotations.

Require Import floyd.sublist.
Require Import Streams.

Section PROOF.


  Set Implicit Arguments.
  Variable array: forall {A:Type}, Type.
  Variable select: forall {A}, array A -> nat -> A.
  Variable store : forall {A}, array A -> nat -> A -> array A.
  
Axiom QFAX1 : forall A a i (e:A), select (store a i e) i = e.  
Axiom QFAX2 : forall A a i j (e:A), i <> j -> select (store a i e) j = select a j.  
Axiom QFAX3 : forall A (a b: array A), (forall i, select a i = select b i) -> a = b.  

(*This definition is "Backwards" so it generates ugly proofs. Maybe change?*)
Fixpoint list_of_array' {A} i L (ar:array A) :=
  match i with
    |  0%nat => nil
    | (S n)%nat => (select ar (L - i))::(list_of_array' n L ar)
  end.

Definition list_of_array1 {A} i (ar:array A) :=
  list_of_array' i i ar.

Fixpoint list_of_array'' {A} L (ar:array A) :=
  match L with
    |  0%nat => nil
    | (S n)%nat => (select ar n)::(list_of_array'' n ar)
  end.

Definition list_of_array {A} L (ar:array A) :=
  rev (list_of_array'' L ar).

Lemma length_la'': forall A (ar:array A) L, length (list_of_array'' L ar) = L.
      Proof. induction L.
             - reflexivity.
             - simpl; f_equal; assumption.
      Qed.

Lemma length_la: forall A L (ar:array A), length (list_of_array L ar) = L.
      Proof. intros. unfold list_of_array. rewrite rev_length.
             induction L.
             - reflexivity.
             - simpl; f_equal; assumption.
      Qed.

Theorem enc_nth: forall A  (L j:nat) (ar:array A) (ls:list A) (s:A)  (d:A),
                   ((0 <= j < L)%nat -> s = select ar j) /\
                    (( j < 0 \/ L <= j)%nat -> s = d) ->
                   (s = nth j (list_of_array L ar) d).
Proof.
  intros.
  destruct H as [H0 H1].
  unfold list_of_array. 
  destruct (le_gt_dec 0 j) as [LE | GT].
  destruct (le_gt_dec L j) as [LE' | GT'].
  - rewrite H1; [| right; assumption]. rewrite nth_overflow; auto.
    replace (rev (list_of_array'' L ar)) with (list_of_array L ar) by reflexivity.
    rewrite length_la; auto.
  - rewrite H0; auto.
    rewrite rev_nth; rewrite length_la'';  simpl; auto.
    clear - GT'.
    induction L.
    + contradict GT'; omega.
    + simpl. destruct (le_gt_dec L j).
      * assert (L = j) by omega.
        rewrite H in *; rewrite minus_diag; auto.
      * replace (L - j)%nat with (S (L - S j))%nat by omega.
        rewrite IHL; auto.
  - omega.
Qed.

Fixpoint upd_nth {A:Type} (i:nat) (l:list A) (a:A): list A :=
  match (i, l) with
    | (S n, a'::l') => a':: (upd_nth n l' a)
    | (0%nat, a'::l') => a::l'
    | _ => l
  end.


Lemma rev_upd_nth:
  forall (A : Type) (l : list A) (x: A) (n : nat),
    (n < length l)%nat -> upd_nth n (rev l) x = rev (upd_nth (length l - S n) l x).
Proof.
  intros. induction l.
  - contradict H; simpl; omega.
  - simpl.
    destruct (le_gt_dec (length l) n). simpl in H.
    assert (HH: n = length l) by omega; rewrite HH.
    rewrite minus_diag. simpl.
    Lemma upd_nth_app1: forall A l l' (x:A) n,
                          (length l <= n)%nat ->
                          upd_nth n (l ++ l') x = l ++ upd_nth (n - length l) l' x.
      intros until x. induction l; intros; auto. 
      simpl. simpl in H. rewrite <- minus_n_O; auto.
      simpl.
      destruct n. contradict H; simpl; omega.
          simpl. f_equal.
          apply IHl. simpl in H; omega.
        Qed.
        Lemma upd_nth_app2: forall A l l' (x:A) n,
                             ( n < length l)%nat ->
                             upd_nth n (l ++ l') x = (upd_nth n l x) ++ l'.
          intros until x. induction l; intros; auto. 
          simpl. simpl in H. contradict H; omega.
          simpl in *. destruct (le_gt_dec (length l) n).
          assert (HH: n = length l) by omega; rewrite HH; clear HH.
          clear. generalize a.
          induction l. reflexivity.
          simpl. intros. f_equal. auto.

          destruct n. reflexivity.
          simpl. f_equal. apply IHl. omega.
        Qed.
        
        rewrite upd_nth_app1.
        rewrite rev_length, minus_diag; simpl; auto.
        rewrite rev_length; auto.
        destruct (length l - n)%nat eqn:DIFF.
        (contradict DIFF; omega).
        rewrite upd_nth_app2; simpl. f_equal.
        replace n0 with (length l - S n)%nat by omega.
        apply IHl; omega.

        rewrite rev_length; auto.
    Qed.

Theorem enc_upd_ge:
  forall A i ss (a: array A) L ss',
    (L <= i)%nat ->
    ss' = store ss i a ->
    list_of_array L ss' = upd_nth i (list_of_array L ss) a.
Proof.
  intros. unfold list_of_array.
  induction L. destruct i; reflexivity.
      simpl. assert (L <= i)%nat by omega.
      specialize (IHL H1).
      rewrite H0 in *. rewrite QFAX2; try omega.
      rewrite upd_nth_app1.
      f_equal; auto.
      f_equal. admit.
      rewrite rev_length, length_la''.
      destruct (i-L)%nat eqn:eq. contradict H; omega.
      simpl. destruct n; reflexivity.
      rewrite rev_length, length_la''; assumption.
Qed.

Theorem enc_upd_lt:
  forall A i ss (a: array A) L ss',
    ( i < L)%nat ->
    ss' = store ss i a ->
    list_of_array L ss' = upd_nth i (list_of_array L ss) a.
Proof.
  intros. unfold list_of_array.
  rewrite rev_upd_nth; [|rewrite length_la''; auto].
  f_equal.
  rewrite length_la''.
  rewrite H0.
  induction L.
  reflexivity.
  destruct (le_gt_dec L i).
  simpl.
  assert (HH: L = i) by omega. rewrite HH.
  rewrite minus_diag. simpl. f_equal.
  apply QFAX1.
  Theorem blah:
    forall A i ss (a: array A) j,
      (j <= i)%nat ->
      list_of_array'' j (store ss i a) = list_of_array'' j ss.
  Proof.
    intros. induction j.
    reflexivity.
    simpl. f_equal. eapply QFAX2; omega.
    apply IHj. omega.
  Qed.
  apply blah; auto.
  {
    simpl.
    destruct (L-i)%nat eqn:Eq. contradict g; omega.
    simpl. f_equal.
    apply QFAX2; omega.
    rewrite IHL; auto.
    replace (L - S i)%nat with n by omega. reflexivity.
  }
  Qed.

Theorem enc_upd:
  forall A i ss (a: array A) L ss',
    ss' = store ss i a ->
    list_of_array L ss' = upd_nth i (list_of_array L ss) a.
Proof.
  intros. destruct (le_gt_dec L i); [apply enc_upd_ge | apply enc_upd_lt]; auto.
Qed.


Theorem enc_app: forall  A L1 L2 (ss1 ss2 ss3: array A),
                   (forall i, (0 <= i < L1)%nat -> select  ss1 i = select  ss3 i) ->
                   (forall i, (0 <= i < L2)%nat -> select ss2 i = select ss3 (i + L1)) ->
                   (list_of_array L1 ss1) ++ (list_of_array L2 ss2)  = list_of_array (L1+L2) ss3.
Proof.
  induction L2; intros.
  - unfold list_of_array; simpl. rewrite app_nil_r. assert (list_of_array'' L1 ss1 = list_of_array'' L1 ss3). revert H. clear H0. revert ss1. revert ss3. induction L1; intros.
    + auto.
    + simpl. unfold list_of_array in IHL1. rewrite IHL1 with (ss3 := ss3) . rewrite H. reflexivity. omega. intros. apply H. omega.
    + rewrite H1. rewrite plus_0_r. reflexivity.
  - unfold list_of_array. replace (L1 + S L2)%nat with (S L1 + L2)%nat by omega.  simpl.
    assert (select ss2 L2 =  select ss3 (L1+L2)). rewrite plus_comm. apply H0. omega.
    assert (list_of_array L1 ss1 ++ list_of_array L2 ss2 =
                                                                                                 list_of_array (L1 + L2) ss3). apply IHL2.
    + assumption.
    + intros. apply H0. omega.
    + unfold list_of_array in H2. rewrite <- H2.  rewrite H1. apply app_assoc.
Qed.




End PROOF.

 

   
(* from verif_revarray.v *)

Definition flip_between {A} lo hi (contents: list A) :=
  firstn (Z.to_nat lo) (rev contents) 
  ++ firstn (Z.to_nat (hi-lo)) (skipn (Z.to_nat lo) contents)
  ++ skipn (Z.to_nat hi) (rev contents).

Lemma flip_fact_0: forall {A} size (contents: list A),
  Zlength contents = size ->
  contents = flip_between 0 (size - 0) contents.
Proof.
  intros.
  assert (length contents = Z.to_nat size).
    apply Nat2Z.inj. rewrite <- Zlength_correct, Z2Nat.id; auto.
    subst; rewrite Zlength_correct; omega.
  unfold flip_between.
  rewrite !Z.sub_0_r. change (Z.to_nat 0) with O; simpl. rewrite <- H0.
  rewrite skipn_short.
  rewrite <- app_nil_end.
  rewrite firstn_exact_length. auto.
  rewrite rev_length. omega.
Qed.

Lemma flip_fact_1: forall A size (contents: list A) j,
  Zlength contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_between j (size - j) contents = rev contents.
Proof.
  intros.
  assert (length contents = Z.to_nat size).
    apply Nat2Z.inj. rewrite <- Zlength_correct, Z2Nat.id; auto.
    subst; rewrite Zlength_correct; omega.
  unfold flip_between.
  symmetry.
  rewrite <- (firstn_skipn (Z.to_nat j)) at 1.
  f_equal.
  replace (Z.to_nat (size-j)) with (Z.to_nat j + Z.to_nat (size-j-j))%nat
    by (rewrite <- Z2Nat.inj_add by omega; f_equal; omega).
  rewrite <- skipn_skipn.
  rewrite <- (firstn_skipn (Z.to_nat (size-j-j)) (skipn (Z.to_nat j) (rev contents))) at 1.
  f_equal.
  rewrite firstn_skipn_rev.
Focus 2.
rewrite H2.
apply Nat2Z.inj_le.
rewrite Nat2Z.inj_add by omega.
rewrite !Z2Nat.id by omega.
omega.
  rewrite len_le_1_rev.
  f_equal. f_equal. f_equal.
  rewrite <- Z2Nat.inj_add by omega. rewrite H2.
  rewrite <- Z2Nat.inj_sub by omega. f_equal; omega.
  rewrite firstn_length, min_l. 
  change 1%nat with (Z.to_nat 1). apply Z2Nat.inj_le; omega.
  rewrite skipn_length.  rewrite H2.
  rewrite <- Z2Nat.inj_sub by omega. apply Z2Nat.inj_le; omega.
Qed.

(* lists *)
Lemma Zlength_flip_between:
 forall A i j (al: list A),
 0 <= i  -> i<=j -> j <= Zlength al ->
 Zlength (flip_between i j al) = Zlength al.
Proof.
intros.
unfold flip_between.
rewrite !Zlength_app, !Zlength_firstn, !Zlength_skipn, !Zlength_rev.
forget (Zlength al) as n.
rewrite (Z.max_comm 0 i).
rewrite (Z.max_l i 0) by omega.
rewrite (Z.max_comm 0 j).
rewrite (Z.max_l j 0) by omega.
rewrite (Z.max_comm 0 (j-i)).
rewrite (Z.max_l (j-i) 0) by omega.
rewrite (Z.max_comm 0 (n-i)).
rewrite (Z.max_l (n-i) 0) by omega.
rewrite Z.max_r by omega.
rewrite (Z.min_l i n) by omega.
rewrite Z.min_l by omega.
omega.
Qed.

(* lists *)
Lemma flip_fact_3:
 forall A (al: list A) (d: A) j size,
  size = Zlength al ->
  0 <= j < size - j - 1 ->
firstn (Z.to_nat j)
  (firstn (Z.to_nat (size - j - 1)) (flip_between j (size - j) al) ++
   firstn (Z.to_nat 1) (skipn (Z.to_nat j) (flip_between j (size - j) al)) ++
   skipn (Z.to_nat (size - j - 1 + 1)) (flip_between j (size - j) al)) ++
firstn (Z.to_nat 1)
  (skipn (Z.to_nat (size - j - 1)) al) ++
skipn (Z.to_nat (j + 1))
  (firstn (Z.to_nat (size - j - 1)) (flip_between j (size - j) al) ++
   firstn (Z.to_nat 1) (skipn (Z.to_nat j) (flip_between j (size - j) al)) ++
   skipn (Z.to_nat (size - j - 1 + 1)) (flip_between j (size - j) al)) =
flip_between (Z.succ j) (size - Z.succ j) al.
Proof.
intros.
assert (Zlength (rev al) = size) by (rewrite Zlength_rev; omega).
unfold flip_between.
rewrite Zfirstn_app1.
Focus 2. {
rewrite Zlength_firstn, Z.max_r by omega.
rewrite !Zlength_app.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite !Zlength_skipn.
rewrite (Z.max_r 0 j) by omega.
rewrite (Z.max_r 0 (size-j)) by omega.
rewrite Z.max_r by omega.
rewrite Z.max_r by omega.
rewrite (Z.min_l j) by omega.
rewrite (Z.min_l (size-j-j)) by omega.
rewrite Z.min_l by omega.
omega.
} Unfocus.
rewrite Zfirstn_app2
 by (rewrite Zlength_firstn, Z.max_r by omega;
      rewrite Z.min_l by omega; omega).
rewrite Zfirstn_app1
 by (rewrite Zlength_firstn, Z.max_r by omega;
      rewrite Z.min_l by omega; omega).
rewrite Zfirstn_firstn by omega.
rewrite Zskipn_app1.
Focus 2. {
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_rev. 
rewrite !Zlength_app.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Z.min_l by omega.
rewrite Zlength_firstn.
rewrite (Z.min_l j (Zlength al)) by omega.
rewrite Z.max_r by omega.
rewrite Zlength_app.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_skipn.
rewrite (Z.max_r 0 j)  by omega.
rewrite (Z.max_r 0 ) by omega.
rewrite (Z.min_l  (size-j-j)) by omega.
rewrite Zlength_skipn.
rewrite (Z.max_r 0 (size-j)) by omega.
rewrite Z.max_r by omega.
rewrite Z.min_l by omega.
omega.
} Unfocus.
rewrite Zskipn_app2
 by (rewrite Zlength_firstn, Z.max_r by omega;
       rewrite Z.min_l by omega; omega).
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Z.min_l by omega.
rewrite Zfirstn_app1.
Focus 2. {
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_skipn, (Z.max_r 0 j) by omega.
rewrite Z.max_r by omega.
rewrite Z.min_l by omega. omega.
} Unfocus.
rewrite Zfirstn_firstn by omega.
rewrite Zskipn_app2
 by (rewrite Zlength_firstn, Z.max_r by omega;
       rewrite Z.min_l by omega; omega).
rewrite Zskipn_app1.
Focus 2. {
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Z.min_l by omega.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_skipn, (Z.max_r 0 j) by omega.
rewrite Z.max_r by omega.
rewrite Z.min_l by omega. omega.
} Unfocus.
rewrite Zfirstn_app1.
Focus 2. {
rewrite !Zlength_skipn, !Zlength_firstn.
rewrite (Z.max_r 0 j) by omega.
rewrite (Z.min_l j) by omega.
rewrite Zlength_skipn.
rewrite (Z.max_r 0 j) by omega.
rewrite (Z.max_r 0 (Zlength al - j)) by omega.
rewrite (Z.max_l 0 (j-j)) by omega.
rewrite (Z.max_r 0 (size-j-j)) by omega.
rewrite Z.min_l by omega.
rewrite Z.max_r by omega.
omega.
} Unfocus.
rewrite Zskipn_app2.
Focus 2. {
rewrite Zlength_firstn, Z.max_r by omega.
rewrite (Z.min_l j) by omega.
omega.
} Unfocus.
rewrite Zskipn_app2.
Focus 2. {
rewrite Zlength_firstn, Z.max_r by omega.
rewrite (Z.min_l j) by omega.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_skipn, (Z.max_r 0 j) by omega.
rewrite Z.max_r by omega.
rewrite Z.min_l by omega.
omega.
} Unfocus.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_skipn, (Z.max_r 0 j) by omega.
rewrite Z.max_r by omega.
rewrite Z.min_l by omega.
rewrite Z.min_l by omega.
rewrite Zskipn_skipn by omega.
rewrite !Zskipn_firstn by omega.
rewrite !Z.sub_diag.
rewrite Z.sub_0_r.
rewrite !Zskipn_skipn by omega.
rewrite Zfirstn_firstn by omega.
rewrite <- app_ass.
f_equal.
rewrite <- (firstn_skipn (Z.to_nat j) (rev al)) at 2.
rewrite Zfirstn_app2
  by (rewrite Zlength_firstn, Z.max_r by omega;
        rewrite Z.min_l by omega; omega).
rewrite Zlength_firstn, Z.max_r by omega;
rewrite Z.min_l by omega.
replace (Z.succ j - j) with 1 by omega.
f_equal.
rewrite app_nil_end.
rewrite app_nil_end at 1.
rewrite <- Znth_cons with (d0:=d) by omega.
rewrite <- Znth_cons with (d0:=d) by omega.
f_equal.
rewrite Znth_rev by omega.
f_equal. omega.
replace (size - j - 1 - j - (j + 1 - j))
  with (size- Z.succ j- Z.succ j) by omega.
replace (j+(j+1-j)) with (j+1) by omega.
f_equal.
rewrite Z.add_0_r.
rewrite <- (firstn_skipn (Z.to_nat 1) (skipn (Z.to_nat (size- Z.succ j)) (rev al))).
rewrite Zskipn_skipn by omega.
f_equal.
rewrite app_nil_end.
rewrite app_nil_end at 1.
rewrite <- Znth_cons with (d0:=d) by omega.
rewrite <- Znth_cons with (d0:=d) by omega.
f_equal.
rewrite Znth_rev by omega.
f_equal.
omega.
f_equal.
f_equal.
omega.
Qed.

(* theory of lists + lia *)
Lemma flip_fact_2:
  forall {A} (al: list A) size j d,
 Zlength al = size ->
  j < size - j - 1 ->
   0 <= j ->
  Znth (size - j - 1) al d =
  Znth (size - j - 1) (flip_between j (size - j) al) d.
Proof.
intros.
unfold flip_between.
rewrite app_Znth2
 by (rewrite Zlength_firstn, Z.max_r by omega;
      rewrite Zlength_rev, Z.min_l by omega; omega).
rewrite Zlength_firstn, Z.max_r by omega;
rewrite Zlength_rev, Z.min_l by omega.
rewrite app_Znth1.
Focus 2. {
rewrite Zlength_firstn, Z.max_r by omega;
rewrite Zlength_skipn by omega.
rewrite (Z.max_r 0 j) by omega.
rewrite Z.max_r by omega.
rewrite Z.min_l by omega.
omega. } Unfocus.
rewrite Znth_firstn by omega.
rewrite Znth_skipn by omega.
f_equal; omega.
Qed.

Require Import msl.shares.
Require Import veric.shares.
Require Import Integers.
Require Import compcert.common.Values.
Require Import veric.expr.
Require Import compcert.cfrontend.Ctypes.

Lemma verif_sumarray_example1:
forall (sh : share) (contents : list int) (size : Z) (a : val),
readable_share sh ->
0 <= size <= Int.max_signed ->
is_pointer_or_null a ->
@Zlength val (@map int val Vint contents) = size ->
0 <= 0 /\
(0 <= size /\ True) /\
a = a /\
Vint (Int.repr 0) = Vint (Int.repr 0) /\
Vint (Int.repr size) = Vint (Int.repr size) /\
Vint Int.zero = Vint (Int.repr 0) /\ True.
Abort.

Lemma verif_sumarray_example2:
forall (sh : share) (contents : list int) (size : Z) (a : val),
forall (sh : share) (contents : list int) (size a1 : Z) (a : val),
readable_share sh ->
0 <= size <= Int.max_signed ->
a1 < size ->
0 <= a1 <= size ->
is_pointer_or_null a ->
Zlength (map Vint contents) = size ->
is_int I32 Signed (Znth a1 (map Vint contents) Vundef).
Abort.

Require Import compcert.exportclight.Clightdefs.
(* from sem_add_default @ H:force_val... arithmetic + lists*)
Lemma verif_sumarray_example3:
forall (sum_int: list int -> int) (sh : share) (contents : list int) (size a1 : Z) (a : val) (x s : int),
(forall (contents0 : list int) (i : Z) (x0 : int),
 Znth i (map Vint contents0) Vundef = Vint x0 ->
 0 <= i ->
 sum_int (sublist 0 (Z.succ i) contents0) =
 Int.add (sum_int (sublist 0 i contents0)) x0) ->
readable_share sh ->
0 <= size <= Int.max_signed ->
a1 < size ->
0 <= a1 <= size ->
is_pointer_or_null a ->
force_val
  (sem_add_default tint tint (Vint (sum_int (sublist 0 a1 contents)))
                   (Znth a1 (map Vint contents) Vundef)) = Vint s ->
Znth a1 (map Vint contents) Vundef = Vint x ->
Zlength (map Vint contents) = size ->
0 <= Z.succ a1 /\
(Z.succ a1 <= size /\ True) /\
a = a /\
Vint (Int.repr (Z.succ a1)) = Vint (Int.repr (a1 + 1)) /\
Vint (Int.repr size) = Vint (Int.repr size) /\
Vint (sum_int (sublist 0 (Z.succ a1) contents)) = Vint s /\ True.
Abort.


Require Import floyd.assert_lemmas.  (* just for nullval? *)

(* this is false, n - m <> (n - (h + m) + h) if h+m > n and h <> 0 *)
Lemma verif_reverse_example1:
forall (sum_int: list int -> int) (sh : share) (contents cts : list int) (t0 t_old t : val) (h : int),
readable_share sh ->
isptr t0 ->
t0 = t_old ->
is_pointer_or_null t ->
is_pointer_or_null t ->
(t = nullval <-> map Vint cts = []) ->
t = t /\
Vint (Int.sub (sum_int contents) (sum_int cts)) =
Vint (Int.add (Int.sub (sum_int contents) (Int.add h (sum_int cts))) h) /\
True.
Abort.


(* true by app_assoc *)
Lemma verif_reverse_example2:
forall (sh : share) (contents cts1 : list val) (w h : val) (r : list val)
  (w_ t_ : val),
writable_share sh ->
contents = rev cts1 ++ h :: r ->
is_pointer_or_null t_ ->
is_pointer_or_null w_ ->
isptr w_ ->
is_pointer_or_null t_ ->
is_pointer_or_null t_ ->
(t_ = nullval <-> r = []) ->
is_pointer_or_null w ->
(w = nullval <-> cts1 = []) ->
contents = (rev cts1 ++ [h]) ++ r 
Abort.



