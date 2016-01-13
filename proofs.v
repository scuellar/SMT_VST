Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.


Section PROOF.
  
Set Implicit Arguments.
Variable array: forall {A:Type}, Type.
Variable select: forall {A}, array A -> nat -> A.
Variable store : forall {A}, array A -> nat -> A -> array A.
  
Axiom QFAX1 : forall A a i (e:A), select (store a i e) i = e.  
Axiom QFAX2 : forall A a i j (e:A), i <> j -> select (store a i e) j = select a j.  
Axiom QFAX3 : forall A (a b: array A), (forall i, select a i = select b i) -> a = b.  



Fixpoint list_of_array' {A} L (ar:array A) :=
  match L with
    |  0%nat => nil
    | (S n)%nat => (select ar n)::(list_of_array' n ar)
  end.

Definition list_of_array {A} L (ar:array A) :=
  rev (list_of_array' L ar).

Lemma length_la': forall A (ar:array A) L, length (list_of_array' L ar) = L.
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
    replace (rev (list_of_array' L ar)) with (list_of_array L ar) by reflexivity.
    rewrite length_la; auto.
  - rewrite H0; auto.
    rewrite rev_nth; rewrite length_la';  simpl; auto.
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
      rewrite rev_length, length_la'.
      destruct (i-L)%nat eqn:eq. contradict H; omega.
      simpl. destruct n; reflexivity.
      rewrite rev_length, length_la'; assumption.
Qed.

Theorem enc_upd_lt:
  forall A i ss (a: array A) L ss',
    ( i < L)%nat ->
    ss' = store ss i a ->
    list_of_array L ss' = upd_nth i (list_of_array L ss) a.
Proof.
  intros. unfold list_of_array.
  rewrite rev_upd_nth; [|rewrite length_la'; auto].
  f_equal.
  rewrite length_la'.
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
      list_of_array' j (store ss i a) = list_of_array' j ss.
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
  - unfold list_of_array; simpl. rewrite app_nil_r. assert (list_of_array' L1 ss1 = list_of_array' L1 ss3). revert H. clear H0. revert ss1. revert ss3. induction L1; intros.
    + auto.
    + simpl. unfold list_of_array in IHL1. rewrite IHL1 with (ss3 := ss3) . rewrite H. reflexivity. omega. intros. apply H. omega.
    + rewrite H1. rewrite plus_0_r. reflexivity.
  - unfold list_of_array. replace (L1 + S L2)%nat with (S L1 + L2)%nat by omega.  simpl.
    assert (select ss2 L2 =  select ss3 (L1+L2)). rewrite plus_comm. apply H0. omega.
    assert (list_of_array L1 ss1 ++ list_of_array L2 ss2 = list_of_array (L1 + L2) ss3). apply IHL2.
    + assumption.
    + intros. apply H0. omega.
    + unfold list_of_array in H2. rewrite <- H2.  rewrite H1. apply app_assoc.
Qed.



End PROOF.