Require Import Arith.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.

Require Import Logic.FinFun.

Inductive char : Type :=
  | O
  | I.

Inductive word : Type :=
  | Void
  | Concat: char -> word -> word.

Fixpoint size (w:word) :=
  match w with
  | Void => 0
  | Concat _ w => 1 + size (w)
  end.

Fixpoint concat_words w1 w2 :=
  match w1 with
  | Void => w2
  | Concat c w => 
    Concat c (concat_words w w2)
  end.

Notation "a ^ b" := (concat_words a b).

Lemma concat_w_void :
  forall w, w ^ Void = w.
Proof.
  intros.
  - induction w.
    + simpl. reflexivity.
    + simpl. rewrite IHw. reflexivity.
Qed.

Lemma concat_assoc:
  forall w1 w2 w3, w1 ^ w2 ^ w3 = (w1 ^ w2) ^ w3.
Proof.
  intros.
  induction w1.
  + simpl. reflexivity.
  + simpl. rewrite IHw1. reflexivity.
Qed.


Lemma size_concat :
  forall w1 w2, size (w1 ^ w2) = (size w1) + (size w2).
Proof.
  intros.
  induction w1 as [|c w IH].
  + simpl. reflexivity.
  + simpl. rewrite IH. reflexivity.
Qed.

Definition less (w1:word) (w2:word) :=
  exists u v, u ^ w1 ^ v = w2.

Check order.


Lemma concat_void :
  forall w, concat_words w Void = Void -> w = Void.
Proof.
  intros.
  induction w.
  + auto.
  + simpl in H.
    discriminate H.
Qed.

Lemma concat_concat_void: 
  forall u v,  u ^ v = Void -> u = Void /\ v = Void.
Proof.
  intros.
  split.
  + induction v.
    ++ apply concat_void. assumption.
    ++ induction u.
      * auto.
      * discriminate H.
  + induction u.
    simpl in H; assumption.
    ++ induction v.
      * auto.
      * discriminate H.
Qed.

Lemma concat_left_void :
  forall v w,
    v ^ w = v -> w = Void.
Proof.
  intros.
  induction v.
  + apply H.
  + simpl in H.
    inversion H.
    apply IHv. assumption.
Qed.

Lemma eq_size:
  forall u v,
    u = v -> size(u) = size(v).
Proof.
  intros [|u H1] [|v H2].
  + auto.
  + intros []. auto.
  + intros []. auto.
  + intros.
    inversion H.
    reflexivity.
Qed.

Lemma compare_size_l:
  forall u v, size(v) <= size(u ^ v).
Proof.
  intros.
  induction u.
  + simpl. auto.
  + simpl. apply le_S. assumption.
Qed.

Lemma compare_size_r:
  forall u v, size(v) <= size(v ^ u).
Proof.
  intros.
  induction v.
  + simpl. apply Nat.le_0_l.
  + simpl. apply le_n_S. apply IHv.
Qed.

Lemma size_void:
  forall u, u = Void <-> size(u) = 0.
Proof.
  intros.
  split.
  + intro. rewrite H. auto.
  + intro. induction u.
    * reflexivity.
    * discriminate H.
Qed.

Lemma size_concat_void_l:
  forall u v, size(u ^ v) = size(v) <-> u = Void.
Proof.
  intros.
  split.
  + rewrite size_concat. 
    intro. 
    rewrite Nat.add_comm in H.
    rewrite <- Nat.add_0_r in H.
    apply plus_reg_l in H.
    apply size_void in H. assumption.
  + intro.
    rewrite H.
    auto.
Qed.

Lemma size_concat_void_r:
  forall u v, size(v ^ u) = size(v) <-> u = Void.
Proof.
  intros.
  split.
  + rewrite size_concat.
    intro.
    rewrite <- Nat.add_0_r in H.
    apply plus_reg_l in H.
    apply size_void in H. assumption.
  + intro.
    rewrite H.
    rewrite concat_w_void.
    auto.
Qed.

Lemma concat_void_iff:
  forall u v, u ^ v = Void <-> u = Void /\ v = Void.
Proof.
  intros.
  split; intro.
  - apply eq_size in H.
    rewrite size_concat in H.
    simpl in H.
    apply plus_is_O in H.
    inversion H. 
    apply size_void in H0.
    apply size_void in H1.
    auto.
  - elim H.
    intros H2 H3.
    rewrite H2, H3.
    simpl. reflexivity.
Qed.


Lemma size_concat_void_lr:
  forall u v w, size(u ^ v ^ w) = size(v) <-> u = Void /\ w = Void.
Proof.
  intros.
  split.
  + intros.
    induction v.
    - simpl in H. apply size_void in H.
       apply concat_concat_void in H. assumption.
    - rewrite size_concat in H.
      rewrite size_concat in H.
      simpl in H. rewrite Nat.add_comm in H.
      simpl in H.
      inversion H.
      apply IHv.
      rewrite size_concat.
      rewrite size_concat.
      rewrite Nat.add_comm.
      assumption.
  + intros.
    inversion H.
    rewrite H0, H1.
    simpl. rewrite concat_w_void. reflexivity.
Qed.

Lemma less_size_eq:
  forall u v,
    less u v -> size(u) = size(v) -> u = v.
Proof.
  intros.
  inversion H.
  inversion H1.
  assert(H3:=H2).
  apply eq_size in H2.
  rewrite <- H0 in H2.
  rewrite size_concat_void_lr in H2.
  inversion H2.
  rewrite H4 in H3.
  rewrite H5 in H3.
  simpl in H3. rewrite concat_w_void in H3. assumption.
Qed.


Lemma less_le:
  forall u v,
    less u v -> size (u) <= size(v).
Proof.
  intros.
  + unfold less in H.
    inversion H.
    inversion H0.
    rewrite <- H1.
    assert (size(u^x0) <= size(x ^ u ^ x0)).
    ++ apply compare_size_l.
    ++ assert (size(u) <= size(u^x0)).
      +++ apply compare_size_r.
      +++ rewrite H3. apply H2.
Qed.

Theorem less_ord: order word less.
Proof.
  split.
  + unfold reflexive.
    intros.
    * unfold less. exists Void, Void. simpl. apply concat_w_void.
  + unfold transitive.
    intros x y z [u1 [v1 H1]] [u2 [v2 H2]].
    unfold less.
    exists (u2 ^ u1), (v1 ^ v2).
    rewrite <- concat_assoc.
    replace (x ^ v1 ^ v2) with ((x ^ v1) ^ v2).
    ++ replace (u1 ^ (x ^ v1) ^ v2) with (y ^ v2).
      +++ assumption.
      +++ rewrite <- H1. rewrite <- concat_assoc. reflexivity.
    ++ symmetry; apply concat_assoc.
  + unfold antisymmetric.
    intros x y.
    intros H1 H2.
    assert (H3:less x y) by assumption.
    apply less_le in H1.
    apply less_le in H2.
    cut (size(x) = size(y)).
    * intros.
      apply less_size_eq; assumption.
    * apply le_antisym; assumption.
Qed.

Lemma void_minimal_less :
  forall w, less Void w.
Proof.
  intros.
  unfold less.
  exists Void, w.
  + simpl. reflexivity.
Qed.


Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Import List.ListNotations.

Lemma word_eq_dec :
  forall x y:word, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Qed.

Fixpoint ln (n:nat) : list word :=
  match n with
  | 0 => [Void]
  | S m =>
    let lnm := (ln m) in
    let with_O := map (Concat O) lnm in
    let with_I := map (Concat I) lnm in
     with_O ++ with_I
  end.

Lemma card_ln:
  forall n, List.length (ln n) = Nat.pow 2 n.
Proof.
  intro.
  induction n.
  + simpl. reflexivity.
  + simpl.
    rewrite app_length.
    rewrite map_length.
    rewrite map_length.
    rewrite IHn.
    simpl.
    rewrite Nat.add_0_r.
    reflexivity.
Qed.

Lemma extend_c_injective:
  forall c, Injective (Concat c).
Proof.
  unfold Injective.
  intros.
  inversion H.
  reflexivity.
Qed.

Inductive disjoints : (list word) -> (list word) -> Prop :=
  | Disjoints_nil : forall l, disjoints [] l
  | Disjoints_cons_l : forall x l1 l2, ~ In x l2 -> disjoints l1 l2 -> disjoints (x::l1) l2.

Check(disjoints_ind).

Lemma NoDup_app_disjoints: 
  forall l1 l2, disjoints l1 l2 -> NoDup l1 -> NoDup l2 -> NoDup (l1 ++ l2).
Proof.
  intros.
  induction l1.
  ++ simpl. assumption.
  ++ simpl app.
    inversion H0.
    inversion H.
    apply IHl1 in H10.
    apply NoDup_cons_iff.
    split.
    * rewrite in_app_iff.
      unfold not.
      intros.
      elim H11; [apply H4 | apply H8].
    * assumption.
    * assumption.
Qed.


Lemma super:
  forall a x, In x (map (Concat I) a) -> exists w, x = Concat I w.
Proof.
  intros.
  rewrite in_map_iff in H.
  inversion H.
  inversion H0.
  exists x0.
  symmetry. 
  assumption.
Qed.


Definition disjoints2 (l1 l2 : list word) := 
  forall x, In x l1 -> ~ In x l2 /\ forall x, In x l2 -> ~In x l1.

Lemma disjoints2_mapO_mapI:
  forall a, disjoints2 (map (Concat O) a) (map (Concat I) a).
Proof.
  intro.
  induction a.
  + simpl. 
    unfold disjoints2.
    split;intros.
    - auto.
    - intro. auto.
  + unfold disjoints2.
    split; intros.
    - rewrite in_map_iff in H.
      inversion H.
      inversion H0.
      rewrite in_map_iff.
      red.
      intros [x1 [H3 H4]].
      rewrite <- H3 in H1.
      discriminate H1.
    - rewrite in_map_iff in H0.
      inversion H0.
      inversion H1.
      rewrite in_map_iff.
      red.
      intros [x2 [H4 H5]].
      rewrite <- H4 in H2.
      discriminate H2.
Qed.

Lemma disjoints_mapO_mapI:
  forall a, disjoints (map (Concat O) a) (map (Concat I) a).
Proof.
  intros.
  induction a.
  + simpl. apply Disjoints_nil.
  + simpl. apply Disjoints_cons_l.
    * simpl. unfold not. intro.
      inversion H.
      discriminate H0.
      apply super in H0.
      inversion H0.
      discriminate H1.
    *


Lemma ln_set:
  forall n, NoDup (ln n).
Proof.
  intros.
  induction n as [|n H].
  + simpl.
    apply NoDup_cons.
    ++ auto.
    ++ apply NoDup_nil.
  + simpl.
    apply NoDup_app_disjoints.
    *
    apply Injective_map_NoDup.