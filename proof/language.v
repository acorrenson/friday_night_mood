Require Import Arith.
Require Import Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import FunInd.

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

Lemma void_concat :
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

Compute (Concat O Void ^ Concat I Void ^ Concat O Void).

Lemma concat_size :
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

Lemma concat_size_void_l:
  forall u v, size(u ^ v) = size(v) <-> u = Void.
Proof.
  intros.
  split.
  + rewrite concat_size. 
    intro. 
    rewrite Nat.add_comm in H.
    rewrite <- Nat.add_0_r in H.
    apply plus_reg_l in H.
    apply size_void in H. assumption.
  + intro.
    rewrite H.
    auto.
Qed.

Lemma concat_size_void_r:
  forall u v, size(v ^ u) = size(v) <-> u = Void.
Proof.
  intros.
  split.
  + rewrite concat_size.
    intro.
    rewrite <- Nat.add_0_r in H.
    apply plus_reg_l in H.
    apply size_void in H. assumption.
  + intro.
    rewrite H.
    rewrite void_concat.
    auto.
Qed.

Lemma concat_eq_void:
  forall u v, u ^ v = Void -> u = Void /\ v = Void.
Proof.
  intros.
  apply eq_size in H.
  rewrite concat_size in H.
  simpl in H.
  apply plus_is_O in H.
  inversion H. 
  apply size_void in H0.
  apply size_void in H1.
  auto.
Qed.


Lemma concat_size_void_lr:
  forall u v w, size(u ^ v ^ w) = size(v) <-> u = Void /\ w = Void.
Proof.
  intros.
  split.
  + intros.
    induction v.
    - simpl in H. apply size_void in H.
       apply concat_concat_void in H. assumption.
    - rewrite concat_size in H.
      rewrite concat_size in H.
      simpl in H. rewrite Nat.add_comm in H.
      simpl in H.
      inversion H.
      apply IHv.
      rewrite concat_size.
      rewrite concat_size.
      rewrite Nat.add_comm.
      assumption.
  + intros.
    inversion H.
    rewrite H0, H1.
    simpl. rewrite void_concat. reflexivity.
Qed.

Lemma super_lemma:
  forall u v,
    less u v -> size(u) = size(v) -> u = v.
Proof.
  intros.
  inversion H.
  inversion H1.
  assert(H3:=H2).
  apply eq_size in H2.
  rewrite <- H0 in H2.
  rewrite concat_size_void_lr in H2.
  inversion H2.
  rewrite H4 in H3.
  rewrite H5 in H3.
  simpl in H3. rewrite void_concat in H3. assumption.
Qed.


Lemma less_le_size:
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
    * unfold less. exists Void, Void. simpl. apply void_concat.
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
    apply less_le_size in H1.
    apply less_le_size in H2.
    cut (size(x) = size(y)).
    * intros.
      apply super_lemma; assumption.
    * apply le_antisym; assumption.
Qed.

Lemma void_minimal :
  forall w, less Void w.
Proof.
  intros.
  unfold less.
  exists Void, w.
  + simpl. reflexivity.
Qed.
