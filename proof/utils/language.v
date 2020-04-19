(***************************************
    Definitions and facts about words 
    on the alphabet {O, I}
***************************************)


Require Import Arith.

Section Definitions.

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

End Definitions.


Section Facts.

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


  Lemma concat_w_void_void :
    forall w, concat_words w Void = Void -> w = Void.
  Proof.
    intros.
    induction w.
    + auto.
    + simpl in H.
      discriminate H.
  Qed.

  Lemma concat_w_w_void: 
    forall u v,  u ^ v = Void -> u = Void /\ v = Void.
  Proof.
    intros.
    split.
    + induction v.
      ++ apply concat_w_void_void. assumption.
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

  Lemma size_le_concat_l:
    forall u v, size(v) <= size(u ^ v).
  Proof.
    intros.
    induction u.
    + simpl. auto.
    + simpl. apply le_S. assumption.
  Qed.

  Lemma size_le_concat_r:
    forall u v, size(v) <= size(v ^ u).
  Proof.
    intros.
    induction v.
    + simpl. apply Nat.le_0_l.
    + simpl. apply le_n_S. apply IHv.
  Qed.

  Lemma size_0_iff:
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
      apply size_0_iff in H. assumption.
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
      apply size_0_iff in H. assumption.
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
      apply size_0_iff in H0.
      apply size_0_iff in H1.
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
      - simpl in H. apply size_0_iff in H.
        apply concat_w_w_void in H. assumption.
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

End Facts.