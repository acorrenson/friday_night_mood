(***************************************
    Utils to proof that a list is 
    free of redundancy
***************************************)

Require Import Coq.Lists.List.
Import List.ListNotations.

Set Implicit Arguments.

Section Definitions.

  Variable A : Type.

  (** Inductive definition of disjoints lists *)
  Inductive disjoints : list A -> list A -> Prop :=
    | Disjoints_nil : forall l, disjoints [] l
    | Disjoints_cons_l : forall x l1 l2, ~ In x l2 -> disjoints l1 l2 -> disjoints (x::l1) l2.


  (** Classical definition of disjoints lists *)
  Definition disjoints2 (l1 l2 : list A) := 
    forall x, (In x l1 -> ~ In x l2) /\ (In x l2 -> ~In x l1).

End Definitions.


Section Facts.

  Variable A : Type.

  Lemma disjoints2_inv:
    forall (a : A) l1 l2,
      disjoints2 l1 l2 -> ~ In a l2 -> disjoints2 (a :: l1) l2.
  Proof.
    intros.
    unfold disjoints2.
    intros; split.
    - intros.
      inversion H1.
      * rewrite H2 in H0. assumption.
      * apply H. assumption.
    - red. intros.
      inversion H2.
      * rewrite <- H3 in H1. contradiction H1.
      * apply H in H3. assumption. assumption.
  Qed.

  Lemma disjoints2_cons:
  forall (a:A) l1 l2, disjoints2 (a :: l1) l2 -> disjoints2 l1 l2.
  Proof.
    intros.
    unfold disjoints2.
    intros.
    split.
    - intros.
      apply H.
      apply in_cons. assumption.
    - intros.
      red. intros.
      apply H in H0.
      apply not_in_cons in H0 as [_ H2].
      contradiction H1.
  Qed.


  Lemma disjoints2_comm:
    forall (l1: list A) (l2 : list A), disjoints2 l1 l2 -> disjoints2 l2 l1.
  Proof.
    intros l1 l2 H w.
    split; apply H.
  Qed.

  Lemma disjoints2_disjoints:
    forall (l1 l2 : list A), disjoints2 l1 l2 -> disjoints l1 l2.
  Proof.
    intros.
    induction l1.
    + apply Disjoints_nil.
    + apply Disjoints_cons_l.
      - apply H. apply in_eq.
      - apply IHl1.
        apply disjoints2_cons in H.
        assumption.
  Qed.

  Lemma disjoints_disjoints2:
    forall (l1 l2 : list A), disjoints l1 l2 -> disjoints2 l1 l2.
  Proof.
    intros.
    induction l1.
    + unfold disjoints2.
      intros.
      auto.
    + apply disjoints2_inv.
      * apply IHl1.
        inversion H. assumption.
      * inversion H. assumption.
  Qed.

  Lemma disjoints_iff:
    forall (l1 l2 : list A), disjoints l1 l2 <-> disjoints2 l1 l2.
  Proof.
    intros.
    split; [apply disjoints_disjoints2 | apply disjoints2_disjoints].
  Qed.

End Facts.

Section NoDup.

  Variable A : Type.

  Lemma NoDup_disjoints_app:
    forall (l1 l2 : list A), disjoints2 l1 l2 -> NoDup l1 -> NoDup l2 -> NoDup (l1 ++ l2).
  Proof.
    intros l1 l2 H1 H2 H3.
    induction l1 as [|w l1 IH].
    + simpl. assumption.
    + simpl.
      apply NoDup_cons_iff.
      split.
      - red.
        intros H4.
        apply in_app_or in H4 as [H6 | H6].
        * apply NoDup_cons_iff in H2 as [H7 _].
          contradiction H7.
        * apply H1 in H6.
          elim H6.
          apply in_eq.
      - apply IH.
        * apply disjoints2_cons in H1. assumption.
        * apply NoDup_cons_iff in H2 as [?]. assumption.
  Qed.

End NoDup.