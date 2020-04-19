Require Import Coq.Arith.Arith.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FinFun.
Require Import Utils.language.
Require Import Utils.nodup.
Import List.ListNotations.

Notation "a ^ b" := (concat_words a b).

(** We define an order on words *)
Definition less (w1:word) (w2:word) :=
  exists u v, u ^ w1 ^ v = w2.

(** If to words are in relation and have the same size, then their equals *)
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
  unfold less in H.
  inversion H.
  inversion H0.
  rewrite <- H1.
  assert (size(u^x0) <= size(x ^ u ^ x0)).
  - apply size_le_concat_l.
  - assert (size(u) <= size(u^x0)).
    * apply size_le_concat_r.
    * rewrite H3. apply H2.
Qed.

(** Less is an order on words *)
Theorem less_ord: order word less.
Proof.
  split.
  - unfold reflexive.
    intros.
    unfold less. exists Void, Void. simpl. apply concat_w_void.
  - unfold transitive.
    intros x y z [u1 [v1 H1]] [u2 [v2 H2]].
    unfold less.
    exists (u2 ^ u1), (v1 ^ v2).
    rewrite <- concat_assoc.
    replace (x ^ v1 ^ v2) with ((x ^ v1) ^ v2).
    * replace (u1 ^ (x ^ v1) ^ v2) with (y ^ v2).
      + assumption.
      + rewrite <- H1. rewrite <- concat_assoc. reflexivity.
    * symmetry; apply concat_assoc.
  - unfold antisymmetric.
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


(** Ln is a language including all words on {I, O} whose sizes are less than n *)
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
  forall n, length (ln n) = Nat.pow 2 n.
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

Lemma disjoints2_mapO_mapI:
  forall a, disjoints2 (map (Concat O) a) (map (Concat I) a).
Proof.
  intro.
  unfold disjoints2.
  intros x.
  split;
  intros H1 H2;
  rewrite in_map_iff in H1;
  rewrite in_map_iff in H2;
  inversion H1 as [? [H1' _ ]];
  inversion H2 as [? [H2' _ ]];
  rewrite <- H1' in H2';
  discriminate H2'.
Qed.

Lemma extend_c_injective:
  forall c, Injective (Concat c).
Proof.
  unfold Injective.
  intros.
  inversion H.
  reflexivity.
Qed.

(** There is no redundancy in Ln *)
Lemma ln_NoDup:
  forall n, NoDup (ln n).
Proof.
  intros.
  induction n as [|n H].
  + simpl.
    apply NoDup_cons.
    * auto.
    * apply NoDup_nil.
  + simpl.
    apply NoDup_disjoints_app.
    apply disjoints2_mapO_mapI.
    all: apply Injective_map_NoDup; [apply extend_c_injective | assumption].
Qed.
