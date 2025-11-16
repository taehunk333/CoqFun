Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Lia.

Lemma add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma and_comm : forall P Q: Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split; assumption.
Qed.

Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IHn. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma app_nil_r : forall (A : Type) (l : list A), l ++ [] = l.
Proof.
  intros A l. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma double_plus : forall n, 2 * n = n + n.
Proof.
  intros n.
  induction n; simpl; try lia.
Qed.