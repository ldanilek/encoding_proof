Require Import EqNat.
Require Import PeanoNat.
Require Import String.
Require Import BinNums.
Require Import List.
Require Import Compare_dec.
Require Import Omega.
Require Import Bool.
Set Implicit Arguments.

Section PREFIX.

Definition B: Type := list bool.

(* is b1 a prefix of b2 *)
Fixpoint is_prefix_bool (b1 b2: B): bool :=
  match b1 with
  | nil => true
  | f1::r1 => match b2 with
    | nil => false
    | f2::r2 => (eqb f1 f2 && is_prefix_bool r1 r2)
    end
  end.

Definition is_prefix (b1 b2: B): Prop :=
  is_prefix_bool b1 b2 = true.
Hint Unfold is_prefix.

Lemma is_prefix_spec: forall (b1 b2: B),
  is_prefix b1 b2 <-> b1 = firstn (length b1) b2.
Proof.
autounfold. induction b1; simpl; intros;
split; intros; try trivial.
- (* prefix implies firstn *)
destruct b2. discriminate.
apply andb_true_iff in H. destruct H.
apply eqb_prop in H.
apply IHb1 in H0.
subst a. rewrite <- H0. trivial.
- (* firstn implies prefix *)
destruct b2. discriminate.
injection H; intros.
apply IHb1 in H0.
subst a. rewrite H0.
rewrite eqb_reflx. simpl. trivial.
Qed.

Lemma is_prefix_app: forall (b1 b2: B),
  is_prefix b1 b2
  <-> exists b3, b1 ++ b3 = b2.
Proof.
intros; split; intros.
-
apply is_prefix_spec in H.
exists (skipn (length b1) b2).
remember (length b1) as n.
rewrite H.
apply firstn_skipn.
-
destruct H.
apply is_prefix_spec.
subst b2.
rewrite firstn_app.
rewrite firstn_all.
cut (length b1 - length b1 = O).
intro. rewrite H. rewrite firstn_O. rewrite app_nil_r. trivial.
omega.
Qed.

Lemma is_prefix_refl: forall b, is_prefix b b.
Proof.
intros. apply is_prefix_app. exists nil. apply app_nil_r.
Qed.

Lemma is_prefix_nil: forall b, is_prefix nil b.
Proof.
intros. autounfold. simpl. easy.
Qed.

Lemma is_nil_prefix: forall b, is_prefix b nil -> b = nil.
Proof.
induction b; autounfold; simpl; intros; trivial.
discriminate.
Qed.
(*
Lemma is_prefix_append: forall p b f, is_prefix p (b ++ (f::nil)) ->
  is_prefix p b \/ p = b ++ (f::nil).
Proof.
intros. apply is_prefix_app in H. 
destruct H.
rewrite <- H. destruct x.
- right. rewrite app_nil_r. reflexivity.
- left. apply is_prefix_spec.
Qed.
*)
End PREFIX.
