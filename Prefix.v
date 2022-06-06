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

Variable X: Type.

Hypothesis x_eq_dec: forall (x y: X), {x = y} + {x <> y}.

Definition eqx (x y: X): bool :=
  match x_eq_dec x y with
  | left _ => true
  | right _ => false
  end.

Lemma eqx_prop: forall x y, eqx x y = true <-> x = y.
Proof.
intros.
unfold eqx.
destruct x_eq_dec. split; trivial.
split. intro. discriminate.
intro. apply n in H. contradiction.
Qed.

Lemma eqx_reflx: forall x, eqx x x = true.
Proof.
unfold eqx. intro.
destruct (x_eq_dec x x). reflexivity. contradiction.
Qed.


(* can think of X as a bool and B as a bitstring, but everything
in this file is general to any type with decidable equality.
*)
Definition B: Type := list X.


(* is b1 a prefix of b2 *)
Fixpoint is_prefix_bool (b1 b2: B): bool :=
  match b1 with
  | nil => true
  | f1::r1 => match b2 with
    | nil => false
    | f2::r2 => (eqx f1 f2 && is_prefix_bool r1 r2)
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
apply eqx_prop in H.
apply IHb1 in H0.
subst a. rewrite <- H0. trivial.
- (* firstn implies prefix *)
destruct b2. discriminate.
injection H; intros.
apply IHb1 in H0.
subst a. rewrite H0.
rewrite eqx_reflx. simpl. trivial.
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

Lemma list_induction_append: forall T (P: list T->Prop),
  P nil ->
  (forall l (v: T), P l -> P (l ++ (v::nil))) ->
  (forall l, P l).
Proof.
intros.
apply rev_ind.
assumption. intros. apply H0. assumption.
Qed.

(*
Lemma nonempty_append: forall T l (v: T),
  exists s, cons v l = (firstn (length l) (cons v l)) ++ s::nil.
Proof.
induction l; simpl; intros.
- exists v. reflexivity.
-  

Qed.*)

Lemma nonzero_length: forall T (l: list T),
  l <> nil <-> 1 <= length l.
Proof.
destruct l; simpl.
- split; intro. contradiction. omega.
- split; intro. omega. intro. discriminate.
Qed.

Lemma apply_both_sides: forall T U (f: T->U) a b,
  a = b -> f a = f b.
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma removelast_both_sides: forall T (a: list T) b,
  a = b -> removelast a = removelast b.
Proof.
intros. apply apply_both_sides. assumption.
Qed.

Lemma length_both_sides: forall T (a: list T) b,
  a = b -> length a = length b.
Proof.
intros. apply apply_both_sides. assumption.
Qed.

(* docs say this is in the List library, but it's not there.
so we prove it.
*)
Lemma removelast_last:
  forall T l (a: T), removelast (l ++ a::nil) = l.
Proof.
induction l; simpl; intros.
reflexivity.
remember (l ++ a0::nil) as l0. destruct l0.
- apply length_both_sides in Heql0.
rewrite app_length in Heql0. simpl in Heql0. omega.
-
apply removelast_both_sides in Heql0.
rewrite IHl in Heql0. rewrite Heql0. reflexivity.
Qed.

Lemma append_nonempty_prefix: forall p b x f,
  p ++ x = b ++ (f::nil) ->
  1 <= length x ->
  is_prefix p b.
Proof.
intros. apply is_prefix_app.
apply nonzero_length in H0.
destruct (exists_last H0). destruct s.
subst x.
exists x0.
apply removelast_both_sides in H.
rewrite app_assoc in H.
repeat rewrite removelast_last in H.
assumption.
Qed.

Lemma is_prefix_append: forall p b f,
  is_prefix p (b ++ (f::nil)) ->
  is_prefix p b \/ p = b ++ (f::nil).
Proof.
intros. apply is_prefix_app in H. 
destruct H.
rewrite <- H. destruct x.
- right. rewrite app_nil_r. reflexivity.
- left. apply append_nonempty_prefix in H. assumption.
simpl. omega.
Qed.

Lemma nat_cmp: forall (x y: nat), x > y \/ x = y \/ y > x.
Proof.
intros. omega.
Qed.

Lemma prefix_app_helper: forall p b x,
  p ++ x = b -> is_prefix p b.
Proof.
intros. apply is_prefix_app. exists x. assumption.
Qed.

Lemma prefix_removelast: forall (p: B) b f g,
  p ++ (f::nil) = b ++ (g::nil) ->
  p = b.
Proof.
intros.
apply removelast_both_sides in H. repeat rewrite removelast_last in H.
assumption.
Qed.

Lemma rev_destruct: forall (x: B) d,
  x = nil \/ x = (removelast x)++(last x d)::nil.
Proof.
destruct x. left. reflexivity.
right.
eapply app_removelast_last. intro. discriminate.
Qed.

Lemma last_last: forall (x: B) x0 d, last (x++x0::nil) d = x0.
Proof.
induction x; simpl; intros.
reflexivity.
rewrite IHx.
remember (x++x0::nil) as xs. destruct xs.
apply length_both_sides in Heqxs.
rewrite app_length in Heqxs. simpl in Heqxs. omega.
reflexivity.
Qed.

Lemma rev_injection: forall (x: B) y x0 y0,
  x++x0::nil = y++y0::nil -> x = y /\ x0 = y0.
Proof.
intros. split.
- apply removelast_both_sides in H.
  repeat rewrite removelast_last in H.
  assumption.
- apply (apply_both_sides (fun k => @last X k x0)) in H.
  repeat rewrite last_last in H. assumption.
Qed.

Lemma length_removelast: forall (x: B),
  length (removelast x) <= length x.
Proof.
induction x; simpl; intros.
omega.
destruct x. simpl. omega.
remember (removelast (x::x0)) as y. simpl. simpl in IHx.
omega.
Qed.

Lemma prefix_app_length: forall y x p b,
  p ++ x = b ++ y ->
  length x > length y ->
  is_prefix p b.
Proof.
apply (rev_ind (fun y => forall x p b,
  p ++ x = b ++ y ->
  length x > length y ->
  is_prefix p b)).
- simpl. intros. rewrite app_nil_r in H.
  apply is_prefix_app. exists x. assumption.
- intro y0. intro y. (* inductive case y = y++y0::nil *)
  intros.
  destruct (rev_destruct x y0).
  subst x. simpl in H1. omega.
  rewrite H2 in H0.
  repeat rewrite <- app_ass in H0.
  apply H with (removelast x).
  apply rev_injection in H0. destruct H0. assumption.
  rewrite app_length in H1. simpl in H1.
  apply length_both_sides in H2. rewrite app_length in H2. simpl in H2.
  omega.
Qed.

Lemma firstn_length: forall (x: B), firstn (length x) x = x.
Proof.
induction x; simpl; intros.
reflexivity. rewrite IHx. reflexivity.
Qed.

Lemma firstn_app: forall (x: B) y, firstn (length x) (x++y) = x.
Proof.
induction x; simpl; intros.
reflexivity.
rewrite IHx. reflexivity.
Qed.

Lemma prefix_app_length_eq: forall (y: B) x p b,
  p ++ x = b ++ y ->
  length x = length y ->
  p = b.
Proof.
intros.
cut (length p = length b).
- intro.
  apply (apply_both_sides (firstn (length p))) in H.
  rewrite firstn_app in H.
  rewrite H1 in H. rewrite firstn_app in H. assumption.
- apply length_both_sides in H. repeat rewrite app_length in H. omega.
Qed.

Theorem equal_prefix: forall p1 p2 b1 b2,
  p1 ++ b1 = p2 ++ b2 ->
  is_prefix p1 p2 \/ is_prefix p2 p1.
Proof.
intros.
assert (CMP := nat_cmp (length b1) (length b2)).
destruct CMP.
left. eapply prefix_app_length; eauto.
destruct H0.
left. cut (p1 = p2). intro. subst. apply is_prefix_refl.
eapply prefix_app_length_eq; eauto.
right. eapply prefix_app_length; eauto.
Qed.

End PREFIX.
