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

(* note all of this prefix stuff doesn't require B to be a list of bool;
it could be any type with decidable equality. *)
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
Lemma list_induction_append: forall T P,
  P nil ->
  (forall l (v: T), P l -> P (l ++ (v::nil))) ->
  (forall l, P l).
Proof.
Qed.*)

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

(*
it's true but hard to prove
Lemma prefix_length: forall p b x y,
  p ++ x = b ++ y ->
  length y <= length x ->
  is_prefix p b.
Proof.
*)

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

End PREFIX.
