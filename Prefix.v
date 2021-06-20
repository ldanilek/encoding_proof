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

End PREFIX.

Section CODE.

(* the type being encoded. e.g. letters *)
Variable V: Type.

(* V has at least two possible values *)
Variable v01 v02: V.
Hypothesis v_diff:
  v01 <> v02.

Hypothesis v_dec:
  forall (v1 v2: V), {v1 = v2} + {v1 <> v2}.

Definition Code: Type := V -> B.
Definition Decode: Type := B -> option V.

Variable c: Code.
Variable d: Decode.

(* d is the decoder for the encoder c *)
Hypothesis c_d_inv:
  forall v b, d b = Some v <-> c v = b.

(* what does it mean to be a prefix code?
you can't have one code be a prefix of another.
 *)
Hypothesis is_prefix_code:
  forall v1 v2, is_prefix (c v1) (c v2) -> v1 = v2.

Lemma nonempty_code: forall v, c v <> nil.
Proof.
intros. intro.
cut (exists v1, v1 <> v).
intro. destruct H0.
assert (NIL := is_prefix_nil (c x)).
rewrite <- H in NIL.
apply is_prefix_code in NIL.
apply H0. auto.
destruct (v_dec v v01).
exists v02. intro. subst v. rewrite H0 in v_diff. contradiction.
exists v01. intro. rewrite H0 in n. contradiction.
Qed.

Definition encode (vs: list V): B :=
  flat_map c vs.

Definition is_unmatched_prefix (unmatched: B) :=
  forall p, is_prefix p unmatched -> d p = None.

Lemma nil_is_unmatched: is_unmatched_prefix nil.
Proof.
unfold is_unmatched_prefix; intros; simpl.
apply is_nil_prefix in H. rewrite H.
unfold is_prefix in H. unfold is_prefix_bool in H.
remember (d nil) as v. destruct v; trivial.
symmetry in Heqv. apply c_d_inv in Heqv. apply nonempty_code in Heqv.
contradiction.
Qed.


(* decodes unmatched++b into list of values *)
Fixpoint decode_helper (unmatched b: B) 
(proof_unmatched: is_unmatched_prefix unmatched)
{struct b}: option (list V) :=
  match b with
  | nil => match unmatched with
    | nil => Some nil
    | _ => None
    end
  | f::r =>
    let pref := unmatched ++ (f::nil) in
      match d pref with
      | None => decode_helper pref r
      | Some v => match decode_helper nil r proof_ with
        | None => None
        | Some vs => Some (v :: vs)
        end
      end
  end.

Definition decode (b: B): option (list V) :=
  decode_helper nil b.

Lemma encode_not_nil:
  forall x, encode x = nil -> x = nil.
Proof.
induction x; simpl; intros.
trivial.
apply app_eq_nil in H. destruct H.
apply nonempty_code in H.
contradiction.
Qed.

Lemma decode_helper_inv:
  forall b unmatched vs, decode_helper unmatched b = Some vs 
  <-> encode vs = unmatched ++ b.
Proof.
induction b; induction unmatched; simpl; intros.
- split; intros. injection H; intros; subst. simpl. trivial.
  apply encode_not_nil in H. rewrite H. trivial.
- split; intros. discriminate. 

Theorem encode_decode_inv:
  forall bs vs, decode bs = Some vs <-> encode vs = bs.
Proof.
induction bs; unfold decode; simpl; intros.
- (* encoded to nil *)
split; intros. injection H; intros; subst. simpl. trivial.
apply encode_not_nil in H. rewrite H. trivial.
- (* encoded to not nil *)
unfold encode. 
split. 



Qed.

End CODE.

Section CONSTLENGTH.

END CONSTLENGTH.

Section LENGTHPREFIX.

End LENGTHPREFIX.