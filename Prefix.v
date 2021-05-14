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

Section CODE.

Variable V: Type.

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

Definition encode (vs: list V): B :=
  flat_map c vs.

Fixpoint decode_helper (b unmatched: B): option (list V) :=
  match b with
  | nil => Some nil
  | f::r =>
    let pref := unmatched ++ (f::nil) in
      match d pref with
      | None => decode_helper r pref
      | Some v => match decode_helper r nil with
        | None => None
        | Some vs => Some (v :: vs)
        end
      end
  end.

Definition decode (b: B): option (list V) :=
  decode_helper b nil.

(* lol this is false *)
Lemma flat_map_nil: 
  forall A B (f: A->list B) x,
  flat_map f x = nil -> x = nil.
Proof.
induction x; simpl; intros.
trivial.
apply app_eq_nil in H. destruct H.
Qed.

Theorem encode_decode_inv:
  forall bs vs, decode bs = Some vs <-> encode vs = bs.
Proof.
induction bs; simpl; intros.
- (* encoded to nil *)
unfold decode. simpl.
split; intros. injection H; intros; subst. simpl. trivial.


Qed.

End CODE.

End PREFIX.

Section CONSTLENGTH.

END CONSTLENGTH.

Section LENGTHPREFIX.

End LENGTHPREFIX.