Require Import EqNat.
Require Import PeanoNat.
Require Import String.
Require Import BinNums.
Require Import List.
Require Import Compare_dec.
Require Import Omega.
Require Import Bool.

(* local import *)
Require Import Prefix.
Set Implicit Arguments.

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

Lemma append_unmatched: forall unmatched f,
  is_unmatched_prefix unmatched ->
  d (unmatched ++ (f::nil)) = None ->
  is_unmatched_prefix (unmatched ++ (f::nil)).
Proof.
intros. unfold is_unmatched_prefix.

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

End CONSTLENGTH.

Section LENGTHPREFIX.

End LENGTHPREFIX.