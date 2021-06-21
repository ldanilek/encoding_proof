Require Import EqNat.
Require Import PeanoNat.
Require Import String.
Require Import BinNums.
Require Import List.
Require Import Compare_dec.
Require Import Omega.
Require Import Bool.
Require Import Logic.

(* local import *)
Require Import Prefix.

Set Implicit Arguments.

Definition equal_some (T: Type) (x: option T) (y: T): Prop :=
  x = Some y.

Lemma none_dec: forall T (x: option T),
  {x = None} + {True}.
Proof.
destruct x. right. trivial.
left. reflexivity.
Defined.

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
Hint Unfold is_unmatched_prefix.

Lemma nil_is_unmatched: is_unmatched_prefix nil.
Proof.
autounfold; intros; simpl.
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
autounfold.
intros.
apply is_prefix_append in H1.
destruct H1. apply H. assumption.
subst p. assumption.
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
      | None => match none_dec (d pref) with
        | left pref_no_decode =>
          @decode_helper pref r
          (@append_unmatched unmatched f proof_unmatched pref_no_decode)
        | right _ => None (* unreachable *)
        end
      | Some v => match @decode_helper nil r nil_is_unmatched with
        | None => None
        | Some vs => Some (v :: vs)
        end
      end
  end.

Definition decode (b: B): option (list V) :=
  @decode_helper nil b nil_is_unmatched.

Lemma encode_not_nil:
  forall x, encode x = nil -> x = nil.
Proof.
induction x; simpl; intros.
trivial.
apply app_eq_nil in H. destruct H.
apply nonempty_code in H.
contradiction.
Qed.

Lemma encode_not_unmatched:
  forall vs unmatched,
  is_unmatched_prefix unmatched ->
  encode vs = unmatched ->
  unmatched = nil.
Proof.
induction vs; simpl; intros.
- symmetry. assumption.
- exfalso. subst unmatched. autounfold in H.
cut (d (c a) = None).
+ intro. remember (c a) as b. symmetry in Heqb.
  apply c_d_inv in Heqb. rewrite Heqb in H0. discriminate.
+ apply H. apply is_prefix_app. exists (encode vs).
reflexivity.
Qed.

Lemma list_split: forall T (b: T) c,
  b :: c = (b :: nil) ++ c.
Proof.
intros.
rewrite <- app_comm_cons.
simpl. reflexivity.
Qed.

Lemma list_app_split: forall T a (b: T) c,
  a ++ b :: c = (a ++ (b::nil)) ++ c.
Proof.
intros. rewrite list_split. rewrite app_assoc. reflexivity.
Qed.

Lemma decode_helper_inv:
  forall b unmatched vs is_unmatched,
  @decode_helper unmatched b is_unmatched = Some vs
  <-> encode vs = unmatched ++ b.
Proof.
induction b.
- (* b empty *)
  simpl. destruct unmatched; intros.
  * (* unmatched empty *)
  split; intros. injection H; intros; subst. simpl. trivial.
  apply encode_not_nil in H. rewrite H. trivial.
  * (* b empty, unmatched nonempty *)
  split; intros. discriminate. exfalso.
  rewrite app_nil_r in H.
  cut (b::unmatched = nil).
    + intro. discriminate.
    + eapply encode_not_unmatched; eauto.
- (* b nonempty *)
  intros.
  rewrite list_app_split.
  remember (d (unmatched ++ a::nil)) as d_pref.
  simpl.
  destruct d_pref.
  + (* unmatched++a::nil can be decoded *)
    (* rewrite once *)
    pattern (d (unmatched++a::nil)) at 1. rewrite <- Heqd_pref.
    split; intro.
    * (* valid decode -> valid encode *)
      remember (decode_helper b nil_is_unmatched) as decode_rest.
      destruct decode_rest. injection H; intros; subst.
      simpl. symmetry in Heqd_pref. apply c_d_inv in Heqd_pref.
      replace (encode l) with b. rewrite Heqd_pref. reflexivity.
      symmetry. replace b with (nil++b). eapply IHb.
      symmetry. eapply Heqdecode_rest.
      simpl. reflexivity.
      discriminate.
    * (* valid encode -> valid decode *)
      
  
  
  
Qed.

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