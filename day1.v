Require Import Coq.Sorting.Mergesort.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import ExtrHaskellBasic.

Definition has_pair (t : nat) (is : list nat) : Prop :=
  exists n1 n2 : nat, n1 <> n2 /\ In n1 is /\ In n2 is /\ n1 + n2 = t.

Fixpoint find_matching (is : list nat) (total : nat) (x : nat) : option nat :=
  match is with
  | nil => None
  | cons y ys =>
      if Nat.eqb (x + y) total
      then Some y
      else find_matching ys total x 
  end.

Fixpoint find_sum (is : list nat) (total : nat) : option (nat * nat) :=
  match is with
  | nil => None
  | cons x xs =>
      match find_matching xs total x with
      | None => find_sum xs total (* Was buggy! *)
      | Some y => Some (x, y)
      end
  end.

Lemma find_matching_correct : forall is k x y,
  find_matching is k x = Some y -> x + y = k.
Proof.
  intros is. induction is;
  intros k x y Hev.
  - simpl in Hev. inversion Hev.
  - simpl in Hev. destruct (Nat.eqb (x+a) k) eqn:Heq.
    + injection Hev as H; subst.
      apply EqNat.beq_nat_eq. auto.
    + apply IHis. assumption.
Qed.

Lemma find_matching_skip : forall k x y i is,
  find_matching is k x = Some y -> find_matching (cons i is) k x = Some y.
Proof.
  intros k x y i is Hsmall.
  simpl. destruct (Nat.eqb (x+i) k) eqn:Heq.
  - apply find_matching_correct in Hsmall.
    symmetry in Heq. apply EqNat.beq_nat_eq in Heq.
    assert (i = y). { omega. } rewrite H. reflexivity.
  - assumption.
Qed.

Lemma find_matching_works : forall is k x y, In y is /\ x + y = k ->
  find_matching is k x = Some y.
Proof.
  intros is. induction is;
  intros k x y [Hin Heq].
  - inversion Hin.
  - inversion Hin.
    + subst a. simpl. Search Nat.eqb.
      destruct (Nat.eqb_spec (x+y) k).
      * reflexivity.
      * exfalso. apply n. assumption.
    + apply find_matching_skip. apply IHis.
      split; assumption.
Qed.

Theorem find_sum_works :
  forall k is, has_pair k is ->
  exists x y, (find_sum is k = Some (x, y) /\ x + y = k).
Proof.
  intros k is. generalize dependent k.
  induction is; intros k [x' [y' [Hneq [Hinx [Hiny Hsum]]]]].
  - (* is is empty. But x is in is! *)
    inversion Hinx.
  - (* is is not empty. *)
    inversion Hinx. 
    + (* x is the first element. *)
      subst a. inversion Hiny.
      * (* y is also the first element; but this is impossible! *)
        exfalso. apply Hneq. apply H.
      * (* y is somewhere in the rest of the list.
           We've proven that we will find it! *)
        exists x'. simpl.
        erewrite find_matching_works.
        { exists y'. split. reflexivity. assumption. }
        { split; assumption. }
    + (* x is not the first element. *)
      inversion Hiny.
      * (* y is the first element,
           so x is somewhere in the rest of the list.
           Again, we've proven that we can find it. *)
        subst a. exists y'. simpl.
        erewrite find_matching_works.
        { exists x'. split. reflexivity. rewrite plus_comm. assumption. }
        { split. assumption. rewrite plus_comm. assumption. }
      * (* y is not the first element, either.
           Of course, there could be another matching pair
           starting with a. Otherwise, the inductive hypothesis applies. *)
        simpl. destruct (find_matching is k a) eqn:Hf.
        { exists a. exists n. split.
          reflexivity. 
          apply find_matching_correct with is. assumption. }
        { apply IHis. unfold has_pair. exists x'. exists y'.
          repeat split; assumption. }
Qed.

Extraction Language Haskell.
Extraction "test.hs" find_sum.

Check find_sum_works.

(* WIP stuff for 2-pointer solution. *)

Inductive non_empty {X : Type} : list X -> Prop :=
  | non_empty_cons : forall x xs, non_empty (cons x xs).

Lemma nil_empty {X: Type} : ~ @non_empty X nil.
Proof. intros H. inversion H. Qed.

Program Fixpoint last (is : list nat) (H : non_empty is) {measure (length is)} : nat :=
  match is with
  | nil => _
  | cons x nil => x
  | cons x (cons y xs) => last (cons y xs) _
  end.
Obligation 1.
  exfalso. apply (nil_empty H).
Qed.
Obligation 2.
  apply non_empty_cons.
Qed.

Program Fixpoint drop_last (is : list nat) (H : non_empty is) {measure (length is)} : list nat :=
  match is with
  | nil => _
  | cons x nil => nil
  | cons x (cons y xs) => cons x (drop_last (cons y xs) _)
  end.
Obligation 1.
  exfalso. apply (nil_empty H).
Qed.
Obligation 2.
  apply non_empty_cons.
Qed.

Program Fixpoint find_pair (is : list nat) (t : nat) : option (nat * nat) :=
  match is with
  | nil => None
  | cons x nil => None
  | cons x (cons y xs) => Some (x, last (cons y xs) _)
  end.
Obligation 1.
  apply non_empty_cons.
Qed.

