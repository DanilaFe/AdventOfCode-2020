Require Import Coq.ZArith.Int.
Require Import Coq.Lists.ListSet.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Vectors.Fin.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Wf.
Require Import Lia.

Module DayEight (Import M:Int).
  (* We need to coerce natural numbers into integers to add them. *)
  Parameter nat_to_t : nat -> t.
  (* We need a way to convert integers back into finite sets. *)
  Parameter clamp : forall {n}, t -> option (Fin.t n).

  Definition fin := Fin.t.
  
  (* The opcode of our instructions. *)
  Inductive opcode : Type :=
    | add
    | nop
    | jmp.

  (* The result of running a program is either the accumulator
     or an infinite loop error. In the latter case, we return the
     set of instructions that we tried. *)
  Inductive run_result {n : nat} : Type :=
    | Ok : t -> run_result
    | Fail : set (fin n) -> run_result.

  (* A single program state .*)
  Definition state n : Type := (fin (S n) * set (fin n) * t).

  (* An instruction is a pair of an opcode and an argument. *)
  Definition inst : Type := (opcode * t).
  (* An input is a bounded list of instructions. *)
  Definition input (n : nat) := VectorDef.t inst n.
  (* 'indices' represents the list of instruction
     addresses, which are used for calculating jumps. *)
  Definition indices (n : nat) := VectorDef.t (fin n) n.

  (* Change a jump to a nop, or a nop to a jump. *)
  Definition swap (i : inst) : inst :=
    match i with
    | (add, t) => (add, t)
    | (nop, t) => (jmp, t)
    | (jmp, t) => (nop, t)
    end.

  Inductive swappable : inst -> Prop :=
  | swap_nop : forall t, swappable (nop, t)
  | swap_jmp : forall t, swappable (jmp, t).

  (* Compute the destination jump index, an integer. *)
  Definition jump_t {n} (pc : fin n) (off : t) : t :=
    M.add (nat_to_t (proj1_sig (to_nat pc))) off.

  (* Compute a destination index that's valid.
     Not all inputs are valid, so this may fail. *)
  Definition valid_jump_t {n} (pc : fin n) (off : t) : option (fin (S n)) := @clamp (S n) (jump_t pc off).

  (* Cast a fin n to a fin (S n). *)
  Fixpoint weaken_one {n} (f : fin n) : fin (S n) :=
    match f with
    | F1 => F1
    | FS f' => FS (weaken_one f')
    end.

  (* Convert a nat to fin. *)
  Fixpoint nat_to_fin (n : nat) : fin (S n) :=
    match n with
    | O => F1
    | S n' => FS (nat_to_fin n')
    end.

  (* A finite natural is either its maximum value (aka nat_to_fin n),
     or it's not thatbig, which means it can be cast down to
     a fin (pred n). *)
  Lemma fin_big_or_small : forall {n} (f : fin (S n)),
    (f = nat_to_fin n) \/ (exists (f' : fin n), f = weaken_one f').
  Proof.
    (* Hey, looks like the creator of Fin provided
       us with nice inductive principles. Using Coq's
       default `induction` breaks here.

       Merci, Pierre! *)
    apply Fin.rectS.
    - intros n. destruct n.
      + left. reflexivity.
      + right. exists F1. auto.
    - intros n p IH.
      destruct IH.
      + left. rewrite H. reflexivity.
      + right. destruct H as [f' Heq]. 
        exists (FS f'). simpl. rewrite Heq.
        reflexivity.
  Qed.
  
  (* One modification: we really want to use 'allowed' addresses,
     a set that shrinks as the program continues, rather than 'visited'
     addresses, a set that increases as the program continues. *)
  Inductive step_noswap {n} : inst -> (fin n * t) -> (fin (S n) * t) -> Prop :=
    | step_noswap_add : forall pc acc t,
        step_noswap (add, t) (pc, acc) (FS pc, M.add acc t)
    | step_noswap_nop : forall pc acc t,
        step_noswap (nop, t) (pc, acc) (FS pc, acc)
    | step_noswap_jmp : forall pc pc' acc t,
        valid_jump_t pc t = Some pc' ->
        step_noswap (jmp, t) (pc, acc) (pc', acc).

  Inductive done {n} : input n -> state n -> Prop :=
    | done_prog : forall inp v acc, done inp (nat_to_fin n, v, acc).

  Inductive stuck {n} : input n -> state n -> Prop :=
    | stuck_prog : forall inp pc' v acc,
        ~ set_In pc' v -> stuck inp (weaken_one pc', v, acc).

  Inductive run_noswap {n} : input n -> state n -> state n -> Prop :=
    | run_noswap_ok : forall inp st, done inp st -> run_noswap inp st st
    | run_noswap_fail : forall inp st, stuck inp st -> run_noswap inp st st
    | run_noswap_trans : forall inp pc pc' v acc acc' st',
        set_In pc v ->
        step_noswap (nth inp pc) (pc, acc) (pc', acc') ->
        run_noswap inp (pc', set_remove Fin.eq_dec pc v, acc') st' ->
        run_noswap inp (weaken_one pc, v, acc) st'.

  Inductive run_swap {n} : input n -> state n -> state n -> Prop :=
    | run_swap_normal : forall inp pc pc' v acc acc' st',
        set_In pc v ->
        ~ swappable (nth inp pc) ->
        step_noswap (nth inp pc) (pc, acc) (pc', acc') ->
        run_swap inp (pc', set_remove Fin.eq_dec pc v, acc') st' ->
        run_swap inp (weaken_one pc, v, acc) st'
    | run_swap_swapped_ok : forall inp pc pc' v acc acc' st',
        set_In pc v ->
        swappable (nth inp pc) ->
        step_noswap (swap (nth inp pc)) (pc, acc) (pc', acc') ->
        run_noswap inp (pc', set_remove Fin.eq_dec pc v, acc') st' ->
        done inp st' ->
        run_swap inp (weaken_one pc, v, acc) st'
    | run_swap_swapped_next : forall inp pc pc'w pc'n v acc acc'w acc'n st'w st'n,
        set_In pc v ->
        swappable (nth inp pc) ->
        step_noswap (swap (nth inp pc)) (pc, acc) (pc'w, acc'w) ->
        run_noswap inp (pc'w, set_remove Fin.eq_dec pc v, acc'w) st'w ->
        stuck inp st'w ->
        step_noswap (nth inp pc) (pc, acc) (pc'n, acc'n) ->
        run_swap inp (pc'n, set_remove Fin.eq_dec pc v, acc'n) st'n ->
        run_swap inp (weaken_one pc, v, acc) st'n.

  Inductive valid_inst {n} : inst -> fin n -> Prop :=
    | valid_inst_add : forall t f, valid_inst (add, t) f
    | valid_inst_nop : forall t f f',
        valid_jump_t f t = Some f' -> valid_inst (nop, t) f
    | valid_inst_jmp : forall t f f',
        valid_jump_t f t = Some f' -> valid_inst (jmp, t) f.

  (* An input is valid if all its instructions are valid. *)
  Definition valid_input {n} (inp : input n) : Prop := forall (pc : fin n),
    valid_inst (nth inp pc) pc.

  Section ValidInput.
    Variable n : nat.
    Variable inp : input n.
    Hypothesis Hv : valid_input inp.

    Theorem valid_input_can_step : forall pc acc, exists pc' acc',
      step_noswap (nth inp pc) (pc, acc) (pc', acc').
    Proof.
      intros pc acc.
      destruct (nth inp pc) eqn:Hop.
      destruct o.
      - exists (FS pc). exists (M.add acc t0). apply step_noswap_add. 
      - exists (FS pc). exists acc. eapply step_noswap_nop.
      - specialize (Hv pc). rewrite Hop in Hv. inversion Hv; subst.
        exists f'. exists acc. eapply step_noswap_jmp. apply H0.
    Qed.

    (* A program is either done, stuck (at an invalid/visited address), or can step. *)
    Theorem valid_input_progress : forall pc v acc,
      (pc = nat_to_fin n /\ done inp (pc, v, acc)) \/
      (exists pcs, pc = weaken_one pcs /\
        ((~ set_In pcs v /\ stuck inp (pc, v, acc)) \/
         (exists pc' acc', set_In pcs v /\
         step_noswap (nth inp pcs) (pcs, acc) (pc', acc')))).
    Proof.
      intros pc v acc.
      (* Have we reached the end? *)
      destruct (fin_big_or_small pc).
      (* We're at the end, so we're done. *)
      left. rewrite H. split. reflexivity. apply done_prog.
      (* We're not at the end. *)
      right. destruct H as [pcs H]. exists pcs. rewrite H. split. reflexivity.
      (* We're not at the end. Is the PC valid? *)
      destruct (set_In_dec Fin.eq_dec pcs v).
      - (* It is. *)
        right.
        destruct (valid_input_can_step pcs acc) as [pc' [acc' Hstep]].
        exists pc'; exists acc'; auto.
      - (* It is not. *)
        left. split; auto. apply stuck_prog; auto.
    Qed.

    (* A valid input always terminates, either by getting to the end of the program,
       or by looping and thus getting stuck. *)
    Program Fixpoint valid_input_terminates (pc : fin (S n)) (v : set (fin n)) (acc : t) (Hnd : List.NoDup v)
      { measure (length v) }:
      (exists pc', run_noswap inp (pc, v, acc) pc') :=
      match valid_input_progress pc v acc with
      | or_introl (conj Heq Hdone) => _
      | or_intror (ex_intro _ pcs (conj Hw w)) =>
          match w with
          | or_introl (conj Hnin Hstuck) => _
          | or_intror (ex_intro _ pc' (ex_intro _ acc' (conj Hin Hst))) =>
              match valid_input_terminates pc' (set_remove Fin.eq_dec pcs v) acc' (set_remove_nodup Fin.eq_dec pcs Hnd) with
              | ex_intro _ pc'' Hrun => _
              end
          end
      end.
    Obligation 1. eexists. apply run_noswap_ok. assumption. Qed.
    Obligation 2. eexists. apply run_noswap_fail. assumption. Qed.
    Obligation 3. 
      clear Heq_anonymous. clear valid_input_terminates. clear Hst.
      induction v.
      - inversion Hin.
      - destruct (Fin.eq_dec pcs a) eqn:Heq_dec.
        + simpl. rewrite Heq_dec. lia.
        + inversion Hnd; subst.
          inversion Hin. subst. exfalso. apply n0. auto.
          specialize (IHv H2 H).
          simpl. rewrite Heq_dec. simpl. lia.
    Qed.
    Obligation 4. eexists. eapply run_noswap_trans; auto. apply Hst. apply Hrun. Qed.
  End ValidInput.
End DayEight.
