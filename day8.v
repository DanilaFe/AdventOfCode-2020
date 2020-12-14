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
  Definition replace (i : inst) : inst :=
    match i with
    | (add, t) => (add, t)
    | (nop, t) => (jmp, t)
    | (jmp, t) => (nop, t)
    end.

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
  Inductive step_noswap {n} : input n -> state n -> state n -> Prop :=
    | step_noswap_add : forall inp pc' v acc t,
        nth inp pc' = (add, t) ->
        set_In pc' v ->
        step_noswap inp (weaken_one pc', v, acc) (FS pc', set_remove Fin.eq_dec pc' v, M.add acc t)
    | step_noswap_nop : forall inp pc' v acc t,
        nth inp pc' = (nop, t) ->
        set_In pc' v ->
        step_noswap inp (weaken_one pc', v, acc) (FS pc', set_remove Fin.eq_dec pc' v, acc)
    | step_noswap_jmp : forall inp pc' pc'' v acc t,
        nth inp pc' = (jmp, t) ->
        set_In pc' v ->
        valid_jump_t pc' t = Some pc'' ->
        step_noswap inp (weaken_one pc', v, acc) (pc'', set_remove Fin.eq_dec pc' v, acc).

  Inductive done {n} : input n -> state n -> Prop :=
    | done_prog : forall inp v acc, done inp (nat_to_fin n, v, acc).

  Inductive stuck {n} : input n -> state n -> Prop :=
    | stuck_prog : forall inp pc' v acc,
        ~ set_In pc' v -> stuck inp (weaken_one pc', v, acc).

  Inductive run_noswap {n} : input n -> state n -> state n -> Prop :=
    | run_noswap_ok : forall inp st, done inp st -> run_noswap inp st st
    | run_noswap_fail : forall inp st, stuck inp st -> run_noswap inp st st
    | run_noswap_trans : forall inp st st' st'',
        step_noswap inp st st' -> run_noswap inp st' st'' -> run_noswap inp st st''.

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

    (* If the current address, which is not the end of the array, is
       present in the "allowed" set, the program can continue. *)
    Lemma step_if_possible : forall pcs v acc,
      set_In pcs v ->
      exists pc' acc', step_noswap inp (weaken_one pcs, v, acc) (pc', set_remove Fin.eq_dec pcs v, acc').
    Proof.
      intros pcs v acc Hin.
      remember (nth inp pcs) as instr. destruct instr as [op t]. destruct op.
      + exists (FS pcs). exists (M.add acc t). apply step_noswap_add; auto.
      + exists (FS pcs). exists acc. apply step_noswap_nop with t; auto.
      + unfold valid_input in Hv. specialize (Hv pcs).
        rewrite <- Heqinstr in Hv. inversion Hv; subst.
        exists f'. exists acc. apply step_noswap_jmp with t; auto.
    Qed.

    (* A program is either done, stuck (at an invalid/visited address), or can step. *)
    Theorem valid_input_progress : forall pc v acc,
      (pc = nat_to_fin n /\ done inp (pc, v, acc)) \/
      (exists pcs, pc = weaken_one pcs /\
        ((~ set_In pcs v /\ stuck inp (pc, v, acc)) \/
         (exists pc' acc', set_In pcs v /\
         step_noswap inp (pc, v, acc) (pc', set_remove Fin.eq_dec pcs v, acc')))).
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
        destruct (step_if_possible pcs v acc) as [pc' [acc' Hstep]]; auto.
        exists pc'. exists acc'. split; auto.
      - (* It is not. *)
        left. split; auto. apply stuck_prog; auto.
    Qed.

    (* A valid input always terminates, either by getting to the end of the program,
       or by looping and thus getting stuck. *)
    Program Fixpoint valid_input_terminates (pc : fin (S n)) (v : set (fin n)) (acc : t) (Hnd : List.NoDup v)
      { measure (length v) }:
      (exists pc', run_noswap inp (pc, v, acc) pc') :=
      match valid_input_progress pc v acc with
      | or_introl (conj Heq Hdone) =>
          inhabited_sig_to_exists 
            (inhabits
              (@exist (state n)
                (fun x => run_noswap inp (pc, v, acc) x) (pc, v, acc) (run_noswap_ok _ _ Hdone)))
      | or_intror (ex_intro _ pcs (conj Hw w)) =>
          match w with
          | or_introl (conj Hnin Hstuck) =>
              inhabited_sig_to_exists
                (inhabits
                  (@exist (state n)
                    (fun x => run_noswap inp (pc, v, acc) x) (pc, v, acc) (run_noswap_fail _ _ Hstuck)))
          | or_intror (ex_intro _ pc' (ex_intro _ acc' (conj Hin Hst))) =>
              match valid_input_terminates pc' (set_remove Fin.eq_dec pcs v) acc' (set_remove_nodup Fin.eq_dec pcs Hnd) with
              | ex_intro _ pc'' Hrun =>
                  inhabited_sig_to_exists
                    (inhabits
                      (@exist (state n)
                        (fun x => run_noswap inp (pc, v, acc) x) pc''
                          (run_noswap_trans _ _ (pc', set_remove Fin.eq_dec pcs v, acc') _ Hst Hrun)))
              end
          end
      end.
    Obligation 1. 
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
  End ValidInput.
End DayEight.
