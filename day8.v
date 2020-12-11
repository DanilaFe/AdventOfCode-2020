Require Import Coq.ZArith.Int.
Require Import Coq.Lists.ListSet.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Vectors.Fin.

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

  Definition state n : Type := (fin (S n) * set (fin n) * t).

  (* An instruction is a pair of an opcode and an argument. *)
  Definition inst : Type := (opcode * t).
  (* An input is a bounded list of instructions. *)
  Definition input (n : nat) := VectorDef.t inst n.
  (* 'indices' represents the list of instruction
     addresses, which are used for calculating jumps. *)
  Definition indices (n : nat) := VectorDef.t (fin n) n.

  (* Compute the destination jump index, an integer. *)
  Definition jump_t {n} (pc : fin n) (off : t) : t :=
    M.add (nat_to_t (proj1_sig (to_nat pc))) off.

  (* Compute a destination index that's valid.
     Not all inputs are valid, so this may fail. *)
  Definition valid_jump_t {n} (pc : fin n) (off : t) : option (fin (S n)) := @clamp (S n) (jump_t pc off).

  Definition weaken_one {n} (f : fin n) : fin (S n).
  Proof.
    apply (@cast (n + 1)).
    + apply L. apply f.
    + rewrite <- plus_n_Sm. rewrite <- plus_n_O. reflexivity.
  Defined.

  Inductive step_noswap {n} : input n -> state n -> state n -> Prop :=
    | step_noswap_acc : forall inp pc' v acc t,
        nth inp pc' = (add, t) ->
        ~ set_mem Fin.eq_dec pc' v = true ->
        step_noswap inp (weaken_one pc', v, acc) (FS pc', set_add Fin.eq_dec pc' v, M.add acc t)
    | step_noswap_nop : forall inp pc' v acc t,
        nth inp pc' = (nop, t) ->
        ~ set_mem Fin.eq_dec pc' v = true ->
        step_noswap inp (weaken_one pc', v, acc) (FS pc', set_add Fin.eq_dec pc' v, acc)
    | step_noswap_jmp : forall inp pc' pc'' v acc t,
        nth inp pc' = (jmp, t) ->
        ~ set_mem Fin.eq_dec pc' v = true ->
        valid_jump_t pc' t = Some pc'' ->
        step_noswap inp (weaken_one pc', v, acc) (pc'', set_add Fin.eq_dec pc' v, acc).

  Fixpoint nat_to_fin (n : nat) : fin (S n) :=
    match n with
    | O => F1
    | S n' => FS (nat_to_fin n')
    end.

  Inductive run_noswap {n} : input n -> state n -> state n -> Prop :=
    | run_noswap_ok : forall inp v acc,
        run_noswap inp (nat_to_fin n, v, acc) (nat_to_fin n, v, acc)
    | run_noswap_fail : forall inp pc' v acc,
        set_mem Fin.eq_dec pc' v = true ->
        run_noswap inp (weaken_one pc', v, acc) (weaken_one pc', v, acc)
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

  Theorem valid_input_terminates  : forall n (inp : input n) st,
    valid_input inp -> exists st', run_noswap inp st st'.
  Proof.
    (* Stoppped here. *)
  Admitted.
End DayEight.
