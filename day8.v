Require Import Coq.ZArith.Int.
Require Import Coq.Lists.ListSet.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Vectors.Fin.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

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

  Fixpoint weaken_one {n} (f : fin n) : fin (S n) :=
    match f with
    | F1 => F1
    | FS f' => FS (weaken_one f')
    end.

  (* One modification: we really want to use 'allowed' addresses,
     a set that shrinks as the program continues, rather than 'visited'
     addresses, a set that increases as the program continues. *)
  Inductive step_noswap {n} : input n -> state n -> state n -> Prop :=
    | step_noswap_add : forall inp pc' v acc t,
        nth inp pc' = (add, t) ->
        set_mem Fin.eq_dec pc' v = true ->
        step_noswap inp (weaken_one pc', v, acc) (FS pc', set_remove Fin.eq_dec pc' v, M.add acc t)
    | step_noswap_nop : forall inp pc' v acc t,
        nth inp pc' = (nop, t) ->
        set_mem Fin.eq_dec pc' v = true ->
        step_noswap inp (weaken_one pc', v, acc) (FS pc', set_remove Fin.eq_dec pc' v, acc)
    | step_noswap_jmp : forall inp pc' pc'' v acc t,
        nth inp pc' = (jmp, t) ->
        set_mem Fin.eq_dec pc' v = true ->
        valid_jump_t pc' t = Some pc'' ->
        step_noswap inp (weaken_one pc', v, acc) (pc'', set_remove Fin.eq_dec pc' v, acc).

  Fixpoint nat_to_fin (n : nat) : fin (S n) :=
    match n with
    | O => F1
    | S n' => FS (nat_to_fin n')
    end.

  Inductive run_noswap {n} : input n -> state n -> state n -> Prop :=
    | run_noswap_ok : forall inp v acc,
        run_noswap inp (nat_to_fin n, v, acc) (nat_to_fin n, v, acc)
    | run_noswap_fail : forall inp pc' v acc,
        set_mem Fin.eq_dec pc' v = false ->
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

  Lemma set_add_idempotent : forall {A:Type}
    (Aeq_dec : forall x y : A, { x = y } + { x <> y })
    (a : A) (s : set A), set_mem Aeq_dec a s = true -> set_add Aeq_dec a s = s.
  Proof.
    intros A Aeq_dec a s Hin.
    induction s.
    - inversion Hin.
    - simpl. simpl in Hin.
      destruct (Aeq_dec a a0).
      + reflexivity.
      + simpl. rewrite IHs; auto.
  Qed.
  
  Theorem set_add_append : forall {A:Type}
    (Aeq_dec : forall x y : A, {x = y } + { x <> y })
    (a : A) (s : set A), set_mem Aeq_dec a s = false ->
    set_add Aeq_dec a s = List.app s (List.cons a List.nil).
  Proof.
    induction s.
    - reflexivity.
    - intros Hnm. simpl in Hnm.
      destruct (Aeq_dec a a0) eqn:Heq_dec.
      + inversion Hnm.
      + simpl. rewrite Heq_dec. rewrite IHs.
        reflexivity. assumption.
  Qed.

  Lemma list_append_or_nil : forall {A:Type} (l : list A),
    l = List.nil \/ exists l' a, l = List.app l' (List.cons a List.nil).
  Proof.
    induction l.
    - left. reflexivity.
    - right. destruct IHl.
      + exists List.nil. exists a.
        rewrite H. reflexivity.
      + destruct H as [l' [a' H]].
        exists (List.cons a l'). exists a'.
        rewrite H. reflexivity.
  Qed.

  Theorem list_append_induction : forall {A:Type}
    (P : list A -> Prop),
    P List.nil -> (forall (a : A) (l : list A), P l -> P (List.app l (List.cons a (List.nil)))) ->
    forall l, P l.
  Proof. Admitted.


  Theorem set_induction : forall {A:Type}
    (Aeq_dec : forall x y : A, { x = y } + {x <> y })
    (P : set A -> Prop),
    P (@empty_set A) -> (forall (a : A) (s' : set A), P s' -> P (set_add Aeq_dec a s')) ->
    forall (s : set A), P s.
  Proof. Admitted.

  Lemma weaken_one_inj : forall n (f1 f2 : fin n),
    (weaken_one f1 = weaken_one f2 -> f1 = f2).
  Proof. 
    remember (fun {n} (a b : fin n) => weaken_one a = weaken_one b -> a = b) as P.
    (* Base case for rect2 *)
    assert (forall n, @P (S n) F1 F1).
    {rewrite HeqP. intros n Heq. reflexivity. }
    (* 'Impossible' cases for rect2. *)
    assert (forall {n} (f : fin n), P (S n) F1 (FS f)).
    {rewrite HeqP. intros n f Heq. simpl in Heq. inversion Heq. }
    assert (forall {n} (f : fin n), P (S n) (FS f) F1).
    {rewrite HeqP. intros n f Heq. simpl in Heq. inversion Heq. }
    (* Recursive case for rect2. *)
    assert (forall {n} (f g : fin n), P n f g -> P (S n) (FS f) (FS g)).
    {rewrite HeqP. intros n f g IH Heq.
      simpl in Heq. injection Heq as Heq'.
      apply inj_pair2_eq_dec in Heq'.
      - rewrite IH. reflexivity. assumption.
      - apply eq_nat_dec. }

    (* Actually apply recursion. *)
    (* This can't be _the_ way to do this. *)
    intros n.
    specialize (@Fin.rect2 P H H0 H1 H2 n) as Hind.
    rewrite HeqP in Hind. apply Hind.
  Qed.

  Lemma weaken_neq_to_fin : forall {n} (f : fin (S n)),
    nat_to_fin (S n) <> weaken_one f.
  Proof.
    apply Fin.rectS; intros n Heq.
    - inversion Heq.
    - intros IH. simpl. intros Heq'.
      injection Heq' as Hinj. apply inj_pair2_eq_dec in Hinj.
      + simpl in IH. apply IH. apply Hinj.
      + apply eq_nat_dec.
  Qed.

  Lemma add_pc_safe_step : forall {n} (inp : input n) (pc : fin (S n)) i is acc st',
    step_noswap inp (pc, is, acc) st' ->
    exists st'', step_noswap inp (pc, (set_add Fin.eq_dec i is), acc) st''.
  Proof.
    intros n inp pc' i is acc st' Hstep.
    inversion Hstep.
    - eexists. apply step_noswap_add. apply H4.
      apply set_mem_correct2. apply set_add_intro1.
      apply set_mem_correct1 with Fin.eq_dec. assumption.
    - eexists. eapply step_noswap_nop. apply H4.
      apply set_mem_correct2. apply set_add_intro1.
      apply set_mem_correct1 with Fin.eq_dec. assumption.
    - eexists. eapply step_noswap_jmp. apply H3.
      apply set_mem_correct2. apply set_add_intro1.
      apply set_mem_correct1 with Fin.eq_dec. assumption.
      apply H6.
  Qed.

  Lemma remove_pc_safe_run : forall {n} (inp : input n) i pc v acc st',
    run_noswap inp (pc, set_add Fin.eq_dec i v, acc) st' ->
    exists st'', run_noswap inp (pc, v, acc) st''.
  Proof.
    intros n inp i pc v acc st' Hr.
    dependent induction Hr.
    - eexists. eapply run_noswap_ok.
    - eexists. eapply run_noswap_fail.
      apply set_mem_complete1 in H.
      apply set_mem_complete2.
      intros Hin. apply H. apply set_add_intro. right. apply Hin.
    - inversion H; subst; destruct (set_mem Fin.eq_dec pc' v) eqn:Hm.
  Admitted.

  Lemma add_pc_safe_run : forall {n} (inp : input n) i pc v acc st',
    run_noswap inp (pc, v, acc) st' ->
    exists st'', run_noswap inp (pc, (set_add Fin.eq_dec i v), acc) st''.
  Proof.
    intros n inp i pc v acc st' Hr.
    destruct (set_mem Fin.eq_dec i v) eqn:Hm.
    (* If i is already in the set, nothing changes. *)
    rewrite set_add_idempotent.
    exists st'. assumption. assumption.
    (* Otherwise, the behavior might have changed.. *)
    destruct (fin_big_or_small pc).
    - (* If we're done, we're done no matter what. *)
      eexists. rewrite H. eapply run_noswap_ok.
    - (* The PC points somewhere inside. We tried (and maybe failed)
         to execute and instruction. The challenging part
         is that adding i may change the outcome from 'fail' to 'ok' *)
      destruct H as [pc' Heq].
      generalize dependent st'.
      induction v using (@set_induction (fin n) Fin.eq_dec);
      intros st' Hr.
      + (* Our set of valid states is nearly empty. One step,
           and it runs dry. *)
        simpl. destruct (Fin.eq_dec pc' i) eqn:Heq_dec.
        * (* The PC is the one allowed state. *)
          remember (nth inp pc') as h. destruct h. destruct o.
          { (* Addition. *)
            destruct (fin_big_or_small (FS pc')).
            - (* The additional step puts as at the end. *)
              eexists. eapply run_noswap_trans.
              + rewrite Heq. apply step_noswap_add.
                symmetry. apply Heqh. simpl. rewrite Heq_dec. reflexivity.
              + rewrite H. apply run_noswap_ok.
            - (* The additional step puts us somewhere else. *)
              destruct H as [f' H].
              eexists. eapply run_noswap_trans.
              + rewrite Heq. apply step_noswap_add.
                symmetry. apply Heqh. simpl. rewrite Heq_dec. reflexivity.
              + rewrite H. apply run_noswap_fail.
                simpl. rewrite Heq_dec. reflexivity. }
          { (* No-op *) admit. }
          { (* Jump*) admit. }
        * (* The PC is not. We're done. *)
          eexists. rewrite Heq. eapply run_noswap_fail.
          simpl. rewrite Heq_dec. reflexivity. 
      + destruct (set_mem Fin.eq_dec a v) eqn:Hm'.
        * unfold fin. rewrite (set_add_idempotent Fin.eq_dec a).

            
          { apply step_noswap_nop.
            - symmetry. apply Heqh.
            - simpl. rewrite Heq_dec. reflexivity. }

      (*
      dependent induction Hr; subst.
      + (* We can't be in the OK state, since we already covered
           that earlier. *)
        destruct n. inversion pc'.
        apply weaken_neq_to_fin in Heq as [].
      + apply weaken_one_inj in Heq as Hs. subst.
        destruct (Fin.eq_dec pc'0 i) eqn:Heq_dec.
        * admit.
        * eexists. eapply run_noswap_fail.
          assert (~set_In pc'0 v).
          { apply (set_mem_complete1 Fin.eq_dec). assumption. }
          assert (~set_In pc'0 (List.cons i List.nil)).
          { simpl. intros [Heq'|[]]. apply n0. auto. }
          assert (~set_In pc'0 (set_union Fin.eq_dec v (List.cons i List.nil))).
          { intros Hin. apply set_union_iff in Hin as [Hf|Hf].
            - apply H0. apply Hf.
            - apply H1. apply Hf. }
          simpl in H2. apply set_mem_complete2. assumption.
      + apply (add_pc_safe_step _ _ i) in H as [st''' Hr'].
        eexists. eapply run_noswap_trans.
        apply Hr'. destruct st' as [[pc'' v''] acc''].
         specialize (IHHr i pc'' v'' acc'').*)


    (*    intros n inp i pc v.
    generalize dependent i.
    generalize dependent pc.
    induction v; intros pc i acc st Hr.
    - inversion Hr; subst.
      + eexists. apply run_noswap_ok.
      + destruct (Fin.eq_dec pc' i) eqn:Heq_dec.
        * admit.
        * eexists. apply run_noswap_fail.
          simpl. rewrite Heq_dec. reflexivity.
      + inversion H; subst; simpl in H7; inversion H7.
    - inversion Hr; subst.
      + eexists. apply run_noswap_ok.
      + destruct (Fin.eq_dec pc' i) eqn:Heq_dec.
        * admit.
        * eexists. apply run_noswap_fail.
          simpl. rewrite Heq_dec. simpl in H4.
          apply H4.
      + 
       destruct (nth inp pc') as [op t]. *)

  Admitted.
   
  Theorem valid_input_terminates  : forall n (inp : input n) st,
    valid_input inp -> exists st', run_noswap inp st st'.
  Proof.
    intros n inp st.
    destruct st as [[pc is] acc].
    generalize dependent inp.
    generalize dependent pc.
    generalize dependent acc.
    induction is using (@set_induction (fin n) Fin.eq_dec); intros acc pc inp Hv;
    (* The PC may point past the end of the
       array, or it may not. *)
    destruct (fin_big_or_small pc);
    (* No matter what, if it's past the end
       of the array, we're done, *)
    try (eexists (pc, _, acc); rewrite H; apply run_noswap_ok).
    - (* It's not past the end of the array,
         and the 'allowed' list is empty.
         Evaluation fails. *)
      destruct H as [f' Heq].
      exists (pc, Datatypes.nil, acc).
      rewrite Heq. apply run_noswap_fail. reflexivity.
    - (* We're not past the end of the array. However,
         adding a new valid index still guarantees
         evaluation terminates. *)
      specialize (IHis acc pc inp Hv) as [st' Hr].
      apply add_pc_safe_run with st'. assumption.
  Qed.

  (*
      (* It's not past the end of the array,
         and we're in the inductive case on is. *)
      destruct H as [pc' Heq].
      destruct (Fin.eq_dec pc' a) eqn:Heq_dec.
      + (* This PC is allowed. *)
        (* That must mean we have a non-empty list. *)
        remember (nth inp pc') as h. destruct h as [op t].
        (* Unfortunately, we can't do eexists at the top
           level, since that will mean the final state
           has to be the same for every op. *)
        destruct op.
        (* Addition. *)
        { destruct (IHis (M.add acc t) (FS pc') inp Hv) as [st' Htrans].
          eexists. eapply run_noswap_trans.
          rewrite Heq. apply step_noswap_add.
          - symmetry. apply Heqh.
          - simpl. rewrite Heq_dec. reflexivity.
          - simpl. rewrite Heq_dec. apply Htrans. }
        (* No-ops *)
        { destruct (IHis acc (FS pc') inp Hv) as [st' Htrans].
          eexists. eapply run_noswap_trans.
          rewrite Heq. apply step_noswap_nop with t.
          - symmetry. apply Heqh.
          - simpl. rewrite Heq_dec. reflexivity. 
          - simpl. rewrite Heq_dec. apply Htrans. }
        (* Jump. *) 
        { (* A little more interesting. We need to know that the jump is valid. *)
          assert (Hv' : valid_inst (jmp, t) pc').
          { specialize (Hv pc'). rewrite <- Heqh in Hv. assumption. }
          inversion Hv'.
          (* Now, proceed as usual. *)
          destruct (IHis acc f' inp Hv) as [st' Htrans].
          eexists. eapply run_noswap_trans.
          rewrite Heq. apply step_noswap_jmp with t.
          - symmetry. apply Heqh.
          - simpl. rewrite Heq_dec. reflexivity. 
          - apply H0.
          - simpl. rewrite Heq_dec. apply Htrans. }
      + (* The top PC is not allowed. *)
        specialize (IHis acc pc inp Hv) as [st' Hr].
     apply add_pc_safe_run with st'. assumption. *)
  Qed.


    (* Stoppped here. *)
  Admitted.
End DayEight.
