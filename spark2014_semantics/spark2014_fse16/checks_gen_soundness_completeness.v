(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)
Require Export semantics_flagged.
Require Export checks_generator.
Require Export CpdtTactics.

(** * Helper Lemmas *)

Lemma overflow_check_OK_exist_int: forall v v',
  overflowCheck v (OK v') ->
    v' = Int v.
Proof.
  intros.
  remember (OK v') as x.
  inversion H; smack.
Qed.

Ltac apply_overflow_check_OK_exist_int :=
  match goal with
  | [H: overflowCheck ?v (OK ?v') |- _] => 
    specialize (overflow_check_OK_exist_int _ _ H); 
    let HZ := fresh "HZ" in intros HZ
  end.
 
Lemma binop_overflow_check_soundness: forall op v1 v2 v3,
  op = Plus \/ op = Minus \/ op = Multiply ->
    do_run_time_check_on_binop op v1 v2 v3 -> 
      evalBinOpRTS (OverflowCheck :: nil) op v1 v2 v3.
Proof.
  intros;
  match goal with
  | [H: do_run_time_check_on_binop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: overflowCheck ?v ?v' |- _] => destruct v'
  end;
  match goal with
  | [H: overflowCheck ?v ?v' |- _] => inversion H; smack
  end;
  repeat progress match goal with
    | [|- evalBinOpRTS _ _ _ _ _ ] => econstructor; smack
    | [|- evalBinOpRT  _ _ _ _ _ ] => econstructor; smack
  end.
Qed.

Ltac apply_binop_overflow_check_soundness :=
  match goal with
  | [H1: ?op = Plus \/ ?op = Minus \/ ?op = Multiply,
     H2: do_run_time_check_on_binop ?op ?v1 ?v2 ?v3 |- _ ] =>
      specialize (binop_overflow_check_soundness _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma binop_flagged_overflow_check_soundness: forall op v1 v2 v3,
  op = Plus \/ op = Minus \/ op = Multiply -> 
    evalBinOpRTS (OverflowCheck :: nil) op v1 v2 v3 ->
      do_run_time_check_on_binop op v1 v2 v3.
Proof.
  intros.
  repeat progress match goal with
    | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; clear H; smack
    | [H: evalBinOpRT  _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: overflowCheck ?v1 (RTE _) |- do_run_time_check_on_binop _ _ _ (RTE _)] =>
      apply DoCheckOnBinops with (v:=v1); auto
  | [H: overflowCheck ?v1 (OK _) |- do_run_time_check_on_binop _ _ _ (OK _)] =>
      apply DoCheckOnBinops with (v:=v1); smack;
      apply_overflow_check_OK_exist_int; smack
  end.
Qed.

Ltac apply_binop_flagged_overflow_check_soundness := 
  match goal with
  | [H1: ?op = Plus \/ ?op = Minus \/ ?op = Multiply,
     H2: evalBinOpRTS (OverflowCheck :: nil) ?op ?v1 ?v2 ?v3 |- _ ] =>
      specialize (binop_flagged_overflow_check_soundness _ _ _ _ H1 H2); 
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma binop_overflow_division_check_soundness: forall v1 v2 v3,
    do_run_time_check_on_binop Divide v1 v2 v3 -> 
      evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide v1 v2 v3.
Proof.
  intros;
  match goal with
  | [H: do_run_time_check_on_binop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: divCheck _ _ _ (OK ?v1), H2: overflowCheck _ ?v2 |- _] => 
      destruct v2; apply ChecksBinOp with (v:= v1)
  | _ => idtac
  end;
  repeat progress match goal with
    | [|- evalBinOpRTS _ _ _ _ _ ] => econstructor; smack
    | [|- evalBinOpRT  _ _ _ _ _ ] => econstructor; smack
  end;
  match goal with
  | [H1: divCheck _ _ _ _, H2: overflowCheck _ _ |- _] => 
      inversion H1; smack; inversion H2; smack
  end.
Qed.

Ltac apply_binop_overflow_division_check_soundness :=
  match goal with
  | [H: do_run_time_check_on_binop Divide ?v1 ?v2 ?v3 |- _] => 
      specialize (binop_overflow_division_check_soundness _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma binop_flagged_overflow_division_check_soundness: forall v1 v2 v3,
    evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide v1 v2 v3 ->
      do_run_time_check_on_binop Divide v1 v2 v3.
Proof.
  intros;
  repeat progress match goal with
    | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; clear H; smack
    | [H: evalBinOpRT  _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
    | [H: divCheck _ _ _ _ |- _] => inversion H; smack
  end.
  constructor; auto.
  apply DoCheckOnDivide with (v:=(Z.quot v0 v3)); auto.
  apply DoCheckOnDivide with (v:=(Z.quot v0 v3)); auto;
  match goal with
    | [H: overflowCheck _ _ |- _] => inversion H; smack
  end.
Qed.

Ltac apply_binop_flagged_overflow_division_check_soundness :=
  match goal with
  | [H: evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide ?v1 ?v2 ?v3 |- _] =>
      specialize (binop_flagged_overflow_division_check_soundness _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma binop_division_check_soundness: forall v1 v2 v3,
    do_run_time_check_on_binop Modulus v1 v2 v3 -> 
      evalBinOpRTS (DivCheck :: nil) Modulus v1 v2 v3.
Proof.
  intros;
  match goal with
  | [H: do_run_time_check_on_binop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: divCheck _ ?v1 ?v2 ?v3 |- _] => destruct v3
  end;
  match goal with
  | [H: divCheck _ _ _ _ |- _] => inversion H; smack
  end;
  repeat progress match goal with
    | [|- evalBinOpRTS _ _ _ _ _ ] => econstructor; smack
    | [|- evalBinOpRT  _ _ _ _ _ ] => econstructor; smack
  end.
Qed.

Ltac apply_binop_division_check_soundness :=
  match goal with
  | [H: do_run_time_check_on_binop Modulus ?v1 ?v2 ?v3 |- _] => 
      specialize (binop_division_check_soundness _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.
  
Lemma binop_flagged_division_check_soundness: forall v1 v2 v3,
    evalBinOpRTS (DivCheck :: nil) Modulus v1 v2 v3 ->
      do_run_time_check_on_binop Modulus v1 v2 v3.
Proof.
  intros;
  repeat progress match goal with
    | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; clear H; smack
    | [H: evalBinOpRT  _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
    | [H: divCheck _ _ _ _ |- _] => inversion H; smack
  end;
  apply DoCheckOnModulus; auto.
Qed.

Ltac apply_binop_flagged_division_check_soundness :=
  match goal with
  | [H: evalBinOpRTS (DivCheck :: nil) Modulus ?v1 ?v2 ?v3 |- _] =>
      specialize (binop_flagged_division_check_soundness _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma binop_no_check_soundness: forall op v1 v2 v3,
  op <> Plus /\ op <> Minus /\ op <> Multiply /\ op <> Divide /\ op <> Modulus ->
    do_run_time_check_on_binop op v1 v2 v3 -> 
      evalBinOpRTS nil op v1 v2 v3.
Proof.
  intros;
  match goal with
    | [H: do_run_time_check_on_binop _ _ _ _ |- _] => 
        inversion H; clear H; smack
  end;
  constructor; auto.
Qed.

Ltac apply_binop_no_check_soundness :=
  match goal with
  | [H1: ?op <> Plus /\ ?op <> Minus /\ ?op <> Multiply /\ ?op <> Divide /\ ?op <> Modulus,
     H2: do_run_time_check_on_binop ?op ?v1 ?v2 ?v3 |- _] =>
      specialize (binop_no_check_soundness _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma binop_no_check_flagged_soundness: forall op v1 v2 v3,
  op <> Plus /\ op <> Minus /\ op <> Multiply /\ op <> Divide /\ op <> Modulus ->
    evalBinOpRTS nil op v1 v2 v3 -> 
      do_run_time_check_on_binop op v1 v2 v3.
Proof.
  intros;
  inversion H0; subst;
  constructor; smack.
Qed.

Ltac apply_binop_no_check_flagged_soundness :=
  match goal with
  | [H1: ?op <> Plus /\ ?op <> Minus /\ ?op <> Multiply /\ ?op <> Divide /\ ?op <> Modulus,
     H2: evalBinOpRTS nil ?op ?v1 ?v2 ?v3 |- _] => 
      specialize (binop_no_check_flagged_soundness _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma unop_overflow_check_soundness: forall v v',
    do_run_time_check_on_unop Unary_Minus v v' -> 
      evalUnOpRTS (OverflowCheck :: nil) Unary_Minus v v'.
Proof.
  intros;
  destruct v';
  repeat progress match goal with
    | [H: do_run_time_check_on_unop _ _ _ |- _] => inversion H; clear H; smack
    | [|- evalUnOpRTS _ _ _ _] => econstructor; smack
    | [|- evalUnOpRT  _ _ _ _] => econstructor; smack 
    end;
  match goal with
  | [H: overflowCheck _ _ |- _] => inversion H; smack
  end.
Qed.

Ltac apply_unop_overflow_check_soundness :=
  match goal with
  | [H: do_run_time_check_on_unop Unary_Minus ?v ?v' |- _] => 
      specialize (unop_overflow_check_soundness _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma unop_flagged_overflow_check_soundness: forall v v',
    evalUnOpRTS (OverflowCheck :: nil) Unary_Minus v v' -> 
      do_run_time_check_on_unop Unary_Minus v v'.
Proof.
  intros;
  inversion H;
  repeat progress match goal with
    | [H: evalUnOpRTS _ _ _ _ |- _] => inversion H; clear H; subst
    | [H: evalUnOpRT  _ _ _ _ |- _] => inversion H; clear H; subst
    end.
  apply DoCheckOnUnary_Minus with (v':=v'); smack.
  apply DoCheckOnUnary_Minus with (v':=v'3); smack;
  apply_overflow_check_OK_exist_int; smack.
Qed.

Ltac apply_unop_flagged_overflow_check_soundness :=
  match goal with
  | [H: evalUnOpRTS (OverflowCheck :: nil) Unary_Minus ?v ?v' |- _] =>
      specialize (unop_flagged_overflow_check_soundness _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.
  
Lemma unop_no_check_soundness: forall op v v',
  op <> Unary_Minus ->
    do_run_time_check_on_unop op v v' -> 
      evalUnOpRTS nil op v v'.
Proof.
  intros;
  repeat progress match goal with
  | [H: do_run_time_check_on_unop _ _ _ |- _] => inversion H; clear H; smack
  | [|- evalUnOpRTS _ _ _ _] => constructor; smack
  end.  
Qed.

Ltac apply_unop_no_check_soundness :=
  match goal with
  | [H1: ?op <> Unary_Minus,
     H2: do_run_time_check_on_unop ?op ?v ?v' |- _] =>
      specialize (unop_no_check_soundness _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end. 
  
Lemma unop_no_check_flagged_soundness: forall op v v',
  op <> Unary_Minus ->
    evalUnOpRTS nil op v v' -> 
      do_run_time_check_on_unop op v v'.
Proof.
  intros;
  inversion H0; subst;
  constructor; auto.
Qed.

Ltac apply_unop_no_check_flagged_soundness :=
  match goal with
  | [H1: ?op <> Unary_Minus,
     H2: evalUnOpRTS nil ?op ?v ?v' |- _] =>
      specialize (unop_no_check_flagged_soundness _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.
  
(*********************************************)
(*********************************************)

Scheme expression_ind := Induction for exp Sort Prop 
                         with name_ind := Induction for name Sort Prop.

(** * Completeness of GEN-RT for Expression *)

Lemma expression_checks_completeness: forall e e' st st' s v,
  evalExp st s e v ->
    toExpRT st e e' ->
      toSymTabRT st st' ->
        evalExpRT st' s e' v.
Proof.
  apply (expression_ind
    (fun e: exp => forall (e' : expRT) (st: symTab) (st': symTabRT) (s : STACK.state) (v: Ret value),
      evalExp st s e v ->
      toExpRT st e e' ->
      toSymTabRT st st' ->
      evalExpRT st' s e' v)
    (fun n: name => forall (n': nameRT) (st: symTab) (st': symTabRT) (s : STACK.state) (v: Ret value),
      evalName st s n v ->
      toNameRT st n n' ->
      toSymTabRT st st' ->
      evalNameRT st' s n' v)
    ); smack.
  - (* 1 *)
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExp _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto;
  repeat progress  match goal with
    | [H: evalLiteral _ _ |- _] => inversion H; clear H; smack
    | [H: overflowCheck _ _ |- _] => inversion H; clear H; smack
    end;
  repeat progress match goal with
    | [|- evalLiteralRT _ _ _] => constructor
    | [|- overflowChecks _ _ _] => constructor
    | [|- overflowCheck _ _] => constructor; smack
    end;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
  - (* 2 *)
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExp _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  specialize (H _ _ _ _ _ H8 H7 H2);
  constructor; auto.
  - (* 3 *) 
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExp _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  repeat progress match goal with
  | [H1: forall (e' : expRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalExp _ _ ?e _ ->
      toExpRT _ ?e _ ->
      toSymTabRT _ _ -> evalExpRT _ _ _ _,
     H2: evalExp _ _ ?e _,
     H3: toExpRT _ ?e _,
     H4: toSymTabRT _ _ |- _] =>
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  match goal with
  | [H: evalExp _ _ e (RTE _) |- _] => 
      constructor; auto
  | [H1: evalExp _ _ e (OK _), 
     H2: evalExp _ _ e0 (RTE _) |- _] =>
      apply EvalBinOpRTE2_RTE with (v1 := v1); auto
  | [H1: evalExp _ _ e (OK _), 
     H2: evalExp _ _ e0 (OK _),
     H3: do_run_time_check_on_binop _ _ _ _ |- _] =>
      apply EvalBinOpRT with (v1 := v1) (v2 := v2); auto
  | _ => idtac
  end;
  try (apply binop_overflow_check_soundness; auto);
  match goal with
  | [H: do_run_time_check_on_binop Divide _ _ _ |- _] => 
      apply binop_overflow_division_check_soundness; smack
  | [H: do_run_time_check_on_binop Modulus _ _ _ |- _] => 
      apply binop_division_check_soundness; smack
  | _ => idtac
  end;
  match goal with
  | [H1: ?op = Plus -> False,
     H2: do_run_time_check_on_binop ?op _ _ _ |- _] =>
      apply binop_no_check_soundness; smack
  end.
  - (* 4 *)
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExp _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (e' : expRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalExp _ _ ?e _ ->
      toExpRT _ ?e _ ->
      toSymTabRT _ _ -> evalExpRT _ _ _ _,
     H2: evalExp _ _ ?e _,
     H3: toExpRT _ ?e _,
     H4: toSymTabRT _ _ |- _] =>
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  match goal with
  | [H: evalExpRT _ ?s ?e' (RTE _) |- 
       evalExpRT _ ?s (UnOpRT _ Unary_Minus ?e' _ _) (RTE _)] =>
      apply EvalUnOpRT_RTE; auto
  | [H: do_run_time_check_on_unop Unary_Minus _ _ |- _] =>
      apply EvalUnOpRT with (v := v0); auto;
      apply unop_overflow_check_soundness; auto
  | [H1: ?op = Unary_Minus -> False,
     H2: evalExp _ _ ?e (RTE _) |- _] => 
      apply EvalUnOpRT_RTE; auto
  | [H1: ?op = Unary_Minus -> False,
     H2: evalExp _ _ ?e (OK _) |- _] => 
      apply EvalUnOpRT with (v := v0); auto;
      apply unop_no_check_soundness; smack
  end.
  - (* 5 *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalName _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto.
  - (* 6 *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalName _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalName _ _ ?n _ ->
      toNameRT _ ?n _ ->
      toSymTabRT _ _ -> evalNameRT _ _ _ _,
     H2: evalName _ _ ?n _,
     H3: toNameRT _ ?n _,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  try
  match goal with
  | [H1: forall (e' : expRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalExp _ _ ?e _ ->
      toExpRT _ ?e _ ->
      toSymTabRT _ _ -> evalExpRT _ _ _ _,
     H2: evalExp _ _ ?e _,
     H3: toExpRT _ ?e _,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end.
  + apply EvalIndexedComponentRTX_RTE; auto.
  + apply EvalIndexedComponentRTE_RTE with (a:=a0); auto. 
    apply eval_exp_ex_cks_added; auto.
  + apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H10);
    specialize (symbol_table_exp_type_eq _ _ (name_astnum n) H3); smack.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.    
  + apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H10);
    specialize (symbol_table_exp_type_eq _ _ (name_astnum n) H3); smack.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.
  - (* 7 *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalName _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalName _ _ ?n _ ->
      toNameRT _ ?n _ ->
      toSymTabRT _ _ -> evalNameRT _ _ _ _,
     H2: evalName _ _ ?n _,
     H3: toNameRT _ ?n _,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  [ apply EvalSelectedComponentRTX_RTE; auto |
    apply EvalSelectedComponentRT with (r := r); auto
  ].
Qed.

Ltac apply_expression_checks_completeness :=
  match goal with
  | [H1: evalExp ?st ?s ?e ?v,
     H2: toExpRT ?st ?e ?e',
     H3: toSymTabRT ?st ?st' |- _ ] => 
      specialize (expression_checks_completeness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.

Scheme expression_x_ind := Induction for expRT Sort Prop 
                         with name_x_ind := Induction for nameRT Sort Prop.

(** * Soundess of GEN-RT for Expression *)

Lemma expression_checks_soundness: forall e e' st st' s v,
  evalExpRT st' s e' v ->
    toExpRT st e e' ->
      toSymTabRT st st' ->
        evalExp st s e v.
Proof.
  apply (expression_ind
    (fun e: exp => forall (e' : expRT) (st: symTab) (st': symTabRT) (s : STACK.state) (v: Ret value),
      evalExpRT st' s e' v ->
      toExpRT st e e' ->
      toSymTabRT st st' ->
      evalExp st s e v)
    (fun n: name => forall (n': nameRT) (st: symTab) (st': symTabRT) (s : STACK.state) (v: Ret value),
      evalNameRT st' s n' v ->
      toNameRT st n n' ->
      toSymTabRT st st' ->
      evalName st s n v)
    ); smack.
  - (* 1. E_Literal *)
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExpRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto;
  repeat progress  match goal with
    | [H: evalLiteralRT _ _ _ |- _] => inversion H; clear H; smack
    | [H: overflowChecks _ _ _ |- _] => inversion H; clear H; smack
    | [H: overflowCheck _ _ |- _] => inversion H; clear H; smack
    end;
  repeat progress match goal with
    | [|- evalLiteral _ _] => constructor
    | [|- overflowCheck _ _] => constructor; smack
    end;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
  - (* 2. E_Name *)
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExpRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto;
  apply H with (n':=nRT) (st':=st'); auto.
  - (* 3. E_Binary_Operation *)
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExpRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  repeat progress match goal with
  | [H1: forall (e' : expRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalExpRT st' s e' v ->
      toExpRT st ?e e' ->
      toSymTabRT st st' -> evalExp st s ?e v,
     H2: evalExpRT _ _ ?e' _,
     H3: toExpRT _ _ ?e',
     H4: toSymTabRT _ _ |- _] =>
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  match goal with
  | [H1: evalExpRT _ _ ?e (OK _), 
     H2: evalExpRT _ _ ?e0 (RTE _) |- _] =>
      apply EvalBinOpE2_RTE with (v1 := v1); auto
  | [H1: evalExpRT _ _ ?e (OK _), 
     H2: evalExpRT _ _ ?e0 (OK _) |- _] =>
      apply EvalBinOp with (v1 := v1) (v2 := v2); auto
  | [H: evalExpRT _ _ ?e (RTE _) |- _] => 
      constructor; auto
  | _ => idtac
  end;
  match goal with
  | [ |- do_run_time_check_on_binop Divide _ _ _ ] => 
      apply binop_flagged_overflow_division_check_soundness; smack
  | [ |- do_run_time_check_on_binop Modulus _ _ _ ] => 
      apply binop_flagged_division_check_soundness; smack
  | [H: ?op = Plus -> False |- _] => apply binop_no_check_flagged_soundness; smack
  | _ => apply binop_flagged_overflow_check_soundness; smack
  end.
  - (* 4. UnOpRT *)
  match goal with
  | [H: toExpRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalExpRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (e' : expRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalExpRT st' s e' v ->
      toExpRT st ?e e' ->
      toSymTabRT st st' -> evalExp st s ?e v,
     H2: evalExpRT _ _ ?e' _,
     H3: toExpRT _ _ ?e',
     H4: toSymTabRT _ _ |- _] =>
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  match goal with
  | [H: evalExpRT _ _ ?e (RTE _) |- _] => 
      constructor; auto
  | [H1: evalExpRT _ _ ?e (OK ?v1) |- _] =>
      apply EvalUnOp with (v := v1); auto
  end;
  [ apply unop_flagged_overflow_check_soundness; auto |
    apply unop_no_check_flagged_soundness; auto 
  ].
  - (* 5. E_Identifier_X *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalNameRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto.
  - (* 6. E_Indexed_Component_X *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalNameRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) (st' : symTabRT)
        (s : STACK.state) (v : Ret value),
      evalNameRT st' s n' v ->
      toNameRT st ?n n' ->
      toSymTabRT st st' -> evalName st s ?n v,
     H2: evalNameRT _ _ ?n1 _,
     H3: toNameRT _ _ ?n1,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  try
  match goal with
  | [H1: forall (e' : expRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalExpRT st' s e' v ->
      toExpRT st ?e e' ->
      toSymTabRT st st' -> evalExp st s ?e v,
     H2: evalExpRT _ _ ?e' _,
     H3: toExpRT _ _ ?e',
     H4: toSymTabRT _ _ |- _] =>
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end.
  + apply EvalIndexedComponentX_RTE; auto.
  + apply EvalIndexedComponentE_RTE with (a:=a0); auto.
    apply H0 with (e':=eRT) (st':=st'); auto.
    eapply eval_exp_ex_cks_stripped; smack.
  + apply EvalIndexedComponent_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply H0 with (e':=eRT) (st':=st'); auto.
    eapply eval_exp_ex_cks_stripped; smack.
    rewrite (name_ast_num_eq _ _ _ H10);
    specialize (symbol_table_exp_type_eq _ _ (name_astnum_rt xRT) H3); smack.
    apply index_range_rel_backward with (st' := st'); auto.
    rewrite exp_updated_exterior_checks in H16; constructor; auto.
    repeat progress match goal with
    | [H: rangeChecks _ _ _ _ _ |- _] => inversion H; clear H; subst
    | [H: rangeCheck _ _ _ _ |- _] => inversion H; clear H; subst
    end; auto.
  + apply EvalIndexedComponent with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply H0 with (e':=eRT) (st':=st'); auto.
    eapply eval_exp_ex_cks_stripped; smack.
    rewrite (name_ast_num_eq _ _ _ H10);
    specialize (symbol_table_exp_type_eq _ _ (name_astnum_rt xRT) H3); smack.
    apply index_range_rel_backward with (st' := st'); auto.
    rewrite exp_updated_exterior_checks in H16; constructor; auto.
    repeat progress match goal with
    | [H: rangeChecks _ _ _ _ _ |- _] => inversion H; clear H; subst
    | [H: rangeCheck _ _ _ _ |- _] => inversion H; clear H; subst
    end; auto.
  - (* 7. E_Selected_Component_X *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalNameRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) (st' : symTabRT)
        (s : STACK.state) (v : Ret value),
      evalNameRT st' s n' v ->
      toNameRT st ?n n' ->
      toSymTabRT st st' -> evalName st s ?n v,
     H2: evalNameRT _ _ ?n1 _,
     H3: toNameRT _ _ ?n1,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  [ apply EvalSelectedComponentX_RTE; auto |
    apply EvalSelectedComponent with (r := r); auto
  ].
Qed.

Ltac apply_expression_checks_soundness := 
  match goal with
  | [H1: evalExpRT ?st' ?s ?e' ?v,
     H2: toExpRT ?st ?e ?e',
     H3: toSymTabRT ?st ?st' |- _] => 
      specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.


(** * Completeness of GEN-RT for Name *)
Lemma name_checks_completeness: forall n n' st st' s v,
  evalName st s n v ->
    toNameRT st n n' ->
      toSymTabRT st st' ->
        evalNameRT st' s n' v.
Proof.
  induction n; smack.
  - (* 1. E_Identifier *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalName _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto.
  - (* 2. E_Indexed_Component *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalName _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  try (apply_expression_checks_completeness; smack);
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalName _ _ ?n _ ->
      toNameRT _ ?n _ ->
      toSymTabRT _ _ -> evalNameRT _ _ _ _,
     H2: evalName _ _ ?n _,
     H3: toNameRT _ ?n _,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end.
  apply EvalIndexedComponentRTX_RTE; auto.
  apply EvalIndexedComponentRTE_RTE with (a:=a0); auto.
    apply eval_exp_ex_cks_added; auto.
  apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H8); 
      specialize (symbol_table_exp_type_eq _ _ (name_astnum n) H1); smack.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.
  apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H8);
      specialize (symbol_table_exp_type_eq _ _ (name_astnum n) H1); smack.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.
  - (* 3. E_Selected_Component *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalName _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalName _ _ ?n _ ->
      toNameRT _ ?n _ ->
      toSymTabRT _ _ -> evalNameRT _ _ _ _,
     H2: evalName _ _ ?n _,
     H3: toNameRT _ ?n _,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  [ apply EvalSelectedComponentRTX_RTE; auto |
    apply EvalSelectedComponentRT with (r := r); auto
  ].
Qed.

Ltac apply_name_checks_completeness :=
  match goal with
  | [H1: evalName ?st ?s ?n ?v, 
     H2: toNameRT ?st ?n ?n',
     H3: toSymTabRT ?st ?st' |- _] => 
      specialize (name_checks_completeness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.


(** * Soundness of GEN-RT for Name *)
Lemma name_checks_soundness: forall n n' st st' s v,
  evalNameRT st' s n' v ->
    toNameRT st n n' ->
      toSymTabRT st st' ->
        evalName st s n v.
Proof.
  induction n; smack.
  - (* 1. E_Identifier *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalNameRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto.
  - (* 2. E_Indexed_Component *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalNameRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalNameRT _ _ ?n _ ->
      toNameRT _ _ ?n ->
      toSymTabRT _ _ -> evalName _ _ _ _,
     H2: evalNameRT _ _ ?n1 _,
     H3: toNameRT _ _ ?n1,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  match goal with
  | [H1: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H1); intro HZ;
       apply_expression_checks_soundness
  | _ => idtac
  end.
  apply EvalIndexedComponentX_RTE; auto.
  apply EvalIndexedComponentE_RTE with (a:=a0); auto.
  apply EvalIndexedComponent_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    rewrite (name_ast_num_eq _ _ _ H8).
      specialize (symbol_table_exp_type_eq _ _ (name_astnum_rt xRT) H1); smack.
    apply index_range_rel_backward with (st' := st'); auto.
    rewrite exp_updated_exterior_checks in H14; constructor; auto.
    repeat progress match goal with
    | [H: rangeChecks _ _ _ _ _ |- _] => inversion H; clear H; subst
    | [H: rangeCheck _ _ _ _ |- _] => inversion H; clear H; subst
    end; auto.
  apply EvalIndexedComponent with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    rewrite (name_ast_num_eq _ _ _ H8);
      specialize (symbol_table_exp_type_eq _ _ (name_astnum_rt xRT) H1); smack.
    apply index_range_rel_backward with (st' := st'); auto.
    rewrite exp_updated_exterior_checks in H14; constructor; auto.
    repeat progress match goal with
    | [H: rangeChecks _ _ _ _ _ |- _] => inversion H; clear H; subst
    | [H: rangeCheck _ _ _ _ |- _] => inversion H; clear H; subst
    end; auto.
  - (* 3. E_Selected_Component *)
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: evalNameRT _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : nameRT) (st : symTab) 
        (st' : symTabRT) (s : STACK.state) (v : Ret value),
      evalNameRT _ _ ?n _ ->
      toNameRT _ _ ?n ->
      toSymTabRT _ _ -> evalName _ _ _ _,
     H2: evalNameRT _ _ ?n1 _,
     H3: toNameRT _ _ ?n1,
     H4: toSymTabRT _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  [ apply EvalSelectedComponentX_RTE; auto |
    apply EvalSelectedComponent with (r := r); auto
  ].
Qed.

Ltac apply_name_checks_soundness :=
  match goal with
  | [H1: evalNameRT ?st' ?s ?n' ?v,
     H2: toNameRT ?st ?n ?n',
     H3: toSymTabRT ?st ?st' |- _ ] => 
      specialize (name_checks_soundness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.


(** * Completeness of GEN-RT for Declaration *)

Lemma declaration_checks_completeness: forall st s f d f' d' st',
  evalDecl st s f d f' ->
    toDeclRT st d d' ->
      toSymTabRT st st' ->
        evalDeclRT st' s f d' f'.
Proof.
  intros st s f d f' d' st' H; revert d' st';
  induction H; intros;
  match goal with
  | [H: toDeclRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: toObjDeclRT _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range _ ?t (Range _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  try (apply_expression_checks_completeness);
  [ apply EvalDeclRT_Null |
    apply EvalDeclRT_Type |
    apply EvalDeclRT_Var_None; auto |
    apply EvalDeclRT_Var_RTE with (e:=eRT); smack |
    apply EvalDeclRT_Var_RTE with (e:=(update_exterior_checks_exp eRT (RangeCheck :: nil))); auto |
    apply EvalDeclRT_Var_NoCheck with (e:=eRT); smack |
    apply EvalDeclRT_Var_Range_RTE with (e:=(update_exterior_checks_exp eRT (RangeCheck :: nil))) 
                                           (v:=v) (l:=l) (u:=u); smack |
    apply EvalDeclRT_Var with (e:=(update_exterior_checks_exp eRT (RangeCheck :: nil))) (v:=v) (l:=l) (u:=u); smack |
    apply EvalDeclRT_Proc; auto |
    apply EvalDeclRT_Seq_E; auto |
    apply EvalDeclRT_Seq with (f':=f'); auto
  ];
  match goal with
  | [ |- evalExpRT _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- evalNameRT _ _ (update_exterior_checks_name _ _) _] => apply eval_name_ex_cks_added; auto
  | [ |- context[name_exterior_checks (update_exterior_checks_name _ _)]] => rewrite name_updated_exterior_checks; smack
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- False] => rewrite name_updated_exterior_checks in H; smack
  | [H1: toSymTabRT ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_rt ?st' ?t (RangeRT _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end;
  match goal with
  | [H: toExpRT _ _ _ |- _] => specialize (exp_exterior_checks_beq_nil _ _ _ H); smack
  end.
Qed.

(** * Soundness of GEN-RT for Declaration *)
Lemma declaration_checks_soundness: forall st s f d f' d' st',
  evalDeclRT st' s f d' f' ->
    toDeclRT st d d' ->
      toSymTabRT st st' ->
        evalDecl st s f d f'.
Proof.
  intros st s f d f' d' st' H; revert d st;
  induction H; intros;
  match goal with
  | [H: toDeclRT _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: toObjDeclRT _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range_rt _ ?t (RangeRT _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [ H: context[exp_exterior_checks (update_exterior_checks_exp _ _)] |- _] => 
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end;
  try (apply_eval_exp_ex_cks_stripped);
  try (apply_eval_name_ex_cks_stripped);
  try (apply_expression_checks_soundness);
  [ apply EvalDecl_Null |
    apply EvalDecl_Var_None; auto |
    apply EvalDecl_Var_RTE with (e:=e0); smack |
    apply EvalDecl_Var_RTE with (e:=e0); smack |
    apply EvalDecl_Var with (e:=e0); auto |
    apply EvalDecl_Var_Range_RTE with (e:=e0) (v:=v) (l:=l) (u:=u); smack;
      apply subtype_range_rel_backward with (st':=st); auto |
    apply EvalDecl_Var_Range with (e:=e0) (l:=l) (u:=u); smack;
      apply subtype_range_rel_backward with (st':=st); auto |
    apply EvalDecl_Type |
    apply EvalDecl_Proc |
    apply EvalDecl_Seq_RTE; auto |
    apply EvalDecl_Seq with (f':=f'); auto 
  ].
Qed.

Ltac apply_declaration_checks_soundness :=
  match goal with
  | [H1: evalDeclRT ?st' ?s ?f ?d' ?f',
     H2: toDeclRT ?st ?d ?d',
     H3: toSymTabRT ?st ?st' |- _] =>
      specialize (declaration_checks_soundness _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.
  
(** * Completeness of GEN-RT for Store Update *)

Lemma store_update_checks_completeness: forall st s x v s' x' st',
  storeUpdate st s x v s' ->
    toNameRT st x x' ->
      toSymTabRT st st' ->
        storeUpdateRT st' s x' v s'.
Proof.
  intros st s x;
  induction x; smack;
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; subst
  end.
- match goal with
  | [H: storeUpdate _ _ _ _ _ |- _] => inversion H; clear H; subst
  end; constructor; auto.
- match goal with
  | [H: storeUpdate _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  try (apply_name_checks_completeness; smack);
  try (apply_expression_checks_completeness; smack);
  match goal with
  | [H1: storeUpdate _ _ ?x _ _ ,
     H2: toNameRT _ ?x _ ,
     H3: toSymTabRT _ _ |- _ ] => specialize (IHx _ _ _ _ H1 H2 H3)
  | _ => idtac
  end;
  [ apply SU_Indexed_Component_xRTE_X; auto |
    apply SU_Indexed_Component_eRTE_X with (a:=a0); auto |
    apply SU_Indexed_Component_eRTE_X with (a:=a0); auto |
    apply SU_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply SU_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply SU_Indexed_Component_X with (arrObj:=ArrayV a0) (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u) (a1:=(updateIndexedComp a0 i v)); auto |
    apply SU_Indexed_Component_X with (arrObj:=Undefined) (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u) (a1:=((i, v) :: nil)); auto
  ];
  match goal with
  | [ |- evalExpRT _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H1: toSymTabRT _ _,
     H2: toNameRT ?st0 ?x ?x' |- context[fetch_exp_type_rt (name_astnum_rt ?x') _]] =>
      rewrite <- (name_ast_num_eq _ _ _ H2); 
      specialize (symbol_table_exp_type_eq _ _ (name_astnum x) H1); smack
  | [H1: toSymTabRT ?st ?st', (**)
     H2: extract_array_index_range ?st ?t (Range _ _) |- 
     extract_array_index_range_rt ?st' ?t (RangeRT _ _)] =>
       specialize (index_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end;
  match goal with
  | [|- rangeChecks _ _ _ _ _ ] => constructor; auto
  end.
- match goal with
  | [H: storeUpdate _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: evalName _ ?s ?n ?v,
     H2: toNameRT _ ?n ?n',
     H3: toSymTabRT _ _ |- _] => specialize (name_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  match goal with
  | [H1: storeUpdate _ _ ?x _ _ ,
     H2: toNameRT _ ?x _ ,
     H3: toSymTabRT _ _ |- _ ] => specialize (IHx _ _ _ _ H1 H2 H3)
  | _ => idtac
  end;
  [ apply SU_Selected_Component_xRTE_X; auto |
    apply SU_Selected_Component_X with (recObj:=(RecordV r)) (r:=r) (r1:=(updateSelectedComp r i v)); auto |
    apply SU_Selected_Component_X with (recObj:=Undefined) (r:=r) (r1:=((i, v) :: nil)); auto
  ].
Qed.

Ltac apply_store_update_checks_completeness :=
  match goal with
  | [H1: storeUpdate ?st ?s ?x ?v ?s',
     H2: toNameRT ?st ?x ?x',
     H3: toSymTabRT ?st ?st' |- _] =>
      specialize (store_update_checks_completeness _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.
  

(** * Soundness of GEN-RT for Store Update *)

Lemma store_update_checks_soundness: forall st s x v s' x' st',
  storeUpdateRT st' s x' v s' ->
    toNameRT st x x' ->
      toSymTabRT st st' ->
        storeUpdate st s x v s'.
Proof.
  intros st s x;
  induction x; smack;
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; subst
  end.
- match goal with
  | [H: storeUpdateRT _ _ _ _ _ |- _] => inversion H; clear H; subst
  end; constructor; auto.
- match goal with
  | [H: storeUpdateRT _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  try (apply_eval_exp_ex_cks_stripped);
  try (apply_name_checks_soundness; smack);
  try (apply_expression_checks_soundness; smack);
  match goal with
  | [H1: storeUpdateRT _ _ ?x _ _ ,
     H2: toNameRT _ _ ?x ,
     H3: toSymTabRT _ _ |- _ ] => specialize (IHx _ _ _ _ H1 H2 H3)
  | _ => idtac
  end;
  match goal with
  | [ H: context[exp_exterior_checks (update_exterior_checks_exp _ _)] |- _] => 
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end;
  [ apply SU_Indexed_Component_xRTE; auto |
    apply SU_Indexed_Component_eRTE with (a:=a0); auto |
    apply SU_Indexed_Component_eRTE with (a:=a0); auto |
    apply SU_Indexed_Component_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply SU_Indexed_Component_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply SU_Indexed_Component with (arrObj:=ArrayV a0) (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u) (a1:=(updateIndexedComp a0 i v)); auto |
    apply SU_Indexed_Component with (arrObj:=Undefined) (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u) (a1:=((i, v) :: nil)); auto
  ];
  solve [
    match goal with
    | [H1: toSymTabRT _ _,
       H2: toNameRT ?st0 ?x ?x' |- context[fetch_exp_type (name_astnum ?x) _]] =>
        rewrite (name_ast_num_eq _ _ _ H2); 
        specialize (symbol_table_exp_type_eq _ _ (name_astnum_rt x') H1); smack
    end |
    apply index_range_rel_backward with (st':=st'); auto
  ].
- match goal with
  | [H: storeUpdateRT _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  try (apply_name_checks_soundness; smack);
  match goal with
  | [H1: storeUpdateRT _ _ ?x _ _ ,
     H2: toNameRT _ _ ?x ,
     H3: toSymTabRT _ _ |- _ ] => specialize (IHx _ _ _ _ H1 H2 H3)
  | _ => idtac
  end;
  [ apply SU_Selected_Component_xRTE; auto |
    apply SU_Selected_Component with (recObj:=(RecordV r)) (r:=r) (r1:=(updateSelectedComp r i v)); auto |
    apply SU_Selected_Component with (recObj:=Undefined) (r:=r) (r1:=((i, v) :: nil)); auto
  ].
Qed.

Ltac apply_store_update_checks_soundness :=
  match goal with
  | [H1: storeUpdateRT ?st' ?s ?x' ?v ?s',
     H2: toNameRT ?st ?x ?x',
     H3: toSymTabRT ?st ?st' |- _ ] =>
      specialize (store_update_checks_soundness _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.

(** * Completeness of GEN-RT for Copy_In *)

Lemma copy_in_checks_completeness: forall params st s f args f' params' args' st',
  copyIn st s f params args f' ->
    toParamSpecsRT params params' ->
      toArgsRT st params args args' ->
        toSymTabRT st st' ->
          copyInRT st' s f params' args' f'.
Proof.
  induction params; smack.
- inversion H; inversion H0; inversion H1; subst;
  constructor.
- destruct args, args', params';
  match goal with 
  | [H: copyIn _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copyIn _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: copyInRT _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: toArgsRT _ _ (?a :: ?al) nil |- _] => inversion H
  | [H: toParamSpecsRT (?param :: ?params) nil |- _] => inversion H 
  | _ => idtac
  end.
  inversion H0; clear H0; subst.
  assert(HZ1: p.(parameter_nameRT) = a.(parameter_name)).
    inversion H6; smack.
  assert(HZ2: p.(parameter_mode_rt) = a.(parameter_mode)).
    inversion H6; smack.
  assert (HZ3: p.(parameter_subtype_mark_rt) = a.(parameter_subtype_mark)).
    inversion H6; smack.
  inversion H1; clear H1; subst;
  inversion H; clear H; smack;

  match goal with
  | [H1: is_range_constrainted_type (parameter_subtype_mark ?x) = false,
     H2: extract_subtype_range st (parameter_subtype_mark ?x) (Range _ _) |- _] => 
      destruct (parameter_subtype_mark x); inversion H2; smack
  | _ => idtac
  end;
  try (apply_expression_checks_completeness; smack);
  try (apply_name_checks_completeness; smack);
  match goal with
  | [H1: copyIn _ _ _ ?params ?args ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT st params ?args ?args',
     H4: toSymTabRT _ _ |- _] =>
      specialize (IHparams _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: toExpRT _ (Name _ (Identifier _ ?x)) _ |- _] => inversion H; clear H; subst
  | [H: toNameRT _ (Identifier _ ?x) _ |- _] => inversion H; clear H; subst
  | [H: evalExp _ _ (Name _ (Identifier _ ?x)) _ |- _] => inversion H; clear H; subst
  | [H: evalName _ _ (Identifier _ ?x) _ |- _] => inversion H; clear H; subst
  | _ => idtac
  end;
  [ apply CopyIn_Mode_In_eRTE_X; smack |
    apply CopyIn_Mode_In_NoRangeCheck_X with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply CopyIn_Mode_In_eRTE_X; smack |
    apply CopyIn_Mode_In_Range_RTE_X with (v:=v) (l:=l) (u:=u); smack |
    apply CopyIn_Mode_In_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack |
    apply CopyIn_Mode_Out_X with (f':=(STACK.push f (parameter_name a) Undefined)); smack |
    apply CopyIn_Mode_Out_X with (f':=(STACK.push f (parameter_name a) Undefined)); smack |
    apply CopyIn_Mode_InOut_eRTE_X; smack |
    apply CopyIn_Mode_InOut_NoRange_X with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply CopyIn_Mode_InOut_eRTE_X; smack |
    apply CopyIn_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); smack |
    apply CopyIn_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack |
    apply CopyIn_Mode_InOut_eRTE_X; smack | 
    apply CopyIn_Mode_InOut_NoRange_X with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply CopyIn_Mode_InOut_eRTE_X; smack |
    apply CopyIn_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); smack |
    apply CopyIn_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack
  ];
  match goal with
  | [ |- evalExpRT _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- evalNameRT _ _ (update_exterior_checks_name _ _) _] => apply eval_name_ex_cks_added; auto
  | [ |- context[name_exterior_checks (update_exterior_checks_name _ _)]] => rewrite name_updated_exterior_checks; smack
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- False] => rewrite name_updated_exterior_checks in H; smack
  | [H1: toSymTabRT ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_rt ?st' ?t (RangeRT _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end;
  match goal with
  | [H: toExpRT _ _ _ |- _] => specialize (exp_exterior_checks_beq_nil _ _ _ H); smack
  | [H: toNameRT _ _ _ |- _] => specialize (name_exterior_checks_beq_nil _ _ _ H); smack
  end.
  match goal with
  | [H1: List.In ?ck ?x,
     H2: ?x = nil |- _] => rewrite H2 in H1; clear - H1; smack
  end.
Qed.

Ltac apply_copy_in_checks_completeness :=
  match goal with
  | [H1: copyIn ?st ?s ?f ?params ?args ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT ?st ?params ?args ?args',
     H4: toSymTabRT ?st ?st' |- _] =>
      specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.

(** * Soundness of GEN-RT for CopyIn *)

Lemma copy_in_checks_soundness: forall params st s f args f' params' args' st',
  copyInRT st' s f params' args' f' ->
    toParamSpecsRT params params' ->
      toArgsRT st params args args' ->
        toSymTabRT st st' ->
          copyIn st s f params args f'.
Proof.
  induction params; smack.
- inversion H0; inversion H1; subst;
  inversion H; subst; constructor.
- destruct args, args', params';
  match goal with 
  | [H: copyInRT _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copyInRT _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: toArgsRT _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: toParamSpecsRT (?param :: ?params) nil |- _] => inversion H 
  | _ => idtac
  end.
  inversion H0; clear H0; subst.
  assert(HZ1: p.(parameter_nameRT) = a.(parameter_name)).
    inversion H6; smack.
  assert(HZ2: p.(parameter_mode_rt) = a.(parameter_mode)).
    inversion H6; smack.
  assert (HZ3: p.(parameter_subtype_mark_rt) = a.(parameter_subtype_mark)).
    inversion H6; smack.
  inversion H1; clear H1; subst;
  inversion H; clear H; subst; smack;
  try (rewrite HZ1 in *); try (rewrite HZ3 in *);
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range_rt _ ?t (RangeRT _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  try (apply_expression_checks_soundness; smack);
  try (apply_name_checks_soundness; smack);
  match goal with
  | [H1: copyInRT _ _ _ ?params' ?args' ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT ?st ?params ?args ?args',
     H4: toSymTabRT _ _ |- _] =>
      specialize (IHparams _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | _ => idtac
  end;
  match goal with
  | [ H: context[exp_exterior_checks (update_exterior_checks_exp _ _)] |- _] => 
      rewrite exp_updated_exterior_checks in H; smack
  | [ H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- _] => 
      rewrite name_updated_exterior_checks in H; smack
  | _ => idtac
  end;
  match goal with
  | [H1: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H1); let HZ := fresh "HZ" in intro HZ;
       apply_expression_checks_soundness
  | [H1: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
      specialize (eval_name_ex_cks_stripped _ _ _ _ _ H1); let HZ := fresh "HZ" in intro HZ;
       apply_name_checks_soundness
  | _ => idtac
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: extract_subtype_range_rt ?st' ?t (RangeRT ?l ?u) |- _] => 
      specialize (subtype_range_rel_backward _ _ _ _ _ H1 H2); 
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  [ apply CopyIn_Mode_In_eRTE; smack |
    apply CopyIn_Mode_In_NoRange with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply CopyIn_Mode_In_eRTE; smack |
    apply CopyIn_Mode_In_Range_RTE with (v:=v) (l:=l) (u:=u); smack |
    apply CopyIn_Mode_In_Range with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack |
    apply CopyIn_Mode_Out with (f':=(STACK.push f (parameter_name a) Undefined)); smack |
    apply CopyIn_Mode_Out with (f':=(STACK.push f (parameter_name a) Undefined)); smack |
    apply CopyIn_Mode_InOut_eRTE; smack |
    apply CopyIn_Mode_InOut_NoRange with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply CopyIn_Mode_InOut_eRTE; smack |
    apply CopyIn_Mode_InOut_Range_RTE with (v:=v) (l:=l) (u:=u); smack |
    apply CopyIn_Mode_InOut_Range with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack |
    apply CopyIn_Mode_InOut_eRTE; smack |
    apply CopyIn_Mode_InOut_NoRange with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply CopyIn_Mode_InOut_eRTE; smack |
    apply CopyIn_Mode_InOut_Range_RTE with (v:=v) (l:=l) (u:=u); smack |
    apply CopyIn_Mode_InOut_Range with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack
  ].
Qed.

Ltac apply_copy_in_checks_soundness :=
  match goal with
  | [H1: copyInRT ?st' ?s ?f ?params' ?args' ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT ?st ?params ?args ?args',
     H4: toSymTabRT ?st ?st' |- _] => 
      specialize (copy_in_checks_soundness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.

(** * Completeness of GEN-RT for Copy_Out *)

Lemma copy_out_checks_completeness: forall params st s f args f' params' args' st',
  copyOut st s f params args f' ->
    toParamSpecsRT params params' ->
      toArgsRT st params args args' ->
        toSymTabRT st st' ->
          copyOutRT st' s f params' args' f'.
Proof.
  induction params; smack.
- inversion H1; inversion H0; inversion H; subst;
  constructor.
- destruct args, args', params';
  match goal with 
  | [H: copyOut _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copyOut _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: copyOutRT _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: toArgsRT _ _ (?a :: ?al) nil |- _] => inversion H
  | [H: toParamSpecsRT (?param :: ?params) nil |- _] => inversion H 
  | _ => idtac
  end.
  inversion H0; clear H0; subst.
  assert(HZ1: p.(parameter_nameRT) = a.(parameter_name)).
    inversion H6; smack.
  assert(HZ2: p.(parameter_mode_rt) = a.(parameter_mode)).
    inversion H6; smack.
  assert (HZ3: p.(parameter_subtype_mark_rt) = a.(parameter_subtype_mark)).
    inversion H6; smack.

  inversion H1; clear H1; subst;
  inversion H; clear H; smack;
  match goal with
  | [H: parameter_mode ?x = In |- _] => apply CopyOut_Mode_In_X; smack
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type ?x ?st = Some _, H2: fetch_exp_type ?x ?st = Some _ |- _] =>
      rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range _ ?t (Range _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: toExpRT _ (Name _ (Identifier _ ?x)) _ |- _] => inversion H; clear H; subst
  | [H: toNameRT _ (Identifier _ ?x) _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H1: copyOut _ _ _ ?params ?args ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT st params ?args ?args',
     H4: toSymTabRT _ _ |- _] =>
      specialize (IHparams _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | _ => idtac
  end;
  try (apply_store_update_checks_completeness);
  [ apply CopyOut_Mode_Out_nRTE_X with (v:=v); smack |
    apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'); smack |
    apply CopyOut_Mode_Out_Range_RTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack |
    apply CopyOut_Mode_Out_nRTE_X with (v:=v); smack |
    apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'); smack |
    apply CopyOut_Mode_Out_nRTE_X with (v:=v); smack |
    apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'); smack |
    apply CopyOut_Mode_Out_Range_RTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack |
    apply CopyOut_Mode_Out_Range_RTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack 
  ];
  match goal with
  | [ |- context[name_exterior_checks (update_exterior_checks_name _ _)]] => rewrite name_updated_exterior_checks; smack
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- False] => rewrite name_updated_exterior_checks in H; smack
  | [H1: toNameRT _ ?n ?n', H2: List.In _ (name_exterior_checks ?n') |- False] => 
      rewrite (name_exterior_checks_beq_nil _ _ _ H1) in H2; inversion H2
  | [H1: toSymTabRT _ _ |- context[fetch_exp_type_rt ?ast_num _]] =>
      rewrite <- (symbol_table_exp_type_eq _ _ ast_num H1); auto
  | [ |- storeUpdateRT _ _ _ _ _] => apply store_update_ex_cks_added; auto
  | [H1: toSymTabRT ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_rt ?st' ?t (RangeRT _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end. 
Qed.

Ltac apply_copy_out_checks_completeness :=
  match goal with
  | [H1: copyOut ?st ?s ?f ?params ?args ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT ?st ?params ?args ?args',
     H4: toSymTabRT ?st ?st' |- _] =>
      specialize (copy_out_checks_completeness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.

(** * Soundness of GEN-RT for CopyOut *)

Lemma copy_out_checks_soundness: forall params st s f args f' params' args' st',
  copyOutRT st' s f params' args' f' ->
    toParamSpecsRT params params' ->
      toArgsRT st params args args' ->
        toSymTabRT st st' ->
          copyOut st s f params args f'.
Proof.
  induction params; smack.
- inversion H0; inversion H1; subst; inversion H;
  constructor.
- destruct args, args', params';
  match goal with 
  | [H: copyOutRT _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copyOutRT _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: toArgsRT _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: toParamSpecsRT (?param :: ?params) nil |- _] => inversion H 
  | _ => idtac
  end.
  inversion H0; clear H0; subst.
  assert(HZ1: p.(parameter_nameRT) = a.(parameter_name)).
    inversion H6; smack.
  assert(HZ2: p.(parameter_mode_rt) = a.(parameter_mode)).
    inversion H6; smack.
  assert (HZ3: p.(parameter_subtype_mark_rt) = a.(parameter_subtype_mark)).
    inversion H6; smack.

  inversion H1; clear H1; subst;
  inversion H; clear H; subst; smack;
  try (rewrite HZ1 in *); try (rewrite HZ3 in *);
  match goal with
  | [H: parameter_mode ?x = In |- _] => apply CopyOut_Mode_In; smack
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type ?x ?st = Some ?t, H2: fetch_exp_type_rt ?x ?st' = Some ?t0,
     H3: toSymTabRT ?st ?st' |- _] =>
      rewrite (symbol_table_exp_type_eq _ _ x H3) in H1;
      rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range_rt _ ?t (RangeRT _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [H1: copyOutRT ?st' ?s ?f ?params' ?args' ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT st params ?args ?args',
     H4: toSymTabRT _ _ |- _] =>
      specialize (IHparams _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | _ => idtac
  end;
  match goal with
  | [ H: context[exp_exterior_checks (update_exterior_checks_exp _ _)] |- _] => 
      rewrite exp_updated_exterior_checks in H; smack
  | [ H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- _] => 
      rewrite name_updated_exterior_checks in H; smack
  | _ => idtac
  end;
  match goal with
  | [H1: toSymTabRT _ _ |- context[fetch_exp_type ?ast_num _]] =>
      specialize (symbol_table_exp_type_eq _ _ ast_num H1); let HZ := fresh "HZ" in intro HZ 
  | _ => idtac
  end;
  try (apply_store_update_ex_cks_stripped);
  try (apply_store_update_checks_soundness);
  [ apply CopyOut_Mode_Out_nRTE with (v:=v) (t:=t); smack |
    apply CopyOut_Mode_Out_NoRange with (v:=v) (s':=s') (t:=t); smack |
    apply CopyOut_Mode_Out_Range_RTE with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_nRTE with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack |
    apply CopyOut_Mode_Out_nRTE with (v:=v) (t:=t); smack |
    apply CopyOut_Mode_Out_NoRange with (v:=v) (s':=s') (t:=t); smack |
    apply CopyOut_Mode_Out_nRTE with (v:=v) (t:=t); smack |
    apply CopyOut_Mode_Out_NoRange with (v:=v) (s':=s') (t:=t); smack |
    apply CopyOut_Mode_Out_Range_RTE with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_nRTE with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack |
    apply CopyOut_Mode_Out_Range_RTE with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range_nRTE with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply CopyOut_Mode_Out_Range with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack
  ];
  match goal with
  | [H1: toSymTabRT _ _ |- context[fetch_exp_type ?ast_num _]] =>
      rewrite (symbol_table_exp_type_eq _ _ ast_num H1); smack 
  | [H1: toSymTabRT ?st ?st',
     H2: extract_subtype_range_rt ?st' ?t (RangeRT ?l ?u) |- _] => 
      specialize (subtype_range_rel_backward _ _ _ _ _ H1 H2); 
      let HZ := fresh "HZ" in intro HZ; auto
  | _ => idtac
  end.
Qed.  

Ltac apply_copy_out_checks_soundness :=
  match goal with
  | [H1: copyOutRT ?st' ?s ?f ?params' ?args' ?f',
     H2: toParamSpecsRT ?params ?params',
     H3: toArgsRT ?st ?params ?args ?args',
     H4: toSymTabRT ?st ?st' |- _ ] =>
      specialize (copy_out_checks_soundness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.
  
(** * Completeness of GEN-RT for Assignment *)

Lemma statement_assign_checks_completeness: forall st s n x e s' stmt' st',
  evalStmt st s (Assign n x e) s' -> 
    toStmtRT st (Assign n x e) stmt' ->
      toSymTabRT st st' ->
        evalStmtRT st' s stmt' s'.
Proof.
  intros.
  inversion H0; inversion H; subst; clear H0 H;
  match goal with
  | [H1: fetch_exp_type ?x ?st = Some _,
     H2: fetch_exp_type ?x ?st = Some _ |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range _ ?t (Range _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [H1: evalExp _ ?s ?e ?v,
     H2: toExpRT _ ?e ?e',
     H3: toSymTabRT _ _ |- _] => specialize (expression_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
  | [H1: storeUpdate _ _ ?x _ _,
     H2: toNameRT _ ?x _,
     H3: toSymTabRT _ _ |- _] => specialize (store_update_checks_completeness _ _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  [ apply EvalAssignRT_RTE; auto |
    apply EvalAssignRT with (v:=v); auto |
    apply EvalAssignRT_RTE; auto |
    apply EvalAssignRT_Range_RTE with (v:=v) (t:=t0) (l:=l) (u:=u); auto |
    apply EvalAssignRT_Range with (v:=v) (t:=t0) (l:=l) (u:=u); auto
  ];
  match goal with
  | [H: toExpRT _ _ ?e' |- context[exp_exterior_checks ?e']] => specialize (exp_exterior_checks_beq_nil _ _ _ H); smack
  | [ |- evalExpRT _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H1: toSymTabRT ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_rt ?st' ?t (RangeRT _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  | [H0: toNameRT ?st0 _ ?x',
     H1: toSymTabRT _ _ |- context[fetch_exp_type_rt ?n _]] =>
      rewrite <- (symbol_table_exp_type_eq _ _ n H1); auto;
      rewrite <- (name_ast_num_eq _ _ _ H0); auto
  end.
Qed.

Ltac apply_statement_assign_checks_completeness :=
  match goal with
  | [H1: evalStmt ?st ?s (Assign ?n ?x ?e) ?s',
     H2: toStmtRT ?st (Assign ?n ?x ?e) ?stmt',
     H3: toSymTabRT ?st ?st' |- _] =>
      specialize (statement_assign_checks_completeness _ _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.

(** * Soundness of GEN-RT for Assignment *)

Lemma statement_assign_checks_soundness: forall st s n x e s' stmt' st',
  evalStmtRT st' s stmt' s' -> 
    toStmtRT st (Assign n x e) stmt' ->
      toSymTabRT st st' ->
        evalStmt st s (Assign n x e) s'.
Proof.
  intros.
  inversion H0; inversion H; subst; clear H0 H;
  match goal with
  | [H: _ = AssignRT _ _ _ |- _] => inversion H; subst
  | _ => idtac
  end;
  match goal with
  | [H: toNameRT ?st ?x ?x' |- _] =>
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ;
      try (rewrite HZ in *)
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type ?x ?st = Some ?t |- _] =>
      specialize (symbol_table_exp_type_eq _ _ x H1);
      let HZ := fresh "HZ" in intro HZ
  end;
  match goal with
  | [H1: fetch_exp_type ?x ?st =  fetch_exp_type_rt ?x' ?st',
     H2: fetch_exp_type ?x ?st = Some ?t, 
     H3: fetch_exp_type_rt ?x ?st' = Some ?t' |- _] =>
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; subst
  | _ => idtac
  end;
(*
  match goal with
  | [H0: toNameRT ?st ?x ?x',
     H1: toSymTabRT _ _,
     H2: fetch_exp_type (name_astnum ?x) st = Some ?t, 
     H3: fetch_exp_type_rt (name_astnum_rt ?x') st' = Some ?t' |- _] =>
      rewrite (name_ast_num_eq _ _ _ H0) in H2;
      rewrite (symbol_table_exp_type_eq _ _ (name_astnum_rt x') H1) in H2; auto;
      rewrite H2 in H3; inversion H3; subst
  | _ => idtac
  end;
*)
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range_rt _ ?t (RangeRT _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [ H: context[exp_exterior_checks (update_exterior_checks_exp _ _)] |- _] => 
      rewrite exp_updated_exterior_checks in H; smack
  | [ H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- _] => 
      rewrite name_updated_exterior_checks in H; smack
  | _ => idtac
  end;
  match goal with
  | [H1: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H1); let HZ := fresh "HZ" in intro HZ;
       apply_expression_checks_soundness
  | [H1: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
      specialize (eval_name_ex_cks_stripped _ _ _ _ _ H1); let HZ := fresh "HZ" in intro HZ;
       apply_name_checks_soundness
  | _ => idtac
  end;
  try (apply_expression_checks_soundness; smack);
  try (apply_store_update_checks_soundness; smack);
  [ apply EvalAssign_RTE; auto |
    apply EvalAssign with (v:=v) (t:=t); auto |
    apply EvalAssign_RTE; auto |
    apply EvalAssign_Range_RTE with (v:=v) (t:=t0) (l:=l) (u:=u); auto |
    apply EvalAssign_Range with (v:=v) (t:=t0) (l:=l) (u:=u); auto 
  ];
  match goal with
  | [H1: toSymTabRT _ _ |- context[fetch_exp_type ?n _]] =>
      rewrite (symbol_table_exp_type_eq _ _ n H1); smack 
  | [H1: toSymTabRT ?st ?st',
     H2: extract_subtype_range_rt ?st' ?t (RangeRT ?l ?u) |- _] => 
      specialize (subtype_range_rel_backward _ _ _ _ _ H1 H2); 
      let HZ := fresh "HZ" in intro HZ; auto
  | _ => idtac
  end.
Qed.

Ltac apply_statement_assign_checks_soundness :=
  match goal with
  | [H1: evalStmtRT ?st' ?s ?stmt' ?s',
     H2: toStmtRT ?st (Assign ?n ?x ?e) ?stmt',
     H3: toSymTabRT ?st ?st' |- _ ] =>
      specialize (statement_assign_checks_soundness _ _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.

(** * Completeness of GEN-RT for Statement *)

Lemma statement_checks_completeness: forall st s stmt s' stmt' st',
  evalStmt st s stmt s' -> 
    toStmtRT st stmt stmt' ->
      toSymTabRT st st' ->
        evalStmtRT st' s stmt' s'.
Proof.
  intros st s stmt s' stmt' st' H; revert stmt' st'.
  induction H; intros.
- (* S_Null *)
  inversion H; subst;
  constructor.
- (* Assign *)
  apply statement_assign_checks_completeness with (st:=st) (n:=n) (x:=x) (e:=e); smack.
  apply EvalAssign_RTE; auto.
- apply statement_assign_checks_completeness with (st:=st) (n:=n) (x:=x) (e:=e); smack.
  apply EvalAssign with (v:=v) (t:=t); auto.
- apply statement_assign_checks_completeness with (st:=st) (n:=n) (x:=x) (e:=e); smack.
  apply EvalAssign_Range_RTE with (v:=v) (t:=t) (l:=l) (u:=u); auto.
- apply statement_assign_checks_completeness with (st:=st) (n:=n) (x:=x) (e:=e); smack.
  apply EvalAssign_Range with (v:=v) (t:=t) (l:=l) (u:=u); auto.
- (* If RTE *)
  inversion H0; clear H0; subst;
  apply EvalIfRT_RTE;
  match goal with
  | [H1: evalExp _ ?s ?e ?v,
     H2: toExpRT _ ?e ?e',
     H3: toSymTabRT _ _ |- _] => 
      specialize (expression_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  end. 
- (* If True *)
  inversion H1; clear H1; subst;
  apply EvalIfRT_True.
  match goal with
  | [H1: evalExp _ ?s ?e ?v,
     H2: toExpRT _ ?e ?e',
     H3: toSymTabRT _ _ |- _] => 
      specialize (expression_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  end.
  apply IHevalStmt; smack.
- (* If False *)
  inversion H1; clear H1; subst;
  apply EvalIfRT_False; smack.
  match goal with
  | [H1: evalExp _ ?s ?e ?v,
     H2: toExpRT _ ?e ?e',
     H3: toSymTabRT _ _ |- _] => 
      specialize (expression_checks_completeness _ _ _ _ _ _ H1 H2 H3); smack
  end.
- (* While RTE *)
  inversion H0; clear H0; subst;
  apply EvalWhileRT_RTE;
  specialize (expression_checks_completeness _ _ _ _ _ _ H H7 H1); smack.
- (* While True RTE *)
  inversion H1; clear H1; subst;
  apply EvalWhileRT_True_RTE.
  specialize (expression_checks_completeness _ _ _ _ _ _ H H8 H2); smack.
  apply IHevalStmt; smack.
- (* While True *)
  inversion H2; clear H2; subst;
  apply EvalWhileRT_True with (s1:=s1).
  specialize (expression_checks_completeness _ _ _ _ _ _ H H9 H3); smack.
  apply IHevalStmt1; smack.  
  apply IHevalStmt2; smack.
  constructor; auto.
- (* While False *)
  inversion H0; clear H0; subst;
  apply EvalWhileRT_False;
  specialize (expression_checks_completeness _ _ _ _ _ _ H H7 H1); smack.
- (* Procedure Call Args RTE *)
  inversion H1; subst;
  rewrite H in H9; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H2 H); smack;
  specialize (procedure_components_rel _ _ _ H5); smack;
  apply EvalCallRT_Args_RTE with (n0:=n1) (pb:=x); smack;
  specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ _ H0 H6 H11 H2); smack.
- (* Procedure Call Decls RTE *)
  inversion H3; subst;
  rewrite H in H11; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H4 H); smack;
  specialize (procedure_components_rel _ _ _ H7); smack;
  apply EvalCallRT_Decl_RTE with (n0:=n1) (pb:=x) (f:=f) (intact_s:=intact_s) (s1:=s1); smack.
  specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ _ H0 H8 H13 H4); smack.
  specialize (declaration_checks_completeness _ _ _ _ _ _ _ H2 H5 H4); smack.
- (* Procedure Call Body RTE *)
  inversion H4; subst;
  rewrite H in H12; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H5 H); smack;
  specialize (procedure_components_rel _ _ _ H8); smack;
  apply EvalCallRT_Body_RTE with (n0:=n1) (pb:=x) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1); smack.
  specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ _ H0 H9 H14 H5); smack.
  specialize (declaration_checks_completeness _ _ _ _ _ _ _ H2 H6 H5); smack.
- (* Procedure Call *)
  inversion H7; subst;
  rewrite H in H15; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H8 H); smack;
  specialize (procedure_components_rel _ _ _ H10); smack;
  specialize (IHevalStmt _ _ H13 H8); smack.
  apply EvalCallRT with (n0:=n1) (pb:=x) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1)
                        (s2:=((n, locals_section ++ params_section) :: s3)) 
                        (locals_section:=locals_section) (params_section:=params_section) 
                        (s3:=s3); smack.
  specialize (copy_in_checks_completeness _ _ _ _ _ _ _ _ _ H0 H11 H17 H8); smack.
  specialize (declaration_checks_completeness _ _ _ _ _ _ _ H2 H4 H8); smack.
  specialize (copy_out_checks_completeness _ _ _ _ _ _ _ _ _ H6 H11 H17 H8); smack.
- (* Sequence RTE *)
  inversion H0; smack;
  apply EvalSeqRT_RTE;
  apply IHevalStmt; smack.
- (* Sequence *)
  inversion H1; smack;
  apply EvalSeqRT with (s1:=s1); smack.
Qed.

Ltac apply_statement_checks_completeness :=
  match goal with
  | [H1: evalStmt ?st ?s ?stmt ?s', 
     H2: toStmtRT ?st ?stmt ?stmt',
     H3: toSymTabRT ?st ?st' |- _ ] => 
      specialize (statement_checks_completeness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end. 

(** * Soundness of GEN-RT for Statement *)

Lemma statement_checks_soundness: forall st s stmt s' stmt' st',
  evalStmtRT st' s stmt' s' -> 
    toStmtRT st stmt stmt' ->
      toSymTabRT st st' ->
        evalStmt st s stmt s'.
Proof.
  intros st s stmt s' stmt' st' H; revert stmt st;
  induction H; intros.
- (* S_Null *)
  inversion H; subst;
  constructor.
- (* Assign *)
  match goal with
  | [H: toStmtRT ?st0 ?stmt (AssignRT _ _ _) |- _] => inversion H; subst
  end;
  match goal with
  | [H1: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H1); intro HZ
  | _ => idtac
  end;
  [ apply statement_assign_checks_soundness with (st':=st) (stmt' := (AssignRT n x e)); smack |
    apply statement_assign_checks_soundness with (st':=st) (stmt' := ((AssignRT n x
            (update_exterior_checks_exp eRT (RangeCheck :: nil))))); smack 
  ];
  apply EvalAssignRT_RTE; auto.
- (* EvalAssign_Range_RTE *)
  match goal with
  | [H: toStmtRT ?st0 ?stmt (AssignRT _ _ _) |- _] => inversion H; subst
  end;
  match goal with
  | [ H: context[exp_exterior_checks (update_exterior_checks_exp _ _)] |- _] => 
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  apply statement_assign_checks_soundness with (st':=st) (stmt' := (AssignRT n x e)); smack.
  apply EvalAssignRT with (v:=v); auto.
- (* EvalAssign_Range_RTE *)
  match goal with
  | [H: toStmtRT ?st0 ?stmt (AssignRT _ _ _) |- _] => inversion H; subst
  end.
  (* case 1: conflict *)
  match goal with
  | [H: toNameRT ?st ?x ?x' |- _] =>
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ;
      try (rewrite HZ in *)
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type ?x ?st = Some ?t |- _] =>
      specialize (symbol_table_exp_type_eq _ _ x H1);
      let HZ := fresh "HZ" in intro HZ
  end;
  match goal with
  | [H1: fetch_exp_type ?x ?st =  fetch_exp_type_rt ?x' ?st',
     H2: fetch_exp_type ?x ?st = Some ?t, 
     H3: fetch_exp_type_rt ?x ?st' = Some ?t' |- _] =>
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; subst
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range_rt _ ?t (RangeRT _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end.
  (* case 2 *)
  apply statement_assign_checks_soundness with (st':=st) (stmt' := (AssignRT n x
            (update_exterior_checks_exp eRT (RangeCheck :: nil)))); smack.
  apply EvalAssignRT_Range_RTE with (v:=v) (t:=t) (l:=l) (u:=u); auto.
- (* EvalAssign_Range *)
  match goal with
  | [H: toStmtRT ?st0 ?stmt (AssignRT _ _ _) |- _] => inversion H; subst
  end.
  (* case 1: conflict *)
  match goal with
  | [H: toNameRT ?st ?x ?x' |- _] =>
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ;
      try (rewrite HZ in *)
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type ?x ?st = Some ?t |- _] =>
      specialize (symbol_table_exp_type_eq _ _ x H1);
      let HZ := fresh "HZ" in intro HZ
  end;
  match goal with
  | [H1: fetch_exp_type ?x ?st =  fetch_exp_type_rt ?x' ?st',
     H2: fetch_exp_type ?x ?st = Some ?t, 
     H3: fetch_exp_type_rt ?x ?st' = Some ?t' |- _] =>
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; subst
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range_rt _ ?t (RangeRT _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end.
  (* case 2 *)
  apply statement_assign_checks_soundness with (st':=st) (stmt' := (AssignRT n x
            (update_exterior_checks_exp eRT (RangeCheck :: nil)))); smack.
  apply EvalAssignRT_Range with (v:=v) (t:=t) (l:=l) (u:=u); auto.
- (* If RTE *)
  inversion H0; clear H0; subst.
  apply EvalIf_RTE;
  apply_expression_checks_soundness; auto.
- (* If True *)
  inversion H1; clear H1; subst;
  apply EvalIf_True;
  apply_expression_checks_soundness; auto.
- (* If False *)
  inversion H1; clear H1; subst;
  apply EvalIf_False;
  apply_expression_checks_soundness; auto.
- (* While RTE *)
  inversion H0; clear H0; subst;
  apply EvalWhile_RTE;
  apply_expression_checks_soundness; auto.
- (* While True RTE *)
  inversion H1; clear H1; subst;
  apply EvalWhile_True_RTE;
  apply_expression_checks_soundness; auto.
- (* While True *)
  inversion H2; clear H2; subst;
  apply EvalWhile_True with (s1:=s1);
  apply_expression_checks_soundness; auto.
  specialize (IHevalStmtRT1 _ _ H10 H3).
  apply IHevalStmtRT2; smack.
  constructor; auto.
- (* While False *)
  inversion H0; clear H0; subst;
  apply EvalWhile_False;
  apply_expression_checks_soundness; auto.
- (* Procedure Call Args RTE *)
  inversion H1; subst.
  specialize (symbol_table_procedure_rel_backward _ _ _ _ _ H2 H); smack.
  match goal with
  | [H1: fetch_proc ?p ?st0 = Some _, H2: fetch_proc ?p ?st0 = Some _ |- _] =>
      rewrite H2 in H1; inversion H1; subst
  end.
  specialize (procedure_components_rel _ _ _ H5); smack.
  apply_copy_in_checks_soundness.
  apply EvalCall_Args_RTE with (n0:=n1) (pb:=pb0); smack.
- (* Procedure Call Decls RTE *)
  inversion H3; subst.
  specialize (symbol_table_procedure_rel_backward _ _ _ _ _ H4 H); smack.
  match goal with
  | [H1: fetch_proc ?p ?st0 = Some _, H2: fetch_proc ?p ?st0 = Some _ |- _] =>
      rewrite H2 in H1; inversion H1; subst
  end.
  specialize (procedure_components_rel _ _ _ H7); smack.
  apply_copy_in_checks_soundness.
  apply_declaration_checks_soundness.
  apply EvalCall_Decl_RTE with (n0:=n1) (pb:=pb0) (f:=f) (intact_s:=intact_s) (s1:=s1); smack.
- (* Procedure Call Body RTE *)
  inversion H4; subst.
  specialize (symbol_table_procedure_rel_backward _ _ _ _ _ H5 H); smack.
  match goal with
  | [H1: fetch_proc ?p ?st0 = Some _, H2: fetch_proc ?p ?st0 = Some _ |- _] =>
      rewrite H2 in H1; inversion H1; subst
  end.
  specialize (procedure_components_rel _ _ _ H8); smack.
  apply_copy_in_checks_soundness.
  apply_declaration_checks_soundness.
  apply EvalCall_Body_RTE with (n0:=n1) (pb:=pb0) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1); smack.
- (* Procedure Call *)
  inversion H7; subst.
  specialize (symbol_table_procedure_rel_backward _ _ _ _ _ H8 H); smack.
  match goal with
  | [H1: fetch_proc ?p ?st0 = Some _, H2: fetch_proc ?p ?st0 = Some _ |- _] =>
      rewrite H2 in H1; inversion H1; subst
  end.
  specialize (procedure_components_rel _ _ _ H10); smack.
  apply_copy_in_checks_soundness.
  apply_copy_out_checks_soundness.
  apply_declaration_checks_soundness.
  specialize (IHevalStmtRT _ _ H13 H8); smack;
  apply EvalCall with (n0:=n1) (pb:=pb0) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1)
                      (s2:=((n, locals_section ++ params_section) :: s3)) 
                      (locals_section:=locals_section) (params_section:=params_section) 
                      (s3:=s3); smack.
- (* Sequence RTE *)
  inversion H0; smack;
  apply EvalSeq_RTE;
  apply IHevalStmtRT; smack.
- (* Sequence *)
  inversion H1; smack;
  apply EvalSeq with (s1:=s1); smack.
Qed.

Ltac apply_statement_checks_soundness :=
  match goal with
  | [H1: evalStmtRT ?st' ?s ?stmt' ?s',
     H2: toStmtRT ?st ?stmt ?stmt',
     H3: toSymTabRT ?st ?st' |- _ ] =>
      specialize (statement_checks_soundness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intro HZ
  end.

(** * Consistency of GEN-RT Spec *)

(** ** toExpRTConsistent *)

Lemma toExpRTConsistent: forall e eRT st stRT s v,
  toExpRT st e eRT ->
    toSymTabRT st stRT ->
      (evalExpRT stRT s eRT v <-> evalExp st s e v).
Proof.
  intros;
  split; intro;
  [apply_expression_checks_soundness; auto |
   apply_expression_checks_completeness; auto 
  ].
Qed.

(** ** toNameRTConsistent *)
Lemma toNameRTConsistent: forall n nRT st stRT s v,
  toNameRT st n nRT ->
    toSymTabRT st stRT ->
      (evalNameRT stRT s nRT v <-> evalName st s n v).
Proof.
  intros;
  split; intro;
  [apply_name_checks_soundness; auto |
   apply_name_checks_completeness; auto 
  ].
Qed.

(** ** toDeclRTConsistent *)
Lemma toDeclRTConsistent: forall st s f d f' dRT stRT,
  toDeclRT st d dRT ->
    toSymTabRT st stRT ->
      (evalDeclRT stRT s f dRT f' <-> evalDecl st s f d f').
Proof.
  intros;
  split; intro;
  [eapply declaration_checks_soundness; smack |
   eapply declaration_checks_completeness; smack
  ].
Qed.

(** ** toDeclRTConsistent *)
Lemma toStmtRTConsistent: forall st s stmt s' stmtRT stRT,
  toStmtRT st stmt stmtRT ->
    toSymTabRT st stRT ->
      (evalStmtRT stRT s stmtRT s' <-> evalStmt st s stmt s').
Proof.
  intros;
  split; intro;
  [apply_statement_checks_soundness; auto |
   apply_statement_checks_completeness; auto
  ].
Qed.
