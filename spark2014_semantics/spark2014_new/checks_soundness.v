Require Export semantics_flagged.
Require Export checks_generator.
Require Export CpdtTactics.

Lemma binop_overflow_check_soundness: forall op v1 v2 v3,
  op = Plus \/ op = Minus \/ op = Multiply ->
    do_run_time_check_on_binop op v1 v2 v3 -> 
      do_flagged_checks_on_binop (Do_Overflow_Check :: nil) op v1 v2 v3.
Proof.
  intros;
  match goal with
  | [H: do_run_time_check_on_binop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: do_overflow_check ?v ?v' |- _] => destruct v'
  end;
  match goal with
  | [H: do_overflow_check ?v ?v' |- _] => inversion H; smack
  end;
  repeat progress match goal with
    | [|- do_flagged_checks_on_binop _ _ _ _ _ ] => econstructor; smack
    | [|- do_flagged_check_on_binop  _ _ _ _ _ ] => econstructor; smack
  end.
Qed.

Lemma binop_overflow_division_check_soundness: forall v1 v2 v3,
    do_run_time_check_on_binop Divide v1 v2 v3 -> 
      do_flagged_checks_on_binop (Do_Division_Check :: Do_Overflow_Check :: nil) Divide v1 v2 v3.
Proof.
  intros;
  match goal with
  | [H: do_run_time_check_on_binop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: do_division_check _ _ (Normal ?v1), H2: do_overflow_check _ ?v2 |- _] => 
      destruct v2; apply Do_Checks_Binop with (v:= v1)
  | _ => idtac
  end;
  repeat progress match goal with
    | [|- do_flagged_checks_on_binop _ _ _ _ _ ] => econstructor; smack
    | [|- do_flagged_check_on_binop  _ _ _ _ _ ] => econstructor; smack
  end;
  match goal with
  | [H1: do_division_check _ _ _, H2: do_overflow_check _ _ |- _] => 
      inversion H1; smack; inversion H2; smack
  end.
Qed.

Lemma binop_no_check_soundness: forall op v1 v2 v3,
  op <> Plus /\ op <> Minus /\ op <> Multiply /\ op <> Divide ->
    do_run_time_check_on_binop op v1 v2 v3 -> 
      do_flagged_checks_on_binop nil op v1 v2 v3.
Proof.
  intros;
  match goal with
    | [H: do_run_time_check_on_binop _ _ _ _ |- _] => 
        inversion H; clear H; smack
  end;
  constructor; auto.
Qed.

Lemma unop_overflow_check_soundness: forall v v',
    do_run_time_check_on_unop Unary_Minus v v' -> 
      do_flagged_checks_on_unop (Do_Overflow_Check :: nil) Unary_Minus v v'.
Proof.
  intros;
  destruct v';
  repeat progress match goal with
    | [H: do_run_time_check_on_unop _ _ _ |- _] => inversion H; clear H; smack
    | [|- do_flagged_checks_on_unop _ _ _ _] => econstructor; smack
    | [|- do_flagged_check_on_unop  _ _ _ _] => econstructor; smack 
    end;
  match goal with
  | [H: do_overflow_check _ _ |- _] => inversion H; smack
  end.
Qed.

Lemma unop_no_check_soundness: forall op v v',
  op <> Unary_Minus ->
    do_run_time_check_on_unop op v v' -> 
      do_flagged_checks_on_unop nil op v v'.
Proof.
  intros;
  repeat progress match goal with
  | [H: do_run_time_check_on_unop _ _ _ |- _] => inversion H; clear H; smack
  | [|- do_flagged_checks_on_unop _ _ _ _] => constructor; smack
  end.  
Qed.



Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

(** * Soundness Proof of Expression *)

Lemma expression_checks_soundness: forall e e' st st' s v,
  eval_expr st s e v ->
    compile2_flagged_exp st e e' ->
      compile2_flagged_symbol_table st st' ->
        eval_expr_x st' s e' v.
Proof.
  apply (expression_ind
    (fun e: expression => forall (e' : expression_x) (st: symboltable) (st': symboltable_x) (s : STACK.stack) (v: Return value),
      eval_expr st s e v ->
      compile2_flagged_exp st e e' ->
      compile2_flagged_symbol_table st st' ->
      eval_expr_x st' s e' v)
    (fun n: name => forall (n': name_x) (st: symboltable) (st': symboltable_x) (s : STACK.stack) (v: Return value),
      eval_name st s n v ->
      compile2_flagged_name st n n' ->
      compile2_flagged_symbol_table st st' ->
      eval_name_x st' s n' v)
    ); smack.
  - (* 1 *)
  match goal with
  | [H: compile2_flagged_exp _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_expr _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto;
  repeat progress  match goal with
    | [H: eval_literal _ _ |- _] => inversion H; clear H; smack
    | [H: do_overflow_check _ _ |- _] => inversion H; clear H; smack
    end;
  repeat progress match goal with
    | [|- eval_literal_x _ _ _] => constructor
    | [|- do_overflow_checks _ _ _] => constructor
    | [|- do_overflow_check _ _] => constructor; smack
    end;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
  - (* 2 *)
  match goal with
  | [H: compile2_flagged_exp _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_expr _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  specialize (H _ _ _ _ _ H8 H7 H2);
  constructor; auto.
  - (* 3 *) 
  match goal with
  | [H: compile2_flagged_exp _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_expr _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable) 
        (st' : symboltable_x) (s : STACK.stack) (v : Return value),
      eval_expr _ _ ?e _ ->
      compile2_flagged_exp _ ?e _ ->
      compile2_flagged_symbol_table _ _ -> eval_expr_x _ _ _ _,
     H2: eval_expr _ _ ?e _,
     H3: compile2_flagged_exp _ ?e _,
     H4: compile2_flagged_symbol_table _ _ |- _] =>
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  match goal with
  | [H: eval_expr _ _ e (Run_Time_Error _) |- _] => 
      constructor; auto
  | [H1: eval_expr _ _ e (Normal _), 
     H2: eval_expr _ _ e0 (Run_Time_Error _) |- _] =>
      apply Eval_E_Binary_Operation_e2RTE_X with (v1 := v1); auto
  | [H1: eval_expr _ _ e (Normal _), 
     H2: eval_expr _ _ e0 (Normal _),
     H3: do_run_time_check_on_binop _ _ _ _ |- _] =>
      apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  | _ => idtac
  end;
  try (apply binop_overflow_check_soundness; auto);
  match goal with
  | [H: do_run_time_check_on_binop Divide _ _ _ |- _] => 
      apply binop_overflow_division_check_soundness; smack
  | _ => idtac
  end;
  match goal with
  | [H1: ?op = Plus -> False,
     H2: do_run_time_check_on_binop ?op _ _ _ |- _] =>
      apply binop_no_check_soundness; smack
  end.
  - (* 4 *)
  match goal with
  | [H: compile2_flagged_exp _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_expr _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable) 
        (st' : symboltable_x) (s : STACK.stack) (v : Return value),
      eval_expr _ _ ?e _ ->
      compile2_flagged_exp _ ?e _ ->
      compile2_flagged_symbol_table _ _ -> eval_expr_x _ _ _ _,
     H2: eval_expr _ _ ?e _,
     H3: compile2_flagged_exp _ ?e _,
     H4: compile2_flagged_symbol_table _ _ |- _] =>
      specialize (H1 _ _ _ _ _ H2 H3 H4); smack
  end;
  match goal with
  | [H: eval_expr_x _ ?s ?e' (Run_Time_Error _) |- 
       eval_expr_x _ ?s (E_Unary_Operation_X _ Unary_Minus ?e' _ _) (Run_Time_Error _)] =>
      apply Eval_E_Unary_Operation_eRTE_X; auto
  | [H: do_run_time_check_on_unop Unary_Minus _ _ |- _] =>
      apply Eval_E_Unary_Operation_X with (v := v0); auto;
      apply unop_overflow_check_soundness; auto
  | [H1: ?op = Unary_Minus -> False,
     H2: eval_expr _ _ ?e (Run_Time_Error _) |- _] => 
      apply Eval_E_Unary_Operation_eRTE_X; auto
  | [H1: ?op = Unary_Minus -> False,
     H2: eval_expr _ _ ?e (Normal _) |- _] => 
      apply Eval_E_Unary_Operation_X with (v := v0); auto;
      apply unop_no_check_soundness; smack
  end.
  - (* 5 *)
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_name _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto.
  - (* 6 *)
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_name _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : name_x) (st : symboltable) 
        (st' : symboltable_x) (s : STACK.stack) (v : Return value),
      eval_name _ _ ?n _ ->
      compile2_flagged_name _ ?n _ ->
      compile2_flagged_symbol_table _ _ -> eval_name_x _ _ _ _,
     H2: eval_name _ _ ?n _,
     H3: compile2_flagged_name _ ?n _,
     H4: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  try
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable) 
        (st' : symboltable_x) (s : STACK.stack) (v : Return value),
      eval_expr _ _ ?e _ ->
      compile2_flagged_exp _ ?e _ ->
      compile2_flagged_symbol_table _ _ -> eval_expr_x _ _ _ _,
     H2: eval_expr _ _ ?e _,
     H3: compile2_flagged_exp _ ?e _,
     H4: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end.
  + apply Eval_E_Indexed_Component_xRTE_X; auto.
  + apply Eval_E_Indexed_Component_eRTE_X with (a:=a0); auto. 
    apply eval_exp_ex_cks_added; auto.
  + apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H10);
    apply symbol_table_exp_type_rel with (st := st); auto.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.
  + apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H10);
    apply symbol_table_exp_type_rel with (st := st); auto.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.
  - (* 7 *)
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_name _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : name_x) (st : symboltable) 
        (st' : symboltable_x) (s : STACK.stack) (v : Return value),
      eval_name _ _ ?n _ ->
      compile2_flagged_name _ ?n _ ->
      compile2_flagged_symbol_table _ _ -> eval_name_x _ _ _ _,
     H2: eval_name _ _ ?n _,
     H3: compile2_flagged_name _ ?n _,
     H4: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  [ apply Eval_E_Selected_Component_xRTE_X; auto |
    apply Eval_E_Selected_Component_X with (r := r); auto
  ].
Qed.

Lemma name_checks_soundness: forall n n' st st' s v,
  eval_name st s n v ->
    compile2_flagged_name st n n' ->
      compile2_flagged_symbol_table st st' ->
        eval_name_x st' s n' v.
Proof.
  induction n; smack.
  - (* 1. E_Identifier *)
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_name _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  constructor; auto.
  - (* 2. E_Indexed_Component *)
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_name _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  match goal with
  | [H1: forall (n' : name_x) (st : symboltable) 
        (st' : symboltable_x) (s : STACK.stack) (v : Return value),
      eval_name _ _ ?n _ ->
      compile2_flagged_name _ ?n _ ->
      compile2_flagged_symbol_table _ _ -> eval_name_x _ _ _ _,
     H2: eval_name _ _ ?n _,
     H3: compile2_flagged_name _ ?n _,
     H4: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end.
  apply Eval_E_Indexed_Component_xRTE_X; auto.
  apply Eval_E_Indexed_Component_eRTE_X with (a:=a0); auto.
    apply eval_exp_ex_cks_added; auto.
  apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H8); apply symbol_table_exp_type_rel with (st := st); auto.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.
  apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); smack.
    apply eval_exp_ex_cks_added; auto.
    rewrite <- (name_ast_num_eq _ _ _ H8); apply symbol_table_exp_type_rel with (st := st); auto.
    apply index_range_rel with (st := st); auto.
    rewrite exp_updated_exterior_checks; constructor; auto.
  - (* 3. E_Selected_Component *)
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: eval_name _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: forall (n' : name_x) (st : symboltable) 
        (st' : symboltable_x) (s : STACK.stack) (v : Return value),
      eval_name _ _ ?n _ ->
      compile2_flagged_name _ ?n _ ->
      compile2_flagged_symbol_table _ _ -> eval_name_x _ _ _ _,
     H2: eval_name _ _ ?n _,
     H3: compile2_flagged_name _ ?n _,
     H4: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (H1 _ _ _ _ _ H2 H3 H4)
  end;
  [ apply Eval_E_Selected_Component_xRTE_X; auto |
    apply Eval_E_Selected_Component_X with (r := r); auto
  ].
Qed.


Lemma declaration_checks_soundness: forall st s f d f' d' st',
  eval_decl st s f d f' ->
    compile2_flagged_declaration st d d' ->
      compile2_flagged_symbol_table st st' ->
        eval_decl_x st' s f d' f'.
Proof.
  intros st s f d f' d' st' H; revert d' st';
  induction H; intros;
  match goal with
  | [H: compile2_flagged_declaration _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: compile2_flagged_object_declaration _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?t = false,
     H2: extract_subtype_range _ ?t (Range _ _) |- _] => 
      destruct t; inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  [ apply Eval_Decl_Null_X |
    apply Eval_Decl_Type_X |
    apply Eval_Decl_Var_None_X; auto |
    apply Eval_Decl_Var_eRTE_X with (e:=e_flagged); smack |
    apply Eval_Decl_Var_eRTE_X with (e:=(update_exterior_checks_exp e_flagged (Do_Range_Check :: nil))); auto |
    apply Eval_Decl_Var_NoCheck_X with (e:=e_flagged); smack |
    apply Eval_Decl_Var_Range_RTE_X with (e:=(update_exterior_checks_exp e_flagged (Do_Range_Check :: nil))) 
                                           (v:=v) (l:=l) (u:=u); smack |
    apply Eval_Decl_Var_X with (e:=(update_exterior_checks_exp e_flagged (Do_Range_Check :: nil))) (v:=v) (l:=l) (u:=u); smack |
    apply Eval_Decl_Proc_X; auto |
    apply Eval_Decl_Seq_E_X; auto |
    apply Eval_Decl_Seq_X with (f':=f'); auto
  ];
  match goal with
  | [ |- eval_expr_x _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- eval_name_x _ _ (update_exterior_checks_name _ _) _] => apply eval_name_ex_cks_added; auto
  | [ |- context[name_exterior_checks (update_exterior_checks_name _ _)]] => rewrite name_updated_exterior_checks; smack
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- False] => rewrite name_updated_exterior_checks in H; smack
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_x ?st' ?t (Range_X _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end;
  match goal with
  | [H: compile2_flagged_exp _ _ _ |- _] => specialize (exp_exterior_checks_beq_nil _ _ _ H); smack
  end.
Qed.


Lemma store_update_checks_soundness: forall st s x v s' x' st',
  storeUpdate st s x v s' ->
    compile2_flagged_name st x x' ->
      compile2_flagged_symbol_table st st' ->
        storeUpdate_x st' s x' v s'.
Proof.
  intros st s x;
  induction x; smack;
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; subst
  end.
- match goal with
  | [H: storeUpdate _ _ _ _ _ |- _] => inversion H; clear H; subst
  end; constructor; auto.
- match goal with
  | [H: storeUpdate _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: eval_name _ ?s ?n ?v,
     H2: compile2_flagged_name _ ?n ?n',
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (name_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  match goal with
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  match goal with
  | [H1: storeUpdate _ _ ?x _ _ ,
     H2: compile2_flagged_name _ ?x _ ,
     H3: compile2_flagged_symbol_table _ _ |- _ ] => specialize (IHx _ _ _ _ H1 H2 H3)
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
  | [ |- eval_expr_x _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: compile2_flagged_name ?st0 _ ?x' |- context[fetch_exp_type_x (name_astnum_x ?x') _]] =>
      rewrite <- (name_ast_num_eq _ _ _ H); apply symbol_table_exp_type_rel with (st := st0); auto
  | [H1: compile2_flagged_symbol_table ?st ?st', (**)
     H2: extract_array_index_range ?st ?t (Range _ _) |- 
     extract_array_index_range_x ?st' ?t (Range_X _ _)] =>
       specialize (index_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end;
  match goal with
  | [|- do_range_checks _ _ _ _ _ ] => constructor; auto
  end.
- match goal with
  | [H: storeUpdate _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H1: eval_name _ ?s ?n ?v,
     H2: compile2_flagged_name _ ?n ?n',
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (name_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  match goal with
  | [H1: storeUpdate _ _ ?x _ _ ,
     H2: compile2_flagged_name _ ?x _ ,
     H3: compile2_flagged_symbol_table _ _ |- _ ] => specialize (IHx _ _ _ _ H1 H2 H3)
  | _ => idtac
  end;
  [ apply SU_Selected_Component_xRTE_X; auto |
    apply SU_Selected_Component_X with (recObj:=(RecordV r)) (r:=r) (r1:=(updateSelectedComp r i v)); auto |
    apply SU_Selected_Component_X with (recObj:=Undefined) (r:=r) (r1:=((i, v) :: nil)); auto
  ].
Qed.

Lemma copy_in_checks_soundness: forall params st s f args f' params' args' st',
  copy_in st s f params args f' ->
    compile2_flagged_parameter_specifications params params' ->
      compile2_flagged_args st params args args' ->
        compile2_flagged_symbol_table st st' ->
          copy_in_x st' s f params' args' f'.
Proof.
  induction params; smack.
- inversion H; inversion H0; inversion H1; subst;
  constructor.
- destruct args, args', params';
  match goal with 
  | [H: copy_in _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copy_in _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: copy_in_x _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: compile2_flagged_args _ _ (?a :: ?al) nil |- _] => inversion H
  | [H: compile2_flagged_parameter_specifications (?param :: ?params) nil |- _] => inversion H 
  | _ => idtac
  end.
  inversion H0; clear H0; subst.
  assert(HZ1: p.(parameter_name_x) = a.(parameter_name)).
    inversion H6; smack.
  assert(HZ2: p.(parameter_mode_x) = a.(parameter_mode)).
    inversion H6; smack.
  assert (HZ3: p.(parameter_subtype_mark_x) = a.(parameter_subtype_mark)).
    inversion H6; smack.
  inversion H1; clear H1; subst;
  inversion H; clear H; smack;

  match goal with
  | [H1: is_range_constrainted_type (parameter_subtype_mark ?x) = false,
     H2: extract_subtype_range st (parameter_subtype_mark ?x) (Range _ _) |- _] => 
      destruct (parameter_subtype_mark x); inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  | [H1: eval_name _ ?s ?n ?v,
     H2: compile2_flagged_name _ ?n ?n',
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (name_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  match goal with
  | [H1: copy_in _ _ _ ?params ?args ?f',
     H2: compile2_flagged_parameter_specifications ?params ?params',
     H3: compile2_flagged_args st params ?args ?args',
     H4: compile2_flagged_symbol_table _ _ |- _] =>
      specialize (IHparams _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: compile2_flagged_exp _ (E_Name _ (E_Identifier _ ?x)) _ |- _] => inversion H; clear H; subst
  | [H: compile2_flagged_name _ (E_Identifier _ ?x) _ |- _] => inversion H; clear H; subst
  | [H: eval_expr _ _ (E_Name _ (E_Identifier _ ?x)) _ |- _] => inversion H; clear H; subst
  | [H: eval_name _ _ (E_Identifier _ ?x) _ |- _] => inversion H; clear H; subst
  | _ => idtac
  end;
  [ apply Copy_In_Mode_In_eRTE_X; smack |
    apply Copy_In_Mode_In_NoRangeCheck_X with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply Copy_In_Mode_In_eRTE_X; smack |
    apply Copy_In_Mode_In_Range_RTE_X with (v:=v) (l:=l) (u:=u); smack |
    apply Copy_In_Mode_In_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack |
    apply Copy_In_Mode_Out_X with (f':=(STACK.push f (parameter_name a) Undefined)); smack |
    apply Copy_In_Mode_Out_X with (f':=(STACK.push f (parameter_name a) Undefined)); smack |
    apply Copy_In_Mode_InOut_eRTE_x; smack |
    apply Copy_In_Mode_InOut_NoRange_X with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply Copy_In_Mode_InOut_eRTE_x; smack |
    apply Copy_In_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); smack |
    apply Copy_In_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack |
    apply Copy_In_Mode_InOut_eRTE_x; smack | 
    apply Copy_In_Mode_InOut_NoRange_X with (v:=v) (f':=(STACK.push f (parameter_name a) v)); smack |
    apply Copy_In_Mode_InOut_eRTE_x; smack |
    apply Copy_In_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); smack |
    apply Copy_In_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name a) (Int v))); smack
  ];
  match goal with
  | [ |- eval_expr_x _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- eval_name_x _ _ (update_exterior_checks_name _ _) _] => apply eval_name_ex_cks_added; auto
  | [ |- context[name_exterior_checks (update_exterior_checks_name _ _)]] => rewrite name_updated_exterior_checks; smack
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- False] => rewrite name_updated_exterior_checks in H; smack
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_x ?st' ?t (Range_X _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end;
  match goal with
  | [H: compile2_flagged_exp _ _ _ |- _] => specialize (exp_exterior_checks_beq_nil _ _ _ H); smack
  | [H: compile2_flagged_name _ _ _ |- _] => specialize (name_exterior_checks_beq_nil _ _ _ H); smack
  end.
  rewrite H1 in H0; smack.
Qed.


Lemma copy_out_checks_soundness: forall params st s f args f' params' args' st',
  copy_out st s f params args f' ->
    compile2_flagged_parameter_specifications params params' ->
      compile2_flagged_args st params args args' ->
        compile2_flagged_symbol_table st st' ->
          copy_out_x st' s f params' args' f'.
Proof.
  induction params; smack.
- inversion H1; inversion H0; inversion H; subst;
  constructor.
- destruct args, args', params';
  match goal with 
  | [H: copy_out _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: copy_out _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: copy_out_x _ _ _ nil (?a :: ?al) _ |- _] => inversion H
  | [H: compile2_flagged_args _ _ (?a :: ?al) nil |- _] => inversion H
  | [H: compile2_flagged_parameter_specifications (?param :: ?params) nil |- _] => inversion H 
  | _ => idtac
  end.
  inversion H0; clear H0; subst.
  assert(HZ1: p.(parameter_name_x) = a.(parameter_name)).
    inversion H6; smack.
  assert(HZ2: p.(parameter_mode_x) = a.(parameter_mode)).
    inversion H6; smack.
  assert (HZ3: p.(parameter_subtype_mark_x) = a.(parameter_subtype_mark)).
    inversion H6; smack.

  inversion H1; clear H1; subst;
  inversion H; clear H; smack;
  match goal with
  | [H: parameter_mode ?x = In |- _] => apply Copy_Out_Mode_In_X; smack
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
  | [H: compile2_flagged_exp _ (E_Name _ (E_Identifier _ ?x)) _ |- _] => inversion H; clear H; subst
  | [H: compile2_flagged_name _ (E_Identifier _ ?x) _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H1: copy_out _ _ _ ?params ?args ?f',
     H2: compile2_flagged_parameter_specifications ?params ?params',
     H3: compile2_flagged_args st params ?args ?args',
     H4: compile2_flagged_symbol_table _ _ |- _] =>
      specialize (IHparams _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | _ => idtac
  end;
  match goal with
  | [H1: storeUpdate _ _ ?x _ _,
     H2: compile2_flagged_name _ ?x _,
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (store_update_checks_soundness _ _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  [ apply Copy_Out_Mode_Out_nRTE with (v:=v); smack |
    apply Copy_Out_Mode_Out_NoRange_X with (v:=v) (s':=s'); smack |
    apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply Copy_Out_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack |
    apply Copy_Out_Mode_Out_nRTE with (v:=v); smack |
    apply Copy_Out_Mode_Out_NoRange_X with (v:=v) (s':=s'); smack |
    apply Copy_Out_Mode_Out_nRTE with (v:=v); smack |
    apply Copy_Out_Mode_Out_NoRange_X with (v:=v) (s':=s'); smack |
    apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply Copy_Out_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack |
    apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); smack |
    apply Copy_Out_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'); smack 
  ];
  match goal with
  | [ |- context[name_exterior_checks (update_exterior_checks_name _ _)]] => rewrite name_updated_exterior_checks; smack
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: context[name_exterior_checks (update_exterior_checks_name _ _)] |- False] => rewrite name_updated_exterior_checks in H; smack
  | [H1: compile2_flagged_name _ ?n ?n', H2: List.In _ (name_exterior_checks ?n') |- False] => 
      rewrite (name_exterior_checks_beq_nil _ _ _ H1) in H2; inversion H2
  | [ |- context[fetch_exp_type_x _ _]] => apply symbol_table_exp_type_rel with (st := st); auto
  | [ |- storeUpdate_x _ _ _ _ _] => apply store_update_ex_cks_added; auto
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_x ?st' ?t (Range_X _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end. 
Qed.

Lemma statement_assign_checks_soundness: forall st s ast_num x e s' stmt' st',
  eval_stmt st s (S_Assignment ast_num x e) s' -> 
    compile2_flagged_stmt st (S_Assignment ast_num x e) stmt' ->
      compile2_flagged_symbol_table st st' ->
        eval_stmt_x st' s stmt' s'.
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
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  end;
  match goal with
  | [H1: storeUpdate _ _ ?x _ _,
     H2: compile2_flagged_name _ ?x _,
     H3: compile2_flagged_symbol_table _ _ |- _] => specialize (store_update_checks_soundness _ _ _ _ _ _ _ H1 H2 H3); smack
  | _ => idtac
  end;
  [ apply Eval_S_Assignment_eRTE_X; auto |
    apply Eval_S_Assignment_X with (v:=v); auto |
    apply Eval_S_Assignment_eRTE_X; auto |
    apply Eval_S_Assignment_Range_RTE_X with (v:=v) (t:=t0) (l:=l) (u:=u); auto |
    apply Eval_S_Assignment_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u); auto
  ];
  match goal with
  | [H: compile2_flagged_exp _ _ ?e' |- context[exp_exterior_checks ?e']] => specialize (exp_exterior_checks_beq_nil _ _ _ H); smack
  | [ |- eval_expr_x _ _ (update_exterior_checks_exp _ _) _] => apply eval_exp_ex_cks_added; auto
  | [ |- context[exp_exterior_checks (update_exterior_checks_exp _ _)]] => rewrite exp_updated_exterior_checks; auto
  | [H: compile2_flagged_name ?st0 _ ?x' |- context[fetch_exp_type_x (name_astnum_x ?x') _]] =>
      rewrite <- (name_ast_num_eq _ _ _ H); apply symbol_table_exp_type_rel with (st := st0); auto
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: extract_subtype_range ?st ?t (Range _ _) |- 
     extract_subtype_range_x ?st' ?t (Range_X _ _)] =>
       specialize (subtype_range_rel _ _ _ _ _ H1 H2); smack
  end.
Qed.


(** * Soundness Proof of Statement *)

Lemma statement_checks_soundness: forall st s stmt s' stmt' st',
  eval_stmt st s stmt s' -> 
    compile2_flagged_stmt st stmt stmt' ->
      compile2_flagged_symbol_table st st' ->
        eval_stmt_x st' s stmt' s'.
Proof.
  intros st s stmt s' stmt' st' H; revert stmt' st'.
  induction H; intros.
- (* S_Null *)
  inversion H; subst;
  constructor.
- (* S_Assignment *)
  apply statement_assign_checks_soundness with (st:=st) (ast_num:=ast_num) (x:=x) (e:=e); smack.
  apply Eval_S_Assignment_eRTE; auto.
- apply statement_assign_checks_soundness with (st:=st) (ast_num:=ast_num) (x:=x) (e:=e); smack.
  apply Eval_S_Assignment with (v:=v) (t:=t); auto.
- apply statement_assign_checks_soundness with (st:=st) (ast_num:=ast_num) (x:=x) (e:=e); smack.
  apply Eval_S_Assignment_Range_RTE with (v:=v) (t:=t) (l:=l) (u:=u); auto.
- apply statement_assign_checks_soundness with (st:=st) (ast_num:=ast_num) (x:=x) (e:=e); smack.
  apply Eval_S_Assignment_Range with (v:=v) (t:=t) (l:=l) (u:=u); auto.
- (* If RTE *)
  inversion H0; clear H0; subst;
  apply Eval_S_If_RTE_X;
  match goal with
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  end. 
- (* If True *)
  inversion H1; clear H1; subst;
  apply Eval_S_If_True_X.
  match goal with
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  end.
  apply IHeval_stmt; smack.
- (* If False *)
  inversion H1; clear H1; subst;
  apply Eval_S_If_False_X; smack.
  match goal with
  | [H1: eval_expr _ ?s ?e ?v,
     H2: compile2_flagged_exp _ ?e ?e',
     H3: compile2_flagged_symbol_table _ _ |- _] => 
      specialize (expression_checks_soundness _ _ _ _ _ _ H1 H2 H3); smack
  end.
- (* While RTE *)
  inversion H0; clear H0; subst;
  apply Eval_S_While_Loop_RTE_X;
  specialize (expression_checks_soundness _ _ _ _ _ _ H H7 H1); smack.
- (* While True RTE *)
  inversion H1; clear H1; subst;
  apply Eval_S_While_Loop_True_RTE_X.
  specialize (expression_checks_soundness _ _ _ _ _ _ H H8 H2); smack.
  apply IHeval_stmt; smack.
- (* While True *)
  inversion H2; clear H2; subst;
  apply Eval_S_While_Loop_True_X with (s1:=s1).
  specialize (expression_checks_soundness _ _ _ _ _ _ H H9 H3); smack.
  apply IHeval_stmt1; smack.  
  apply IHeval_stmt2; smack.
  constructor; auto.
- (* While False *)
  inversion H0; clear H0; subst;
  apply Eval_S_While_Loop_False_X;
  specialize (expression_checks_soundness _ _ _ _ _ _ H H7 H1); smack.
- (* Procedure Call Args RTE *)
  inversion H1; subst;
  rewrite H in H9; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H2 H); smack;
  specialize (procedure_components_rel _ _ _ H5); smack;
  apply Eval_S_Proc_RTE_Args_X with (n:=n0) (pb:=x); smack;
  specialize (copy_in_checks_soundness _ _ _ _ _ _ _ _ _ H0 H6 H11 H2); smack.
- (* Procedure Call Decls RTE *)
  inversion H3; subst;
  rewrite H in H11; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H4 H); smack;
  specialize (procedure_components_rel _ _ _ H7); smack;
  apply Eval_S_Proc_RTE_Decl_X with (n:=n0) (pb:=x) (f:=f) (intact_s:=intact_s) (s1:=s1); smack.
  specialize (copy_in_checks_soundness _ _ _ _ _ _ _ _ _ H0 H8 H13 H4); smack.
  specialize (declaration_checks_soundness _ _ _ _ _ _ _ H2 H5 H4); smack.
- (* Procedure Call Body RTE *)
  inversion H4; subst;
  rewrite H in H12; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H5 H); smack;
  specialize (procedure_components_rel _ _ _ H8); smack;
  apply Eval_S_Proc_RTE_Body_X with (n:=n0) (pb:=x) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1); smack.
  specialize (copy_in_checks_soundness _ _ _ _ _ _ _ _ _ H0 H9 H14 H5); smack.
  specialize (declaration_checks_soundness _ _ _ _ _ _ _ H2 H6 H5); smack.
- (* Procedure Call *)
  inversion H7; subst;
  rewrite H in H15; smack;
  specialize (symbol_table_procedure_rel _ _ _ _ _ H8 H); smack;
  specialize (procedure_components_rel _ _ _ H10); smack;
  specialize (IHeval_stmt _ _ H13 H8); smack;
  apply Eval_S_Proc_X with (n:=n0) (pb:=x) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1)
                            (s2:=((n0, locals_section ++ params_section) :: s3)) 
                            (locals_section:=locals_section) (params_section:=params_section) 
                            (s3:=s3); smack.
  specialize (copy_in_checks_soundness _ _ _ _ _ _ _ _ _ H0 H11 H17 H8); smack.
  specialize (declaration_checks_soundness _ _ _ _ _ _ _ H2 H4 H8); smack.
  specialize (copy_out_checks_soundness _ _ _ _ _ _ _ _ _ H6 H11 H17 H8); smack.
- (* Sequence RTE *)
  inversion H0; smack;
  apply Eval_S_Sequence_RTE_X;
  apply IHeval_stmt; smack.
- (* Sequence *)
  inversion H1; smack;
  apply Eval_S_Sequence_X with (s1:=s1); smack.
Qed.














