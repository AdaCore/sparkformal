Require Export checks_generator.
Require Export well_typed.
Require Export checks_optimization_util.

Import STACK. 


(** * Helper Lemmas *)
Lemma fetchG_split: forall s1 s2 x v,
  fetchG x (s1 ++ s2) = Some v ->
    fetchG x s1 = Some v \/ fetchG x s2 = Some v.
Proof.
  induction s1; crush;eauto.
  destruct (fetch x a); crush;eauto.
Qed.

Ltac apply_fetchG_split :=
  match goal with
  | [H: fetchG ?x (?s1 ++ ?s2) = Some _ |- _] =>
      specialize (fetchG_split _ _ _ _ H);
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in intros HZ1; destruct HZ1 as [HZ1 | HZ2]
  end.

(********************************************************************)
(********************************************************************)

Lemma range_constrainted_type_true: forall st x u v,
  extract_subtype_range_x st x (Range_X u v) ->
    is_range_constrainted_type x = true.
Proof.
  intros;
  inversion H; subst;
  destruct x; crush;eauto.
Qed.

Lemma well_typed_exp_preserve: forall e st cks,
  well_typed_exp_x st (update_exterior_checks_exp e cks) ->
    well_typed_exp_x st e.
Proof.
  apply (expression_x_ind
    (fun e: expression_x =>
       forall (st : symboltable_x) (cks : exterior_checks),
       well_typed_exp_x st (update_exterior_checks_exp e cks) ->
       well_typed_exp_x st e)
    (fun n: name_x =>
       forall (st : symboltable_x) (cks : exterior_checks),
       well_typed_name_x st (update_exterior_checks_name n cks) ->
       well_typed_name_x st n)
    ); intros.
- inversion H; subst; simpl in H;
  constructor; crush;eauto.
- inversion H0; subst.
  specialize (H _ _ H5); constructor; auto.
  inversion H; subst; simpl in *; crush;eauto.
- simpl in H1.
  inversion H1; subst.
  rewrite <- (exp_exterior_checks_refl e) in H9.
  rewrite <- (exp_exterior_checks_refl e0) in H10.  
  specialize (H _ _ H9).
  specialize (H0 _ _ H10).
  apply WT_Binary_Exp_X with (t := t) (t1 := t1) (t2 := t2); auto.
- simpl in H0.
  inversion H0; subst.
  rewrite <- (exp_exterior_checks_refl e) in H6.
  specialize (H _ _ H6).
  Print well_typed_exp_x.
  apply WT_Unary_Exp_X with (t := t) (t' := t'); auto.
- simpl in H.
  inversion H; subst.
  apply WT_Identifier_X with (md := md) (t := t); auto.
- inversion H1; subst.
  rewrite <- (name_exterior_checks_refl n) in H6.
  rewrite <- (exp_exterior_checks_refl e) in H8.
  specialize (H _ _ H6).
  specialize (H0 _ _ H8).
  Print well_typed_name_x.
  apply WT_Indexed_Component_X with (t := t) (t' := t') (a_ast_num := a_ast_num) (tn := tn) (tm := tm); auto.
- simpl in H0.
  inversion H0; subst.
  rewrite <- (name_exterior_checks_refl n) in H5.
  specialize (H _ _ H5).
  apply WT_Selected_Component_X with (t := t) (t' := t') (r_ast_num := r_ast_num) 
                                     (tn := tn) (fields := fields); auto.
Qed.

Ltac apply_well_typed_exp_preserve :=
  match goal with
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma well_typed_name_preserve: forall n st cks,
  well_typed_name_x st (update_exterior_checks_name n cks) ->
    well_typed_name_x st n.
Proof.
  induction n; intros;
  inversion H; subst.
- apply WT_Identifier_X with (md := md) (t := t); auto.
- apply WT_Indexed_Component_X with (t := t) (t' := t') (a_ast_num := a_ast_num) (tn := tn) (tm := tm); auto.
- apply WT_Selected_Component_X with (t := t) (t' := t') (r_ast_num := r_ast_num) 
                                     (tn := tn) (fields := fields); auto.
Qed.

Ltac apply_well_typed_name_preserve :=
  match goal with
  | [H: well_typed_name_x _ (update_exterior_checks_name _ _) |- _] =>
      specialize (well_typed_name_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.


Lemma well_typed_store_updated_by_undefined_value: forall st f x m t,
  well_typed_store st (snd f) ->
    fetch_var_x x st = Some (m, t) ->
      well_typed_store st (snd (push f x Undefined)).
Proof.
  intros.
  inversion H; subst.
  constructor; crush;eauto.
  remember (beq_nat x0 x) as b.
  destruct b; crush;eauto.
  rewrite (beq_nat_eq _ _ Heqb).
  exists m t; crush;eauto.
  constructor.
Qed.

Ltac apply_well_typed_store_updated_by_undefined_value :=
  match goal with
  | [H1: well_typed_store ?st _,
     H2: fetch_var_x ?x ?st = Some (?m, ?t) |- _] =>
      specialize (well_typed_store_updated_by_undefined_value _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.


Lemma well_typed_store_stack_merge: forall st f s,
  well_typed_store st (snd f) -> (* the frame is well-typed *)
    well_typed_stack st s ->
      well_typed_stack st (f :: s).
Proof.
  intros.
  constructor; crush;eauto.
- remember (fetch x f) as b.
  destruct b; crush;eauto.
  inversion H; crush;eauto.
  inversion H0; crush;eauto.
Qed.

Ltac apply_well_typed_store_stack_merge :=
  match goal with
  | [H1: well_typed_store ?st _,
     H2: well_typed_stack ?st _ |- _] =>
      specialize (well_typed_store_stack_merge _ _ _ H1 H2); let HZ := fresh "HZ" in intros HZ
  end.

Lemma well_typed_stacks_merge: forall st s1 s2,
  well_typed_stack st s1 ->
    well_typed_stack st s2 ->
      well_typed_stack st (s1 ++ s2).
Proof.
  intros.
  constructor; crush;eauto.
- apply_fetchG_split.
  inversion H; crush;eauto.
  inversion H0; crush;eauto.
Qed.

Ltac apply_well_typed_stacks_merge :=
  match goal with
  | [H1: well_typed_stack ?st ?s1,
     H2: well_typed_stack ?st ?s2 |- _] =>
      specialize (well_typed_stacks_merge _ _ _ H1 H2); let HZ := fresh "HZ" in intros HZ
  end.

(* it's impossible to prove the following two lemmas. as for any x, that fetchG x (f :: s) = Some v, 
   its value v is well typed, it may be the case that the value of x in f covers the value of x in s
   where the value of x in s is not well-typed; the lemma can be true only if any variable in (f :: s)
   is unique;
*)
(*
Lemma well_typed_store_stack_split: forall st f s,
  well_typed_stack st (f :: s) ->
    well_typed_stack st s /\ well_typed_store st (snd f).
Proof.
  intros.
  inversion H; subst; crush;eauto; clear H1.
  constructor; intros. admit.
  admit. admit.
Qed.

Lemma well_typed_stack_split: forall st s1 s2,
  well_typed_stack st (s1 ++ s2) ->
    well_typed_stack st s1 /\ well_typed_stack st s2.
Proof.
  admit.
Qed.
*)

(********************************************************************)
(********************************************************************)

(** * well-typed store and stack lemmas *)

Lemma well_typed_store_updated_by_undefined_value': forall st f x m t,
  well_typed_value_in_store st (snd f) ->
    fetch_var_x x st = Some (m, t) ->
      well_typed_value_in_store st (snd (push f x Undefined)).
Proof.
  intros.
  constructor; crush;eauto.
  exists m t; crush;eauto; constructor.
Qed.

Ltac apply_well_typed_store_updated_by_undefined_value' :=
  match goal with
  | [H1: well_typed_value_in_store ?st _, 
     H2: fetch_var_x ?x ?st = Some (?m, ?t) |- _] =>
      specialize (well_typed_store_updated_by_undefined_value' _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma well_typed_store_stack_merge': forall st f s,
  well_typed_value_in_store st (snd f) ->
    well_typed_value_in_stack st s ->
      well_typed_value_in_stack st (f :: s).
Proof.
  intros;
  constructor; crush;eauto.
Qed.

Ltac apply_well_typed_store_stack_merge' :=
  match goal with
  | [H1: well_typed_value_in_store ?st _,
     H2: well_typed_value_in_stack ?st _ |- _] =>
      specialize (well_typed_store_stack_merge' _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma well_typed_store_merge': forall st s1 s2,
  well_typed_value_in_store st s1 ->
    well_typed_value_in_store st s2 ->
      well_typed_value_in_store st (s1 ++ s2).
Proof.
  intros st s1;
  induction s1; crush;eauto.
  inversion H; subst.
  specialize (IHs1 _ H6 H0).
  constructor; crush;eauto.
Qed.

Ltac apply_well_typed_store_merge' := 
  match goal with
  | [H1: well_typed_value_in_store ?st ?s1,
     H2: well_typed_value_in_store ?st ?s2 |- _] =>
      specialize (well_typed_store_merge' _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma well_typed_stacks_merge': forall st s1 s2,
  well_typed_value_in_stack st s1 ->
    well_typed_value_in_stack st s2 ->
      well_typed_value_in_stack st (s1 ++ s2).
Proof.
  intros st s1; revert st;
  induction s1; crush;eauto;
  inversion H; subst;
  specialize (IHs1 _ _ H5 H0);
  constructor; auto.
Qed.

Ltac apply_well_typed_stacks_merge' :=
  match goal with
  | [H1: well_typed_value_in_stack ?st ?s1,
     H2: well_typed_value_in_stack ?st ?s2 |- _] =>
      specialize (well_typed_stacks_merge' _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma well_typed_store_stack_split': forall st f s,
  well_typed_value_in_stack st (f :: s)  ->
    well_typed_value_in_stack st s /\ well_typed_value_in_store st (snd f).
Proof.
  intros;
  inversion H; auto.
Qed.

Ltac apply_well_typed_store_stack_split' := 
  match goal with
  | [H: well_typed_value_in_stack ?st (?f :: ?s) |- _] =>
      specialize (well_typed_store_stack_split' _ _ _ H);
      let HZ := fresh "HZ" in 
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in 
      intros HZ; destruct HZ as [HZ1 HZ2]
  end.

Lemma well_typed_store_split': forall st s1 s2,
  well_typed_value_in_store st (s1 ++ s2) ->
    well_typed_value_in_store st s1 /\ well_typed_value_in_store st s2.
Proof.
  intros st s1;
  induction s1; crush;eauto;
  match goal with
  | [ |- well_typed_value_in_store _ nil] => constructor
  | [H: well_typed_value_in_store _ _ |- _] => inversion H; subst; specialize (IHs1 _ H5); crush;eauto
  end;
  constructor; crush;eauto.
Qed.

Ltac apply_well_typed_store_split' :=
  match goal with
  | [H: well_typed_value_in_store ?st (?s1 ++ ?s2) |- _] => 
      specialize (well_typed_store_split' _ _ _ H);
      let HZ := fresh "HZ" in 
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in 
      intros HZ; destruct HZ as [HZ1 HZ2]
  end.

Lemma well_typed_stack_split': forall st s1 s2,
  well_typed_value_in_stack st (s1 ++ s2) ->
    well_typed_value_in_stack st s1 /\ well_typed_value_in_stack st s2.
Proof.
  intros st s1; revert st.
  induction s1; crush;eauto;
  match goal with
  | [|- well_typed_value_in_stack _ nil] => constructor
  | [H: well_typed_value_in_stack _ _ |- _] => 
      inversion H; subst; specialize (IHs1 _ _ H4); crush;eauto
  end;
  constructor; auto.
Qed.

Ltac apply_well_typed_stack_split' :=
  match goal with
  | [H: well_typed_value_in_stack _ (?s1 ++ ?s2) |- _] => 
      specialize (well_typed_stack_split' _ _ _ H);
      let HZ := fresh "HZ" in 
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in 
      intros HZ; destruct HZ as [HZ1 HZ2]
  end.


(********************************************************************)
(********************************************************************)

(** * storeUpdate_preserve_typed_stack *)

(*
  - assignment 
  - declaration

       eval_expr_x st (f :: s) e (Normal v)
  H1 : exp_exterior_checks e = nil
  H3 : compile2_flagged_symbol_table st0 st
  H5 : well_typed_stack st s
  H6 : well_typed_store st (snd f)
  H11 : compile2_flagged_object_declaration st0 o d
  ============================
   well_typed_store st (snd (push f (object_name_x d) v))


storeUpdate_preserve_typed_stack:

  case 1:

  H0 : fetch (parameter_name_x param) f = Some v
  H1 : ~ List.In Do_Range_Check_On_CopyOut (name_exterior_checks n)
  H2 : storeUpdate_x st s n v (Normal s')
  H4 : compile2_flagged_symbol_table st0 st
  H7 : well_typed_symbol_table st
  H8 : well_typed_value_in_stack st s
  H9 : well_typed_value_in_store st (snd f)
  H17 : well_typed_exp_x st (E_Name_X ast_num n)
  H19 : fetch_var_x (parameter_name_x param) st =
        Some (m, parameter_subtype_mark_x param)
  H31 : fetch_exp_type ast_num st0 = Some t0
  H32 : is_range_constrainted_type t0 = false
  H33 : compile2_flagged_name st0 n0 n
  H23 : fetch_exp_type_x ast_num st = Some t0
  H24 : type_match t0 (parameter_subtype_mark_x param) = true

  =============================

  case 2: with range chek

  H3 : do_range_check v l u (Normal (Int v))
  H5 : compile2_flagged_symbol_table st0 st
  H7 : well_typed_stack_and_symboltable st s
  H4 : storeUpdate_x st s x (Int v) (Normal s')
  H14 : well_typed_name_x st x
  H18 : type_match t0 t' = true
  H22 : compile2_flagged_name st0 x0 x
  H23 : compile2_flagged_exp st0 e0 e_flagged
  H : eval_expr_x st s
        (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil))
        (Normal (Int v))
  H0 : exp_exterior_checks
         (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)) =
       Do_Range_Check :: nil
  H13 : well_typed_exp_x st
          (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil))
  H16 : fetch_exp_type_x
          (expression_astnum_x
             (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)))
          st = Some t0
  H15 : fetch_exp_type (name_astnum_x x) st0 = Some t'
  H21 : is_range_constrainted_type t' = true

  ===========================================

  case 1: no range check :
  H : eval_expr_x st s e (Normal v)
  H2 : compile2_flagged_symbol_table st0 st
  H4 : well_typed_stack_and_symboltable st s
  H1 : storeUpdate_x st s x v (Normal s')
  H10 : well_typed_exp_x st e
  H11 : well_typed_name_x st x
  H13 : fetch_exp_type_x (expression_astnum_x e) st = Some t
  H14 : fetch_exp_type_x (name_astnum_x x) st = Some t'
  H15 : type_match t t' = true
  H18 : is_range_constrainted_type t' = false
  H19 : compile2_flagged_name st0 x0 x
  H20 : compile2_flagged_exp st0 e0 e
  ============================
   well_typed_stack_and_symboltable st s'
*)

Lemma value_in_range_is_well_typed: forall st t v l u,
  extract_subtype_range_x st t (Range_X l u) -> 
    do_range_check v l u (Normal (Int v)) -> 
      well_typed_value st t (Int v).
Proof.
  intros.
  destruct t; inversion H; subst; 
  inversion H3; subst;
  [ apply TV_Subtype with (l:=l) (u:=u); auto |
    apply TV_Derived_Type with (l:=l) (u:=u); auto |
    apply TV_Integer_Type with (l:=l) (u:=u); auto
  ];
  match goal with
  | [H: do_range_check _ _ _ _ |- _] => inversion H; subst; auto
  end.
Qed.

Ltac apply_value_in_range_is_well_typed :=
  match goal with
  | [H1: extract_subtype_range_x ?st ?t (Range_X ?l ?u),
     H2: do_range_check ?v ?l ?u (Normal (Int ?v)) |- _] =>
      specialize (value_in_range_is_well_typed _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)

Lemma binop_int_type: forall op t1 t2 t,
  (op = Plus \/ op = Minus \/ op = Multiply) \/ op = Divide ->
    binop_type op t1 t2 = Some t ->
      t = Integer.
Proof.
  intros;
  destruct H as [[H1 | [H1 | H1]] | H1]; subst;
  destruct t1, t2; crush;eauto.  
Qed.

Ltac apply_binop_int_type :=
  match goal with
  | [H1: ?op' = Plus \/ ?op' = Minus \/ ?op' = Multiply,
     H2: binop_type ?op' ?t1' ?t2' = Some ?t' |- _] => 
      apply binop_int_type with (op := op') (t1 := t1') (t2 := t2');
      [ left; apply H1 |
        apply H2
      ]
  | [H1: ?op' = Divide,
     H2: binop_type ?op' ?t1' ?t2' = Some ?t' |- _] => 
      apply binop_int_type with (op := op') (t1 := t1') (t2 := t2');
      [ right; apply H1 |
        apply H2
      ]
  end.

Lemma binop_bool_type: forall op t1 t2 t,
  op <> Plus ->
  op <> Minus ->
  op <> Multiply ->
  op <> Divide ->                
  binop_type op t1 t2 = Some t ->
  t = Boolean.
Proof.
  intros;
  destruct op; crush;eauto; clear H H0 H1 H2;
  destruct t1, t2; inversion H3; auto.
Qed.

Ltac apply_binop_bool_type :=
  match goal with
  | [H1: ?op <> Plus,
     H2: ?op <> Minus,
     H3: ?op <> Multiply,
     H4: ?op <> Divide,         
     H5: binop_type ?op ?t1 ?t2 = Some ?t |- _] => specialize (binop_bool_type _ _ _ _ H1 H2 H3 H4 H5)
  end.

Lemma binop_arithm_typed: forall op v1 v2 v,
  do_flagged_checks_on_binop (Do_Overflow_Check :: nil) op v1 v2 (Normal v) ->
    forall st, well_typed_value st Integer v.
Proof.
  intros;
  inversion H; subst;
  inversion H2; subst;
  inversion H7; subst;
  rewrite H5 in H1; inversion H1; subst;
  inversion H3; subst;
  constructor; auto.
Qed.

Ltac apply_binop_arithm_typed :=
  match goal with
  | [H: do_flagged_checks_on_binop (Do_Overflow_Check :: nil) _ _ _ _ |- _] =>
      specialize (binop_arithm_typed _ _ _ _ H)
  end.

Lemma binop_logic_typed: forall op v1 v2 v,
  op <> Plus ->
  op <> Minus ->
  op <> Multiply ->
  op <> Divide ->
  do_flagged_checks_on_binop nil op v1 v2 (Normal v) ->
  forall st, well_typed_value st Boolean v.
Proof.
  intros;
  inversion H3; subst; clear H3;
  destruct op; crush;eauto;
  clear H H0 H1 H2;
  destruct v1, v2; inversion H5;
  constructor;
  match goal with
  | [|- ?b = _ \/ ?b = _] => destruct b; auto
  end.
Qed.

Ltac apply_binop_logic_typed :=
  match goal with
  | [H1: ?op <> Plus,
     H2: ?op <> Minus,
     H3: ?op <> Multiply,
     H4: ?op <> Divide,         
     H5: do_flagged_checks_on_binop nil ?op _ _ _ |- _] => 
      specialize (binop_logic_typed _ _ _ _ H1 H2 H3 H4 H5)
  end.

Lemma unop_minus_typed: forall v v',
  do_flagged_checks_on_unop (Do_Overflow_Check :: nil) Unary_Minus v (Normal v') ->
    forall st, well_typed_value st Integer v'.
Proof.
  intros;
  inversion H; subst; clear H;
  inversion H2; subst; clear H2;
  inversion H6; subst; clear H6;
  inversion H2; subst; clear H2;
  rewrite H3 in H; inversion H; subst;
  inversion H0; subst;
  constructor; auto.
Qed.

Ltac apply_unop_minus_typed :=
  match goal with
  | [H: do_flagged_checks_on_unop (Do_Overflow_Check :: nil) Unary_Minus _ (Normal _) |- _] =>
      specialize (unop_minus_typed _ _ H)
  end.

Lemma exp_type_same: forall st e t t',
  well_typed_exp_x st e ->
    type_of_exp_x st e = Some t ->
      fetch_exp_type_x (expression_astnum_x e) st = Some t' ->
        t = t'.
Proof.
  intros;
  inversion H; crush;eauto;
  inversion H2; crush;eauto.
Qed.

Ltac apply_exp_type_same :=
  match goal with
  | [H1: well_typed_exp_x ?st ?e,
     H2: type_of_exp_x ?st ?e = Some _,
     H3: fetch_exp_type_x (expression_astnum_x ?e) ?st = Some _ |- _] =>
      specialize (exp_type_same _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ; subst
  end.

(** * Eval Exp_or_Name Value Well Typed *)

Lemma eval_expr_well_typed_value: forall e st st' s e' v,
  compile2_flagged_exp st e e' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_exp_x st' e' ->
          eval_expr_x st' s e' (Normal v) ->
            exists t, fetch_exp_type_x (expression_astnum_x e') st' = Some t /\ 
                      well_typed_value st' t v.
Proof.
  apply (expression_ind
    (fun e: expression =>
       forall (st : symboltable) (st' : symboltable_x) (s : STACK.stack) 
              (e' : expression_x) (v : value),
       compile2_flagged_exp st e e' ->
       compile2_flagged_symbol_table st st' ->
       well_typed_stack st' s ->
       well_typed_exp_x st' e' ->
       eval_expr_x st' s e' (Normal v) ->
       exists t,
         fetch_exp_type_x (expression_astnum_x e') st' = Some t /\
         well_typed_value st' t v)
    (fun n: name =>
       forall (st : symboltable) (st' : symboltable_x) (s : STACK.stack) 
              (n' : name_x) (v : value),
       compile2_flagged_name st n n' ->
       compile2_flagged_symbol_table st st' ->
       well_typed_stack st' s ->
       well_typed_name_x st' n' ->
       eval_name_x st' s n' (Normal v) ->
       exists t,
         fetch_exp_type_x (name_astnum_x n') st' = Some t /\
         well_typed_value st' t v)
    ); intros.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst. 
  
  exists Boolean; crush;eauto.
  inversion H12; crush;eauto. constructor; destruct b; crush;eauto.
  
  exists Integer; crush;eauto.
  inversion H13; crush;eauto. inversion H7; subst. constructor; crush;eauto.
  
  exists Integer; crush;eauto.
  inversion H13; crush;eauto. inversion H7; subst. inversion H4; subst.
  apply_in_bound_conflict; crush;eauto.
- inversion H0; subst;
  inversion H3; subst; 
  inversion H4; subst.
  specialize(H _ _ _ _ _ H9 H1 H2 H10 H13); crush;eauto.
- inversion H1; subst;
  inversion H4; subst;
  inversion H5; subst;
  simpl;
  match goal with
  | [H: fetch_exp_type_x _ _ = Some ?t |- _] => rewrite H; exists t
  end; split; auto.
  + assert (HZ1: t = Integer).
    apply_binop_int_type. subst.
    apply_binop_arithm_typed; auto.
  + assert (HZ1: t = Integer).
    apply binop_int_type with (op := Divide) (t1 := t1) (t2 := t2); auto.
    inversion H25; subst.
    apply_binop_arithm_typed; auto.
  + assert (HZ1: t = Boolean).
    apply_binop_bool_type; auto.
    apply_binop_logic_typed; subst; auto.
- inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  simpl;
  match goal with
  | [H: fetch_exp_type_x _ _ = Some ?t |- _] => rewrite H; exists t
  end; split; auto.
  + assert(HZ1: t = Integer).
    destruct t'; inversion H15; auto.
    apply_unop_minus_typed. subst; auto.
  + destruct u;
    specialize (H _ _ _ _ _ H11 H1 H2 H12 H19);
    inversion H; destruct H5;
    apply_exp_type_same; intros.
    inversion H20; subst. inversion H8; subst.
    destruct v0; inversion H9; subst.
    inversion H16; subst; assumption.
    crush;eauto.
    inversion H20; subst. inversion H8; subst.
    destruct v0; inversion H9; subst.
    destruct x; inversion H16; subst. 
    destruct (negb n); constructor; auto.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  simpl;
  match goal with
  | [H: fetch_exp_type_x _ _ = Some ?t |- _] => rewrite H; exists t
  end; split; auto.
  inversion H1; subst.
  specialize (H4 _ _ H8); crush;eauto.
- inversion H1; subst;
  inversion H4; subst;
  inversion H5; subst;
  simpl;
  match goal with
  | [H: fetch_exp_type_x _ _ = Some ?t |- _] => rewrite H; exists t
  end; split; auto.
  specialize (H _ _ _ _ _ H12 H2 H3 H10 H18). 
  inversion H. destruct H6.
  inversion H7; subst.
  specialize (H26 _ _ H25).
  rewrite H16 in H6; inversion H6; subst.
  rewrite H17 in H9; inversion H9; subst.
  destruct H26; assumption.
- inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  simpl;
  match goal with
  | [H: fetch_exp_type_x _ _ = Some ?t |- _] => rewrite H; exists t
  end; split; auto.
  specialize (H _ _ _ _ _ H10 H1 H2 H9 H11).
  inversion H; subst.
  destruct H5.
  inversion H6; subst.
  rewrite H13 in H5; inversion H5; subst.
  rewrite H14 in H8; inversion H8; subst.
  specialize (H18 _ _ H19). 
  destruct H18 as [t' [HZ1 HZ2]]. 
  rewrite H15 in HZ1; inversion HZ1; subst; assumption.
Qed.

Ltac apply_eval_expr_well_typed_value := 
  match goal with
  | [H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: eval_expr_x ?st' ?s ?e' (Normal ?v) |- _] =>
      specialize (eval_expr_well_typed_value _ _ _ _ _ _ H1 H2 H3 H4 H5);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma eval_name_well_typed_value: forall n st st' s n' v,
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          eval_name_x st' s n' (Normal v) ->
            exists t, fetch_exp_type_x (name_astnum_x n') st' = Some t /\ 
                      well_typed_value st' t v.
Proof.
  induction n; intros.
- inversion H; subst;
  inversion H1; subst; 
  inversion H2; subst;
  inversion H3; subst.
  specialize (H4 _ _ H9).
  destruct H4 as [md' [t' [HZ1 HZ2]]].
  exists t; crush;eauto.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst.
  specialize (IHn _ _ _ _ _ H10 H0 H1 H8 H16).
  destruct IHn as [t'' [HZ1 HZ2]].
  simpl.
  inversion HZ2; subst.
  specialize (H17 _ _ H23).
  exists typ; crush;eauto.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst.
  specialize (IHn _ _ _ _ _ H9 H0 H1 H8 H10).
  destruct IHn as [t'' [HZ1 HZ2]].
  simpl.
  inversion HZ2; subst. 
  rewrite H12 in HZ1; inversion HZ1; subst.
  rewrite H13 in H5; inversion H5; subst.
  specialize (H15 _ _ H18).
  destruct H15 as [t' [HZ3 HZ4]].
  rewrite H14 in HZ3; inversion HZ3; subst;
  exists t'; crush;eauto.
Qed.

Ltac apply_eval_name_well_typed_value :=
  match goal with
  | [H1: compile2_flagged_name ?st ?n ?n',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: eval_name_x ?st' ?s ?n' (Normal ?v) |- _] =>
      specialize (eval_name_well_typed_value _ _ _ _ _ _ H1 H2 H3 H4 H5);
      let t := fresh "t" in
      let HZ := fresh "HZ" in
      let HZ1 := fresh "HZ" in
      let HZ2 := fresh "HZ" in
      intros HZ; destruct HZ as [t [HZ1 HZ2]]
  end.

(** * Typed Value in Bound *)
Lemma typed_value_in_bound1: forall st t v vBound,
  well_typed_value st t (Int v) ->
    bound_of_type st t vBound ->
      in_bound v vBound true.
Proof.
  intros;
  inversion H; subst; inversion H0; subst; crush;eauto;
  match goal with
  | [H1: extract_subtype_range_x _ _ _,
     H2: extract_subtype_range_x _ _ _ |- _] => apply_extract_subtype_range_unique; auto
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ _ |- _] => inversion H; subst; crush;eauto
  end.
Qed.

Lemma typed_value_in_bound2: forall st t v l u,
  well_typed_value st t (Int v) ->  
    extract_subtype_range_x st t (Range_X l u) ->
      in_bound v (Interval l u) true.
Proof.
  intros;
  inversion H; subst; inversion H0; subst; crush;eauto;
  match goal with
  | [H1: extract_subtype_range_x _ _ _,
     H2: extract_subtype_range_x _ _ _ |- _] => apply_extract_subtype_range_unique; auto
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ _ |- _] => inversion H; subst; crush;eauto
  end.
Qed.

Ltac apply_typed_value_in_bound := 
  match goal with
  | [H1: well_typed_value ?st ?t (Int ?v),
     H2: bound_of_type ?st ?t ?vBound |- _] =>
      specialize (typed_value_in_bound1 _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | [H1: well_typed_value ?st ?t (Int ?v), 
     H2: extract_subtype_range_x ?st ?t (Range_X ?l ?u) |- _] =>
      specialize (typed_value_in_bound2 _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.


(***********************************************************)
(***********************************************************)
(***********************************************************)

Lemma value_well_typed_with_matched_type: forall st t t' v,
  well_typed_symbol_table st ->
    is_range_constrainted_type t = false ->
      well_typed_value st t' v ->
        type_match t t' = true ->
          well_typed_value st t v.
Proof.
  intros.
  inversion H; subst; inversion H3; subst.
  destruct t; inversion H0; crush;eauto;
  destruct t'; inversion H2; crush;eauto;
  match goal with
  | [H: beq_nat _ _ = true |- _] => symmetry in H; rewrite (beq_nat_eq _ _ H); auto
  | [H: well_typed_value st _ _ |- _] => inversion H; subst
  | _ => idtac
  end;
  match goal with
  | [|- well_typed_value _ _ Undefined] => constructor
  | [H1: forall (t : type) (l u : Z),
       extract_subtype_range_x ?st t (Range_X l u) ->
       sub_bound (Interval l u) int32_bound true,
     H2: extract_subtype_range_x ?st ?t (Range_X ?l ?u) |- _] =>  
      specialize (H1 _ _ _ H2)
  end;
  apply_In_Bound_SubBound_Trans;
  constructor; auto.
Qed.

Ltac apply_value_well_typed_with_matched_type :=
  match goal with
  | [H1: well_typed_symbol_table ?st,
     H2: is_range_constrainted_type ?t = false,
     H3: well_typed_value ?st ?t' ?v,
     H4: type_match ?t ?t' = true |- _] =>
      specialize (value_well_typed_with_matched_type _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intros HZ
  end.


Lemma storeUpdate_with_typed_value_preserve_typed_store: forall st f f' x m t v,
  update f x v = Some f' ->
    well_typed_value_in_store st (snd f) ->
      fetch_var_x x st = Some (m, t) ->
        well_typed_value st t v ->    
          well_typed_value_in_store st (snd f').
Proof.
  intros st f f' x m t v H. 
  unfold update in H. remember (updates (store_of f) x v) as b.
  destruct b; inversion H; subst; simpl. clear H.
  revert m t s Heqb. destruct f; simpl in *.
  functional induction (updates s0 x v); intros;
  match goal with
  | [H: Some ?s = _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_typed_value_in_store ?st _ |- _] => inversion H; subst
  end;
  constructor; crush;eauto.
  
  symmetry in e0; rewrite (beq_nat_eq _ _ e0) in *.
  rewrite H0 in H3; inversion H3; subst.
  exists x0 x1; crush;eauto.
Qed.

Ltac apply_storeUpdate_with_typed_value_preserve_typed_store :=
  match goal with
  | [H1: update ?f ?x ?v = Some ?f',
     H2: well_typed_value_in_store ?st _,
     H3: fetch_var_x ?x ?st = Some (?m, ?t),
     H4: well_typed_value ?st ?t ?v |- _] =>
      specialize (storeUpdate_with_typed_value_preserve_typed_store _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intros HZ
  end.


Lemma updateG_with_typed_value_preserve_typed_stack: forall st s s' x m t v,
  updateG s x v = Some s' ->
    well_typed_value_in_stack st s ->
      fetch_var_x x st = Some (m, t) ->
        well_typed_value st t v ->    
          well_typed_value_in_stack st s'.
Proof.
  intros st s s' x m t v; revert s' m t.
  functional induction (updateG s x v); crush;eauto;
  match goal with
  | [H: well_typed_value_in_stack ?st _ |- _] => inversion H; subst
  end;
  constructor; crush;eauto.
  apply_storeUpdate_with_typed_value_preserve_typed_store; auto.
Qed.

Ltac apply_updateG_with_typed_value_preserve_typed_stack :=
  match goal with
  | [H1: updateG ?s ?x ?v = Some ?s',
     H2: well_typed_value_in_stack ?st ?s,
     H3: fetch_var_x ?x ?st = Some (?m, ?t),
     H4: well_typed_value ?st ?t ?v |- _] =>
      specialize (updateG_with_typed_value_preserve_typed_stack _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma updated_array_select_eq: forall a i v,
  array_select (updateIndexedComp a i v) i = Some v.
Proof.
  induction a; crush;eauto.
  assert (HA: Zeq_bool i i = true).
  apply Zeq_is_eq_bool; auto.
  rewrite HA; auto.
  remember (Zeq_bool a1 i) as bx.
  destruct bx; crush;eauto; rewrite <- Heqbx; auto.
Qed.

Lemma updated_record_select_eq: forall r f v,
  record_select (updateSelectedComp r f v) f = Some v.
Proof.
  induction r; crush;eauto.
  rewrite <- beq_nat_refl; auto.
  remember (beq_nat a0 f) as bx.
  destruct bx; crush;eauto; rewrite <- Heqbx; auto.
Qed.

Lemma updated_array_select: forall a i v i1 v1,
  array_select (updateIndexedComp a i v) i1 = Some v1 ->
    i = i1 \/ (Zeq_bool i i1 = false /\ array_select a i1 = Some v1).
Proof.
  induction a; crush;eauto.
  remember (Zeq_bool i i1) as b.
  destruct b; inversion H.
  symmetry in Heqb; rewrite (Zeq_bool_eq _ _ Heqb); auto.
  
  remember (Zeq_bool a1 i1) as b1;
  remember (Zeq_bool a1 i) as b2;
  destruct b1, b2; subst;
  repeat progress match goal with
  | [H: true = Zeq_bool _ _ |- _] => 
      symmetry in H; specialize (Zeq_bool_eq _ _ H); clear H; crush;eauto
  end.
  right. 
  assert(HA: Zeq_bool i i1 = Zeq_bool i1 i).
    clear. remember (Zeq_bool i i1) as b1. remember (Zeq_bool i1 i) as b2.
    destruct b1, b2; auto;
    match goal with
    | [H: true = Zeq_bool _ _ |- _] => 
        symmetry in H; specialize (Zeq_bool_eq _ _ H); clear H; crush;eauto
    end.
    assert (HA1: Zeq_bool i1 i1 = true). apply Zeq_is_eq_bool; auto. auto.
    apply Zeq_is_eq_bool; auto.
  assert(HA1: Zeq_bool i1 i1 = true). apply Zeq_is_eq_bool; auto. 
  rewrite HA1 in H; inversion H; subst. auto.
  right. rewrite <- Heqb1 in H; crush;eauto.
  unfold array_select in H.
  rewrite <- Heqb1 in H. fold array_select in H.
  specialize (IHa _ _ _ _ H); auto.
Qed.

Ltac apply_updated_array_select :=
  match goal with
  | [H: array_select (updateIndexedComp ?a ?i ?v) ?i1 = Some ?v1 |- _] =>
      specialize (updated_array_select _ _ _ _ _ H); 
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma updated_record_select: forall r f v f1 v1,
  record_select (updateSelectedComp r f v) f1 = Some v1 ->
    f = f1 \/ (beq_nat f f1 = false /\ record_select r f1 = Some v1).
Proof.
  induction r; crush;eauto.
  remember (beq_nat f f1) as b.
  destruct b; inversion H.
  symmetry in Heqb; rewrite (beq_nat_true _ _ Heqb); auto.
  
  remember (beq_nat a0 f1) as b1;
  remember (beq_nat a0 f) as b2;
  destruct b1, b2; subst;
  repeat progress match goal with
  | [H: true = beq_nat _ _ |- _] => 
      symmetry in H; specialize (beq_nat_true _ _ H); clear H; crush;eauto
  end.
  right. 
  assert(HA: beq_nat f f1 = beq_nat f1 f).
    clear. remember (beq_nat f f1) as b1. remember (beq_nat f1 f) as b2.
    destruct b1, b2; auto;
    match goal with
    | [H: true = beq_nat _ _ |- _] => 
        symmetry in H; specialize (beq_nat_true _ _ H); clear H; crush;eauto
    end.
    apply beq_nat_refl; auto.
    
    assert (HA1: true = beq_nat f f). apply beq_nat_refl; auto. auto.
  rewrite <- beq_nat_refl in H; inversion H; subst; auto.
  right. rewrite <- Heqb1 in H; auto.
  unfold record_select in H.
  rewrite <- Heqb1 in H. fold record_select in H.
  specialize (IHr _ _ _ _ H); auto.
Qed.

Ltac apply_updated_record_select :=
  match goal with
  | [H: record_select (updateSelectedComp ?r ?f ?v) ?f1 = Some ?v1 |- _] => 
      specialize (updated_record_select _ _ _ _ _ H); 
      let HZ := fresh "HZ" in intros HZ
  end.
  
Lemma arrayUpdate_with_typed_value_preserve_typed_array: forall st t t0 arrObj a a1 i v a_ast_num tn tm l u,
  well_typed_value st (Array_Type t) arrObj ->
  arrObj = ArrayV a \/ arrObj = Undefined ->
  arrayUpdate arrObj i v = Some (ArrayV a1) ->
  fetch_type_x t st = Some (Array_Type_Declaration_X a_ast_num tn tm t0) ->
  well_typed_value st t0 v ->
  extract_array_index_range_x st t (Range_X l u) ->
  do_range_checks (Do_Range_Check :: nil) i l u (Normal (Int i)) ->
  well_typed_value st (Array_Type t) (ArrayV a1).
Proof.
  intros.
  unfold arrayUpdate in H1; crush;eauto.
- inversion H5; subst.
  apply TV_Array_Type with (ast_num:=a_ast_num) (tid:=tn) (tm:=tm) (typ:=t0) (l:=l) (u:=u); crush;eauto.
  apply_updated_array_select; crush;eauto.
  inversion H; subst. 
  apply_extract_array_index_range_x_unique; subst.
  specialize (H13 _ _ H8); crush;eauto.

  apply_updated_array_select; crush;eauto.
  rewrite updated_array_select_eq in H1; inversion H1; subst; auto.
  inversion H; subst.
  specialize (H13 _ _ H8); crush;eauto.
- apply TV_Array_Type with (ast_num:=a_ast_num) (tid:=tn) (tm:=tm) (typ:=t0) (l:=l) (u:=u); crush;eauto;
  inversion H5; subst;
  remember (Zeq_bool i i0) as b;
  destruct b; inversion H0; subst; auto;
  symmetry in Heqb;
  rewrite <- (Zeq_bool_eq _ _ Heqb); auto.
Qed.

Ltac apply_arrayUpdate_with_typed_value_preserve_typed_array :=
  match goal with
  | [H1: well_typed_value ?st (Array_Type ?t) ?arrObj,
     H2: ?arrObj = ArrayV ?a \/ ?arrObj = Undefined,
     H3: arrayUpdate ?arrObj ?i ?v = Some (ArrayV ?a1),
     H4: fetch_type_x ?t ?st = Some (Array_Type_Declaration_X ?a_ast_num ?tn ?tm ?t0),
     H5: well_typed_value ?st ?t0 ?v,
     H6: extract_array_index_range_x ?st ?t (Range_X ?l ?u),
     H7: do_range_checks (Do_Range_Check :: nil) ?i ?l ?u (Normal (Int ?i)) |- _] =>
        specialize (arrayUpdate_with_typed_value_preserve_typed_array _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
        let HZ := fresh "HZ" in intros HZ
  end.

Lemma recordUpdate_with_typed_value_preserve_typed_array: forall st t t0 recObj r r1 f v r_ast_num tn fields,
  well_typed_value st (Record_Type t) recObj ->
  recObj = RecordV r \/ recObj = Undefined ->
  recordUpdate recObj f v = Some (RecordV r1) ->
  fetch_type_x t st = Some (Record_Type_Declaration_X r_ast_num tn fields) ->
  record_field_type fields f = Some t0 ->
  well_typed_value st t0 v ->
  well_typed_value st (Record_Type t) (RecordV r1).
Proof.
  intros.
  unfold recordUpdate in H1; crush;eauto.
- apply TV_Record_Type with (ast_num:=r_ast_num) (tid:=tn) (fields:=fields); auto; intros.
  apply_updated_record_select; crush;eauto.
  
  rewrite updated_record_select_eq in H0; inversion H0; subst.
  exists t0; auto.

  inversion H; subst. rewrite H2 in H9; inversion H9; subst.
  specialize (H10 _ _ H6); auto.
- apply TV_Record_Type with (ast_num:=r_ast_num) (tid:=tn) (fields:=fields); crush;eauto.
  remember (beq_nat f f0) as b.
  destruct b; inversion H0; subst.
  symmetry in Heqb; rewrite <- (beq_nat_true _ _ Heqb).
  exists t0; auto.
Qed.

Ltac apply_recordUpdate_with_typed_value_preserve_typed_array :=
  match goal with
  | [H1: well_typed_value ?st (Record_Type ?t) ?recObj,
     H2: ?recObj = RecordV ?r \/ ?recObj = Undefined,
     H3: recordUpdate ?recObj ?f ?v = Some (RecordV ?r1),
     H4: fetch_type_x ?t ?st = Some (Record_Type_Declaration_X ?r_ast_num ?tn ?fields),
     H5: record_field_type ?fields ?f = Some ?t0,
     H6: well_typed_value ?st ?t0 ?v |- _] =>
      specialize (recordUpdate_with_typed_value_preserve_typed_array _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma storeUpdate_with_typed_value_preserve_typed_stack: forall st0 st x0 x s s' t v,
  storeUpdate_x st s x v (Normal s') ->
    compile2_flagged_symbol_table st0 st ->
      compile2_flagged_name st0 x0 x ->
        well_typed_symbol_table st ->
          well_typed_value_in_stack st s ->
            well_typed_name_x st x ->
              fetch_exp_type_x (name_astnum_x x) st = Some t ->
                well_typed_value st t v -> 
                  well_typed_value_in_stack st s'.
Proof.
  intros st0 st x0 x s s' t v H.
  remember (Normal s') as sx.
  revert st0 x0 t s' Heqsx.
  induction H; intros;
  match goal with
  | [H: _ = Normal ?s' |- _] => inversion H; subst
  end.
- (* SU_Identifier_X *)
  inversion H4; subst.
  simpl in H5.
  rewrite H5 in H10; inversion H10; subst.
  apply_updateG_with_typed_value_preserve_typed_stack; auto.
- (* SU_Indexed_Component_X *)
  (* first, invert on well_typed_name_x; second, invert on compile2_flagged_name *)
  inversion H11; subst.
  inversion H8; subst. simpl in *.

  assert(HA: well_typed_value st (Array_Type t') (ArrayV a1)). 
    apply_well_typed_stack_infer.
    apply_eval_name_well_typed_value.
    repeat progress match goal with
    | [H1: fetch_exp_type_x ?x ?st = _, H2: fetch_exp_type_x ?x ?st = _ |- _] =>
        rewrite H1 in H2; inversion H2; subst
    end.
    rewrite exp_updated_exterior_checks in H4.
    apply_arrayUpdate_with_typed_value_preserve_typed_array; auto.
  specialize (IHstoreUpdate_x _ _ _ _ H14 H7 H27 H9 H10 H19 H23 HA); auto.
- (* SU_Selected_Component_X *)
  (* first, invert on well_typed_name_x; second, invert on compile2_flagged_name *)
  inversion H7; subst.
  inversion H4; subst. simpl in *.

  assert(HA: well_typed_value st (Record_Type t') (RecordV r1)). 
    apply_well_typed_stack_infer.
    apply_eval_name_well_typed_value.
    repeat progress match goal with
    | [H1: fetch_exp_type_x ?x ?st = _, H2: fetch_exp_type_x ?x ?st = _ |- _] =>
        rewrite H1 in H2; inversion H2; subst
    end.
    apply_recordUpdate_with_typed_value_preserve_typed_array; auto.

  specialize (IHstoreUpdate_x _ _ _ _ H10 H3 H14 H5 H6 H15 H18 HA); auto.
Qed.

Ltac apply_storeUpdate_with_typed_value_preserve_typed_stack :=
  match goal with
  | [H1: storeUpdate_x ?st ?s ?x ?v (Normal ?s'),
     H2: compile2_flagged_symbol_table ?st0 ?st,
     H3: compile2_flagged_name ?st0 ?x0 ?x,
     H4: well_typed_symbol_table ?st,
     H5: well_typed_value_in_stack ?st ?s,
     H6: well_typed_name_x ?st ?x,
     H7: fetch_exp_type_x (name_astnum_x ?x) ?st = Some ?t,
     H8: well_typed_value ?st ?t ?v |- _] =>
      specialize (storeUpdate_with_typed_value_preserve_typed_stack _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma push_value_in_range_preserve_typed_store: forall st f x m t l u v,
  well_typed_value_in_store st (snd f) ->
    fetch_var_x x st = Some (m, t) ->
      extract_subtype_range_x st t (Range_X l u) -> 
        do_range_check v l u (Normal (Int v)) -> 
          well_typed_value_in_store st (snd (push f x (Int v))).
Proof.
  intros.
  constructor; auto.
  exists m t; crush;eauto.
  inversion H2; subst.
  destruct t;
  inversion H1; crush;eauto.
  apply TV_Subtype with (l:=l) (u:=u); auto.
  apply TV_Derived_Type with (l:=l) (u:=u); auto.
  apply TV_Integer_Type with (l:=l) (u:=u); auto.
Qed.

Ltac apply_push_value_in_range_preserve_typed_store :=
  match goal with
  | [H1: well_typed_value_in_store ?st _,
     H2: fetch_var_x ?x ?st = Some (?m, ?t),
     H3: extract_subtype_range_x ?st ?t (Range_X ?l ?u),
     H4: do_range_check ?v ?l ?u (Normal (Int ?v)) |- _] =>
      specialize (push_value_in_range_preserve_typed_store _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma push_typed_value_preserve_typed_store: forall st f x m t t' v,
  well_typed_symbol_table st ->
    well_typed_value_in_store st (snd f) ->
      fetch_var_x x st = Some (m, t) ->
        is_range_constrainted_type t = false ->
          well_typed_value st t' v ->
            type_match t' t = true ->
              well_typed_value_in_store st (snd (push f x v)).
Proof.
  intros.
  constructor; auto.
  exists m t; crush;eauto.
  inversion H; subst.
  inversion H5; subst.
  destruct t; inversion H2; crush;eauto;
  destruct t'; inversion H4; crush;eauto;
  inversion H3; crush;eauto;
  match goal with
  | [ |- well_typed_value _ _ Undefined ] => constructor
  | [H: beq_nat _ _ = _ |- _] => symmetry in H; rewrite <- (beq_nat_eq _ _ H); auto
  | [H1: forall (t : type) (l u : Z),
       extract_subtype_range_x ?st t (Range_X l u) ->
       sub_bound (Interval l u) int32_bound true,
     H2: extract_subtype_range_x ?st ?t (Range_X ?l ?u) |- _] =>  
      specialize (H1 _ _ _ H2)
  | _ => idtac
  end;
  apply_In_Bound_SubBound_Trans; constructor; auto.
Qed.

Ltac apply_push_typed_value_preserve_typed_store :=
  match goal with
  | [H1: well_typed_symbol_table ?st,
     H2: well_typed_value_in_store ?st _,
     H3: fetch_var_x ?x ?st = Some (?m, ?t),
     H4: is_range_constrainted_type ?t = false,
     H5: well_typed_value ?st ?t' ?v,
     H6: type_match ?t' ?t = true |- _] => 
      specialize (push_typed_value_preserve_typed_store _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * copy_in_preserve_typed_store *)

Lemma copy_in_preserve_typed_store: forall st st' s f f' params params' args args',
  copy_in_x st' s f params' args' (Normal f') ->
  (* /////// *)
  compile2_flagged_symbol_table st st' ->
  compile2_flagged_args st params args args' ->
  compile2_flagged_parameter_specifications params params' ->
  (* /////// *)
  well_typed_symbol_table st' ->
  well_typed_value_in_stack st' s ->
  well_typed_value_in_store st' (snd f) ->
  well_typed_exps_x st' args' ->
  well_typed_params_x st' params' ->
  well_typed_args_x st' args' params' ->
  (* /////// *)
  well_typed_value_in_store st' (snd f').
Proof.
  intros st st' s f f' params params' args args' H. 
  remember (Normal f') as fx; revert st params args f' Heqfx.
  induction H; intros;
  match goal with
  | [H: _ = Normal ?f' |- _] => inversion H; crush;eauto
  end.
- (* Copy_In_Mode_In_NoRangeCheck_X *)
  inversion H10; subst;
  inversion H11; subst;
  inversion H12; subst.
  inversion H6; subst.

  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  assert(HZ1: (parameter_subtype_mark param0) = (parameter_subtype_mark_x param)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  
  inversion H5; subst;
  repeat progress match goal with
  | [H1: parameter_mode ?p = parameter_mode_x ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_x ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H
  | [H: parameter_subtype_mark ?x = parameter_subtype_mark_x ?y |- _] => rewrite H in *
  | _ => idtac
  end.
  specialize (IHcopy_in_x _ _ _ _ H13 H4 H31 H21 H7 H8).
  apply IHcopy_in_x; auto.  
  assert(HA: well_typed_value st t v). 
    apply_well_typed_stack_infer.
    apply_eval_expr_well_typed_value; crush;eauto.
  apply_push_typed_value_preserve_typed_store; auto.
- (* Copy_In_Mode_In_Range_X *)
  inversion H12; subst;
  inversion H13; subst;
  inversion H14; subst.
  inversion H8; subst.

  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  assert(HZ1: (parameter_subtype_mark param0) = (parameter_subtype_mark_x param)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  
  inversion H7; subst;
  repeat progress match goal with
  | [H1: parameter_mode ?p = parameter_mode_x ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_x ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H
  | [H: parameter_subtype_mark ?x = parameter_subtype_mark_x ?y |- _] => rewrite H in *
  | _ => idtac
  end.
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  specialize (IHcopy_in_x _ _ _ _ H15 H6 H33 H23 H9 H10).
  apply IHcopy_in_x; auto.
  assert(HA: well_typed_value st t (Int v)). 
    apply_well_typed_stack_infer.  
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H0); intro HZ10.
    apply_well_typed_exp_preserve.
    replace (expression_astnum_x
             (update_exterior_checks_exp arg_flagged (Do_Range_Check :: nil))) with 
            (expression_astnum_x arg_flagged) in H24.
    apply_eval_expr_well_typed_value; crush;eauto. 
    clear. destruct arg_flagged; auto.
  apply_push_value_in_range_preserve_typed_store; auto.
- (* Copy_In_Mode_InOut_NoRange_X *)
  inversion H10; subst;
  inversion H11; subst;
  inversion H12; subst.
  inversion H6; subst.

  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  assert(HZ1: (parameter_subtype_mark param0) = (parameter_subtype_mark_x param)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  
  inversion H5; subst;
  repeat progress match goal with
  | [H1: parameter_mode ?p = parameter_mode_x ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_x ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1
  | [H: List.In _ (name_exterior_checks (update_exterior_checks_name _ _)) -> False |- _] =>
      rewrite name_updated_exterior_checks in H; crush;eauto
  | [H: parameter_subtype_mark ?x = parameter_subtype_mark_x ?y |- _] => rewrite H in *
  | _ => idtac
  end;
  specialize (IHcopy_in_x _ _ _ _ H13 H4 H34 H21 H7 H8);
  apply IHcopy_in_x; auto.  
  assert(HA: well_typed_value st t v). 
    apply_well_typed_stack_infer.
    inversion H16; subst.
    apply_eval_name_well_typed_value; crush;eauto.
  apply_push_typed_value_preserve_typed_store; auto.    
  assert(HA: well_typed_value st t v). 
    apply_well_typed_stack_infer.
    specialize (eval_name_ex_cks_stripped _ _ _ _ _ H0); intro HZ10.
    inversion H16; subst.
    apply_well_typed_name_preserve.
    replace (name_astnum_x
             (update_exterior_checks_name n_flagged (Do_Range_Check_On_CopyOut :: nil))) with 
            (name_astnum_x n_flagged) in H26.
    apply_eval_name_well_typed_value; crush;eauto. 
    clear. destruct n_flagged; auto.
  apply_push_typed_value_preserve_typed_store; auto.  
- (* Copy_In_Mode_InOut_Range_X *)  
  inversion H12; subst;
  inversion H13; subst;
  inversion H14; subst.
  inversion H8; subst.

  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  assert(HZ1: (parameter_subtype_mark param0) = (parameter_subtype_mark_x param)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  
  inversion H7; subst;
  repeat progress match goal with
  | [H1: parameter_mode ?p = parameter_mode_x ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_x ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1
  | [H: List.In _ (name_exterior_checks (update_exterior_checks_name _ _)) -> False |- _] =>
      rewrite name_updated_exterior_checks in H; crush;eauto
  | [H: parameter_subtype_mark ?x = parameter_subtype_mark_x ?y |- _] => rewrite H in *
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end;
  specialize (IHcopy_in_x _ _ _ _ H15 H6 H36 H23 H9 H10);
  apply IHcopy_in_x; auto.

  assert(HA: well_typed_value st t (Int v)). 
    apply_well_typed_stack_infer.
    specialize (eval_name_ex_cks_stripped _ _ _ _ _ H0); intro HZ10.
    inversion H18; subst.
    apply_well_typed_name_preserve.
    replace (name_astnum_x
             (update_exterior_checks_name n_flagged (Do_Range_Check :: nil))) with 
            (name_astnum_x n_flagged) in H27.
    apply_eval_name_well_typed_value; crush;eauto. 
    clear. destruct n_flagged; auto.
  apply_push_value_in_range_preserve_typed_store; auto.

  assert(HA: well_typed_value st t (Int v)). 
    apply_well_typed_stack_infer.
    specialize (eval_name_ex_cks_stripped _ _ _ _ _ H0); intro HZ10.
    inversion H18; subst.
    apply_well_typed_name_preserve.
    replace (name_astnum_x
             (update_exterior_checks_name n_flagged (Do_Range_Check :: Do_Range_Check_On_CopyOut :: nil))) with 
            (name_astnum_x n_flagged) in H27.
    apply_eval_name_well_typed_value; crush;eauto. 
    clear. destruct n_flagged; auto.
  apply_push_value_in_range_preserve_typed_store; auto.
- (* Copy_In_Mode_Out_X *)
  inversion H8; subst;
  inversion H9; subst;
  inversion H10; subst;
  inversion H4; subst.  
  
  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  assert(HZ1: (parameter_subtype_mark param0) = (parameter_subtype_mark_x param)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.

  inversion H3; subst;
  repeat progress match goal with
  | [H1: parameter_mode ?p = parameter_mode_x ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_x ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1
  | [H: parameter_subtype_mark ?x = parameter_subtype_mark_x ?y |- _] => rewrite H in *
  | _ => idtac
  end; simpl in *;
  specialize (IHcopy_in_x _ _ _ _ H11 H2 H31 H19 H5 H6);
  apply IHcopy_in_x; auto;
  apply_well_typed_store_updated_by_undefined_value'; auto.
Qed.

Ltac apply_copy_in_preserve_typed_store :=
  match goal with
  | [H1: copy_in_x ?st' ?s ?f ?params' ?args' (Normal ?f'),
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: compile2_flagged_args ?st ?params ?args ?args',
     H4: compile2_flagged_parameter_specifications ?params ?params',
     H5: well_typed_symbol_table ?st',
     H6: well_typed_value_in_stack ?st' ?s,
     H7: well_typed_value_in_store ?st' _,
     H8: well_typed_exps_x ?st' ?args',
     H9: well_typed_params_x ?st' ?params',
     H10: well_typed_args_x ?st' ?args' ?params' |- _] =>
      specialize (copy_in_preserve_typed_store _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma well_typed_value_in_store_fetch: forall st f x v m t,
  well_typed_value_in_store st (snd f) ->
    fetch x f = Some v ->
      fetch_var_x x st = Some (m, t) ->
        well_typed_value st t v.
Proof.
  intros.
  unfold fetch in H0.
  apply_well_typed_store_infer.
  inversion HZ; subst.
  specialize (H2 _ _ H0); crush;eauto.
Qed.

Ltac apply_well_typed_value_in_store_fetch :=
  match goal with
  | [H1: well_typed_value_in_store ?st (snd ?f),
     H2: fetch ?x ?f = Some ?v,
     H3: fetch_var_x ?x ?st = Some (?m, ?t) |- _] =>
      specialize (well_typed_value_in_store_fetch _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * copy_out_preserve_typed_stack *)
Lemma copy_out_preserve_typed_stack: forall st st' s s' f params params' args args',
  copy_out_x st' s f params' args' (Normal s') ->
  (* /////// *)
  compile2_flagged_symbol_table st st' ->
  compile2_flagged_args st params args args' ->
  compile2_flagged_parameter_specifications params params' ->
  (* /////// *)
  well_typed_symbol_table st' ->
  well_typed_value_in_stack st' s ->
  well_typed_value_in_store st' (snd f) ->
  well_typed_exps_x st' args' ->
  well_typed_params_x st' params' ->
  well_typed_args_x st' args' params' ->
  (* /////// *)
  well_typed_value_in_stack st' s'.
Proof.
  intros st st' s s' f params params' args args' H. 
  remember (Normal s') as sx. revert st s' params args Heqsx.
  induction H; intros;
  match goal with
  | [H: _ = Normal ?s |- _] => inversion H; subst; auto
  end.
- (* Copy_Out_Mode_Out_NoRange_X *)
  inversion H10; subst;
  inversion H11; subst;
  inversion H12; subst;
  inversion H6; subst.

  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  assert(HZ1: (parameter_subtype_mark param0) = (parameter_subtype_mark_x param)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  
  inversion H5; subst;
  rewrite HZ in *;
  match goal with
  | [H1: parameter_mode_x ?a = _ ,
     H2: parameter_mode_x ?a = _ |- _] => rewrite H2 in H1; inversion H1 
  | [H1: parameter_mode_x ?a = In ,
     H2: parameter_mode_x ?a = Out \/ parameter_mode_x ?a = In_Out |- _] => 
      rewrite H1 in H2; clear - H2; crush;eauto
  | _ => idtac
  end; simpl in *;
  match goal with
  | [H: ~ List.In ?x (name_exterior_checks (update_exterior_checks_name _ (?x :: _))) |- _] =>
      rewrite name_updated_exterior_checks in H; clear - H; crush;eauto
  | [H: ~ List.In ?x (name_exterior_checks (update_exterior_checks_name _ (_ :: ?x :: _))) |- _] =>
      rewrite name_updated_exterior_checks in H; clear - H; crush;eauto
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: fetch_exp_type ?e ?st = _,
     H3: fetch_exp_type_x ?e ?st' = _ |- _] =>
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ;
      rewrite H3 in HZ; inversion HZ; subst
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: well_typed_exp_x ?st (E_Name_X _ _) |- _] => inversion H; subst; clear H
  | [H: fetch_exp_type_x _ _ = fetch_exp_type_x (name_astnum_x _) _ |- _] => rewrite H in *
  end;
  apply_well_typed_value_in_store_fetch;
  apply_value_well_typed_with_matched_type.

  specialize (IHcopy_out_x _ _ _ _ H13 H4 H34 H22 H7);
  apply IHcopy_out_x; auto.
  apply_storeUpdate_with_typed_value_preserve_typed_stack; auto. 

  specialize (IHcopy_out_x _ _ _ _ H13 H4 H35 H22 H7);
  apply IHcopy_out_x; auto. 
  apply_storeUpdate_with_typed_value_preserve_typed_stack; auto. 

  specialize (IHcopy_out_x _ _ _ _ H13 H4 H35 H22 H7);
  apply IHcopy_out_x; auto.
  apply_store_update_ex_cks_stripped.
  apply_well_typed_name_preserve.
  rewrite update_exterior_checks_name_astnum_eq in H23.
  apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
- (* Copy_Out_Mode_Out_Range_X *)
  inversion H13; subst;
  inversion H14; subst;
  inversion H15; subst;
  inversion H9; subst.

  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  assert(HZ1: (parameter_subtype_mark param0) = (parameter_subtype_mark_x param)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  
  inversion H8; subst;
  rewrite HZ in *;
  match goal with
  | [H1: parameter_mode_x ?a = _ ,
     H2: parameter_mode_x ?a = _ |- _] => rewrite H2 in H1; inversion H1 
  | [H1: parameter_mode_x ?a = In ,
     H2: parameter_mode_x ?a = Out \/ parameter_mode_x ?a = In_Out |- _] => 
      rewrite H1 in H2; clear - H2; crush;eauto
  | _ => idtac
  end; simpl in *;
  match goal with
  | [H: compile2_flagged_name ?st ?n ?n' |- _] => 
      specialize (name_exterior_checks_beq_nil _ _ _ H); 
      let HZ := fresh "HZ" in intros HZ; rewrite HZ in *
  | _ => idtac
  end;
  match goal with
  | [H: List.In ?x nil |- _] =>
      clear - H; crush;eauto
  | [H: List.In ?x (name_exterior_checks (update_exterior_checks_name _ _)) |- _] =>
      rewrite name_updated_exterior_checks in H; crush;eauto
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: fetch_exp_type ?e ?st = _,
     H3: fetch_exp_type_x ?e ?st' = _ |- _] =>
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ;
      rewrite H3 in HZ; inversion HZ; subst
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: well_typed_exp_x ?st (E_Name_X _ _) |- _] => inversion H; subst; clear H
  | [H: fetch_exp_type_x _ _ = fetch_exp_type_x (name_astnum_x _) _ |- _] => 
      rewrite update_exterior_checks_name_astnum_eq in H; rewrite H in *
  | [H1: fetch_exp_type_x (name_astnum_x _) _ = _,
     H2: fetch_exp_type_x (name_astnum_x _) _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  apply_store_update_ex_cks_stripped;
  apply_well_typed_name_preserve;
  apply_well_typed_value_in_store_fetch;
  apply_value_in_range_is_well_typed;
  [ specialize (IHcopy_out_x _ _ _ _ H16 H7 H37 H25 H10) |
    specialize (IHcopy_out_x _ _ _ _ H16 H7 H38 H25 H10) |
    specialize (IHcopy_out_x _ _ _ _ H16 H7 H38 H25 H10)
  ]; apply IHcopy_out_x; auto;
  apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
- (* Copy_Out_Mode_In_X *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  inversion H3; subst.

  assert(HZ: param0.(parameter_mode) = param.(parameter_mode_x)).
  match goal with
  | [H: compile2_flagged_parameter_specification ?param0 ?param |- _] => inversion H; crush;eauto
  end.
  
  inversion H2; subst;
  rewrite HZ in *;
  match goal with
  | [H1: parameter_mode_x ?a = _ ,
     H2: parameter_mode_x ?a = _ |- _] => rewrite H2 in H1; inversion H1 
  end;
  specialize (IHcopy_out_x _ _ _ _ H10 H1 H29 H19 H4);
  apply IHcopy_out_x; auto. 
Qed.

Ltac apply_copy_out_preserve_typed_stack :=
  match goal with
  | [H1: copy_out_x ?st' ?s ?f ?params' ?args' (Normal ?s'),
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: compile2_flagged_args ?st ?params ?args ?args',
     H4: compile2_flagged_parameter_specifications ?params ?params',
     H5: well_typed_symbol_table ?st',
     H6: well_typed_value_in_stack ?st' ?s,
     H7: well_typed_value_in_store ?st' _,
     H8: well_typed_exps_x ?st' ?args',
     H9: well_typed_params_x ?st' ?params',
     H10: well_typed_args_x ?st' ?args' ?params' |- _] =>
      specialize (copy_out_preserve_typed_stack _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10);
      let HZ := fresh "HZ" in intros HZ
  end.


(** * eval_declaration_preserve_typed_stack *)
Lemma eval_declaration_preserve_typed_store: forall st st' s f f' d d',
  eval_decl_x st' s f d' (Normal f') ->
    compile2_flagged_symbol_table st st' ->
      compile2_flagged_declaration st d d' ->
        (* /////// *)
        well_typed_symbol_table st' ->
          well_typed_value_in_stack st' s ->
            well_typed_value_in_store st' (snd f) ->
              well_typed_decl_x st' d' ->       
              (* /////// *)
                well_typed_value_in_store st' (snd f').
Proof.
  intros st st' s f f' d d' H; 
  remember (Normal f') as fx; revert st f' d Heqfx.
  induction H; intros;
  match goal with
  | [H: _ = Normal _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: compile2_flagged_declaration _ _ _, 
     H2: well_typed_decl_x _ _ |- _] => inversion H1; subst; inversion H2; subst
  end;
  match goal with
  | [H1: initialization_expression_x ?x = _,
     H2: initialization_expression_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end.
- (* D_Object_Declaration_X with no initialization*)
  apply_well_typed_store_updated_by_undefined_value'; auto.
- (* D_Object_Declaration_X with no range check *)
  inversion H3; subst;
  inversion H7; subst;
  match goal with
  | [H1: initialization_expression_x ?x = _,
     H2: initialization_expression_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  constructor; auto.
  exists m (object_nominal_subtype_x d); crush;eauto.
  match goal with
  | [H1: fetch_exp_type_x ?e st = _, H2: fetch_exp_type_x ?e st = _ |- _] =>
      rewrite H1 in H2; inversion H2; subst
  end.
  apply_well_typed_store_stack_merge'.
  apply_well_typed_stack_infer.
  match goal with
  | [H: compile2_flagged_object_declaration ?st ?o ?d |- _] => 
      inversion H; subst; simpl in *; crush;eauto
  end.

  apply_eval_expr_well_typed_value; crush;eauto.
  match goal with
  | [H1: fetch_exp_type_x ?e st = _, H2: fetch_exp_type_x ?e st = _ |- _] =>
      rewrite H1 in H2; inversion H2; subst; auto
  end.
  apply value_well_typed_with_matched_type with (t':=x0); auto.  
  rewrite type_match_ref; auto.

  rewrite exp_updated_exterior_checks in H1; inversion H1.
- (* D_Object_Declaration_X *)
  inversion H5; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expression_x ?x = _,
     H2: initialization_expression_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  constructor; auto.
  exists m0 (object_nominal_subtype_x d); crush;eauto.
  match goal with
  | [H1: fetch_exp_type_x ?e st = _, H2: fetch_exp_type_x ?e st = _ |- _] =>
      rewrite H1 in H2; inversion H2; subst
  end.
  apply_well_typed_store_stack_merge'.
  apply_well_typed_stack_infer.
  match goal with
  | [H: compile2_flagged_object_declaration ?st ?o ?d |- _] => 
      inversion H; subst; simpl in *; crush;eauto
  end.

  apply_eval_expr_well_typed_value; crush;eauto.
  match goal with
  | [H1: fetch_exp_type_x ?e st = _, H2: fetch_exp_type_x ?e st = _ |- _] =>
      rewrite H1 in H2; inversion H2; subst; auto
  end.
  apply value_well_typed_with_matched_type with (t':=x0); auto.  
  rewrite type_match_ref; auto.
  
  apply_well_typed_exp_preserve.
  specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H0); intros HZ3.
  apply_value_in_range_is_well_typed; auto.
- (* D_Seq_Declaration_X *)
  inversion H2; subst;
  inversion H6; subst.
  assert (HA: Normal f' = Normal f'). auto.
  specialize (IHeval_decl_x1 _ _ _ HA H1 H12 H3 H4 H5 H16);
  specialize (IHeval_decl_x2 _ _ _ H7 H1 H14 H3 H4 IHeval_decl_x1 H18); auto.
Qed.

Ltac apply_eval_declaration_preserve_typed_store :=
  match goal with
  | [H1: eval_decl_x ?st' ?s ?f ?d' (Normal ?f'),
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: compile2_flagged_declaration ?st ?d ?d',
     H4: well_typed_symbol_table ?st',
     H5: well_typed_value_in_stack ?st' ?s,
     H6: well_typed_value_in_store ?st' _,
     H7: well_typed_decl_x ?st' ?d' |- _] => 
      specialize (eval_declaration_preserve_typed_store _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intros HZ
  end.


(** * cut_until_preserve_typed_stack *)
Lemma cut_until_preserve_typed_stack: forall st s s' intact_s n,
  cut_until s n intact_s s' ->
    well_typed_value_in_stack st s ->
      well_typed_value_in_stack st intact_s /\ well_typed_value_in_stack st s'.
Proof.
  intros;
  induction H; crush;eauto.
- constructor.
- inversion H0; subst; crush;eauto. 
  constructor; auto.
- inversion H0; subst; crush;eauto.
Qed.

Ltac apply_cut_until_preserve_typed_stack :=
  match goal with
  | [H1: cut_until ?s ?n ?intact_s ?s',
     H2: well_typed_value_in_stack ?st ?s |- _] =>
      specialize (cut_until_preserve_typed_stack _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in 
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in 
      intros HZ; destruct HZ as [HZ1 HZ2]
  end.

(** * eval_statement_preserve_typed_stack *)
Lemma eval_statement_preserve_typed_stack: forall st st' s s' c c',
  eval_stmt_x st' s c' (Normal s') ->
    compile2_flagged_symbol_table st st' ->
      compile2_flagged_stmt st c c' ->
        well_typed_stack_and_symboltable st' s ->
          well_typed_statement_x st' c' ->
            well_typed_stack_and_symboltable st' s'.
Proof.
  intros st st' s s' c c' H.
  remember (Normal s') as sx; revert st s' c Heqsx.
  induction H; intros;
  match goal with
  | [H: _ = Normal _ |- _] => inversion H; subst; auto
  end.
- (* S_Assignment_X with no range check *)
  inversion H5; subst;
  inversion H3; subst;
  match goal with
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H
  | _ => idtac
  end.
  match goal with
  | [H: compile2_flagged_name ?st ?n ?n' |- _] =>
      rewrite (name_ast_num_eq _ _ _ H) in *
  end;
  match goal with
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: fetch_exp_type ?e ?st = ?t |- _] =>
      rewrite (symbol_table_exp_type_rel _ _ _ _ H1 H2) in *;
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2); let HZ := fresh "HZ" in intros HZ
  end.
  inversion H14; subst.
  rewrite <- type_match_ref in H15.
  inversion H4; subst. (*well_typed_stack_and_symboltable*)
  apply_well_typed_stack_infer.
  apply_eval_expr_well_typed_value; crush;eauto.
  match goal with
  | [H1: fetch_exp_type_x ?x ?st = _, H2: fetch_exp_type_x ?x ?st = _ |- _] =>
      rewrite H1 in H2; inversion H2; subst
  end.
  apply_value_well_typed_with_matched_type.
  apply_storeUpdate_with_typed_value_preserve_typed_stack.
  constructor; auto.
- (* S_Assignment_X with range check *)
  inversion H8; subst;
  inversion H6; subst;
  match goal with
  | [H: compile2_flagged_name ?st ?n ?n' |- _] =>
      rewrite (name_ast_num_eq _ _ _ H) in *
  end;
  match goal with
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: fetch_exp_type ?e ?st = ?t |- _] =>
      rewrite (symbol_table_exp_type_rel _ _ _ _ H1 H2) in *;
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2); let HZ := fresh "HZ" in intros HZ 
  end;
  inversion H1; subst;
  inversion H17; subst.

  specialize (range_constrainted_type_true _ _ _ _ H2); crush;eauto.
  
  inversion H7; subst. (*well_typed_stack_and_symboltable*)
  apply_well_typed_stack_infer.
  apply_well_typed_exp_preserve.
  rewrite update_exterior_checks_exp_astnum_eq in H16.
  specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); intros HZ3.
  apply_eval_expr_well_typed_value; crush;eauto.
  apply_value_in_range_is_well_typed.
  apply_storeUpdate_with_typed_value_preserve_typed_stack.
  constructor; auto.
- (* S_If_X true *)
  inversion H2; subst;
  inversion H4; subst.
  specialize (IHeval_stmt_x _ _ _ H5 H1 H13 H3 H15); auto.
- (* S_If_X false *)
  inversion H2; subst;
  inversion H4; subst.
  specialize (IHeval_stmt_x _ _ _ H5 H1 H14 H3 H16); auto.
- (* S_While_Loop *)
  inversion H3; subst;
  inversion H5; subst.
  assert (HA: Normal s1 = Normal s1). auto.
  specialize (IHeval_stmt_x1 _ _ _ HA H2 H13 H4 H14). 
  specialize (IHeval_stmt_x2 _ _ _ H6 H2 H3 IHeval_stmt_x1 H5); auto.
- (* S_Procedure_Call *)
  inversion H8; subst;
  inversion H10; subst.
  assert(HA: Normal ((n, locals_section ++ params_section) :: s3) = Normal ((n, locals_section ++ params_section) :: s3)). auto.  
  (* to get: compile2_flagged_stmt st0 c (procedure_statements_x pb) *)
  specialize (symbol_table_procedure_rel _ _ _ _ _ H7 H16); intros HZ1. destruct HZ1 as [pb1 [HZ1 HZ2]]. inversion HZ2; subst.
  repeat progress match goal with
  | [H1: fetch_proc_x ?x ?s = _, 
     H2: fetch_proc_x ?x ?s = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end.
  (* to get: well_typed_statement_x st (procedure_statements_x pb) *)
  match goal with
  | [H: well_typed_stack_and_symboltable _ _ |- _] => inversion H; subst
  end.
  match goal with
  | [H: well_typed_symbol_table _ |- _] => inversion H; subst
  end.
  match goal with
  | [H: well_typed_proc_declaration _ |- _] => inversion H; subst
  end.
  specialize (H23 _ _ _ HZ1). inversion H23; subst. simpl in *.
  (* to get: well_typed_stack st s1 *)
  assert(HA1: well_typed_value_in_stack st s1). apply_cut_until_preserve_typed_stack; auto.
  assert(HA2: well_typed_value_in_stack st intact_s). apply_cut_until_preserve_typed_stack; auto.
  (* to get: well_typed_store st f  after copy in *)
  assert(HA3_0: well_typed_value_in_store st (snd (newFrame n))). constructor.
  assert(HA3: well_typed_value_in_store st (snd f)).
  apply_copy_in_preserve_typed_store; auto.
  (* to get: well_typed_store st f  after declaration evaluation *)
  assert(HA4: well_typed_value_in_store st (snd f1)).
  apply_eval_declaration_preserve_typed_store; auto.
  (* to get: well_typed_stack st (f1 :: s1) *)
  specialize (well_typed_store_stack_merge' _ _ _ HA4 HA1); let HZ := fresh "HZ" in intros HZ.
  replace stmt_flagged with (procedure_statements_x (mkprocedure_body_x ast_num0 p0 params_flagged decls_flagged stmt_flagged)) in *; auto.
  combine_well_typed_stack_and_symboltable.  
  specialize (IHeval_stmt_x _ _ _ HA H7 H13 HZ0 H26).
  inversion IHeval_stmt_x; subst.
  specialize (well_typed_store_stack_split' _ _ _ H27); 
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in intros HZ1; destruct HZ1 as [HZ1 HZ2].
  specialize (well_typed_stacks_merge' _ _ _ HA2 HZ3); let HZ := fresh "HZ" in intros HZ.
  (* to get: well_typed_stack st s'  after copy out *)
  simpl in HZ4; apply_well_typed_store_split'. (* get: well_typed_value_in_store st params_section *)
  apply_copy_out_preserve_typed_stack; constructor; auto.
- (* S_Sequence_X *)
  inversion H2; subst;
  inversion H4; subst.
  assert (HA: Normal s1 = Normal s1). auto.
  specialize (IHeval_stmt_x1 _ _ _ HA H1 H10 H3 H9);
  specialize (IHeval_stmt_x2 _ _ _ H5 H1 H12 IHeval_stmt_x1 H13); auto.
Qed.

Ltac apply_eval_statement_preserve_typed_stack :=
  match goal with
  | [H1: eval_stmt_x ?st' ?s ?c' (Normal ?s'),
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: compile2_flagged_stmt ?st ?c ?c',
     H4: well_typed_stack_and_symboltable ?st' ?s,
     H5: well_typed_statement_x ?st' ?c' |- _] => 
      specialize (eval_statement_preserve_typed_stack _ _ _ _ _ _ H1 H2 H3 H4 H5);
      let HZ := fresh "HZ" in intros HZ
  end.


(********************************************************************)
(********************************************************************)

(*

(** * copy_in_preserve_typed_store *)
Lemma copy_in_preserve_typed_store: forall st s f params args f',
  well_typed_store st (snd f) ->
    copy_in_x st s f params args (Normal f') ->
      well_typed_store st (snd f').
Proof.
  admit.
Qed.


(** * copy_out_preserve_typed_stack *)
Lemma copy_out_preserve_typed_stack: forall st s f s' params args,
  well_typed_stack st s ->
    well_typed_store st (snd f) ->
      copy_out_x st s f params args (Normal s') ->
        well_typed_stack st s'.
Proof.
  admit.
Qed.

(*
  - assignment 
  - declaration

       eval_expr_x st (f :: s) e (Normal v)
  H1 : exp_exterior_checks e = nil
  H3 : compile2_flagged_symbol_table st0 st
  H5 : well_typed_stack st s
  H6 : well_typed_store st (snd f)
  H11 : compile2_flagged_object_declaration st0 o d
  ============================
   well_typed_store st (snd (push f (object_name_x d) v))

*)

(** * eval_declaration_preserve_typed_stack *)
Lemma eval_declaration_preserve_typed_store: forall st st' s fx f f' d d',
  eval_decl_x st' s f d' fx -> fx = (Normal f') ->
    compile2_flagged_symbol_table st st' ->
      compile2_flagged_declaration st d d' ->
        well_typed_stack st' s ->
          well_typed_store st' (snd f) ->
            well_typed_decl_x st' d' ->           
              well_typed_store st' (snd f').
Proof.
  intros st st' s fx f f' d d' H; revert st f' d;
  induction H; intros;
  match goal with
  | [H: _ = Normal _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: compile2_flagged_declaration _ _ _, 
     H2: well_typed_decl_x _ _ |- _] => inversion H1; subst; inversion H2; subst
  end;
  match goal with
  | [H1: initialization_expression_x ?x = _,
     H2: initialization_expression_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end.
- (* D_Object_Declaration_X with no initialization*)
  apply_well_typed_store_updated_by_undefined_value; auto.
- (* D_Object_Declaration_X with no range check *)
  inversion H4; subst;
  inversion H7; subst;
  match goal with
  | [H1: initialization_expression_x ?x = _,
     H2: initialization_expression_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  admit.
- (* D_Object_Declaration_X *)
  inversion H6; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expression_x ?x = _,
     H2: initialization_expression_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  admit.
- (* D_Seq_Declaration_X *)
  inversion H3; subst;
  inversion H6; subst.
  assert (HA: Normal f' = Normal f'). auto.
  specialize (IHeval_decl_x1 _ _ _ HA H2 H11 H4 H5 H10);
  specialize (IHeval_decl_x2 _ _ _ H7 H2 H13 H4 IHeval_decl_x1 H14); auto.
Qed.


(** * eval_statement_preserve_typed_stack *)
Lemma eval_statement_preserve_typed_stack: forall st st' sx s s' c c',
  eval_stmt_x st' s c' sx -> sx = (Normal s') -> (* it's to make the induction proof easy on eval_stmt_x *)
    compile2_flagged_symbol_table st st' ->
      compile2_flagged_stmt st c c' ->
        well_typed_stack st' s ->
          well_typed_statement_x st' c' ->
            well_typed_stack st' s'.
Proof.
  intros st st' sx s s' c c' H; revert st s' c;
  induction H; intros;
  match goal with
  | [H: _ = Normal _ |- _] => inversion H; subst; auto
  end.
- admit.
- admit.
- (* S_If_X true *)
  inversion H3; subst;
  inversion H5; subst.
  specialize (IHeval_stmt_x _ _ _ H6 H2 H13 H4 H15); auto.
- (* S_If_X false *)
  inversion H3; subst;
  inversion H5; subst.
  specialize (IHeval_stmt_x _ _ _ H6 H2 H14 H4 H16); auto.
- (* S_While_Loop *)
  inversion H4; subst;
  inversion H6; subst.
  assert (HA: Normal s1 = Normal s1). auto.
  specialize (IHeval_stmt_x1 _ _ _ HA H3 H13 H5 H14). 
  specialize (IHeval_stmt_x2 _ _ _ H7 H3 H4 IHeval_stmt_x1 H6); auto.
- (* S_Procedure_Call *)
  inversion H9; subst;
  inversion H11; subst.
  assert(HA: Normal ((n, locals_section ++ params_section) :: s3) = Normal ((n, locals_section ++ params_section) :: s3)). auto.  
  (* to get: compile2_flagged_stmt st0 c (procedure_statements_x pb) *)
  specialize (symbol_table_procedure_rel _ _ _ _ _ H8 H16); intros HZ1. destruct HZ1 as [pb1 [HZ1 HZ2]]. inversion HZ2; subst.
  repeat progress match goal with
  | [H1: fetch_proc_x ?x ?s = _, 
     H2: fetch_proc_x ?x ?s = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end.  
  (* to get: well_typed_statement_x st (procedure_statements_x pb) *)
  inversion H10; subst. specialize (H17 _ _ _ HZ1). inversion H17; subst. simpl in *.
  (* to get: well_typed_stack st s1 *)
  assert(HA1: well_typed_stack st s1). admit.
  assert(HA2: well_typed_stack st intact_s). admit.
  (* to get: well_typed_store st f1  after copy in *)
  assert(HA3: well_typed_store st (snd f1)). admit.
  (* to get: well_typed_stack st (f1 :: s1) *)
  specialize (well_typed_store_stack_merge _ _ _ HA3 HA1); let HZ := fresh "HZ" in intros HZ.
  replace stmt_flagged with (procedure_statements_x (mkprocedure_body_x ast_num0 p0 params_flagged decls_flagged stmt_flagged)) in *; auto.
  specialize (IHeval_stmt_x _ _ _ HA H8 H13 HZ H23).
  specialize (well_typed_store_stack_split _ _ _ IHeval_stmt_x); 
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in intros HZ1; destruct HZ1 as [HZ1 HZ2].
  specialize (well_typed_stacks_merge _ _ _ HA2 HZ0); let HZ := fresh "HZ" in intros HZ.
  (* to get: well_typed_stack st s'  after copy out *)
  admit.
- (* S_Sequence_X *)
  inversion H3; subst;
  inversion H5; subst.
  assert (HA: Normal s1 = Normal s1). auto.
  specialize (IHeval_stmt_x1 _ _ _ HA H2 H10 H4 H9);
  specialize (IHeval_stmt_x2 _ _ _ H6 H2 H12 IHeval_stmt_x1 H13); auto.
Qed.


*)






