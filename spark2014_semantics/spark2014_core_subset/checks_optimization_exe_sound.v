Require Export checks_optimization_exe.

(**********************************************)
(** *             helper lemmas               *)
(**********************************************)

Lemma extract_subtype_range_f_soundness: forall st t l u,
  extract_subtype_range_f st t = Some (Range_X l u) ->
    extract_subtype_range_x st t (Range_X l u).
Proof.
  intros;
  functional induction extract_subtype_range_f st t; crush;eauto;
  apply Extract_Range_X with (td:=td) (tn:=tn); auto.
Qed.

Lemma extract_subtype_range_f_completeness: forall st t l u,
  extract_subtype_range_x st t (Range_X l u) ->
    extract_subtype_range_f st t = Some (Range_X l u).
Proof.
  intros;
  destruct H; auto;
  unfold extract_subtype_range_f; crush;eauto.
Qed.

Lemma bound_of_type_f_soundness: forall st t bd,
  bound_of_type_f st t = Some bd ->
    bound_of_type st t bd.
Proof.
  intros;
  functional induction bound_of_type_f st t; crush;eauto;
  try constructor;
  try apply Bound_Of_Composite_Type with (t1:=t0); auto;
  apply extract_subtype_range_f_soundness; auto.
Qed.

Lemma bound_of_type_f_completeness: forall st t bd,
  bound_of_type st t bd ->
    bound_of_type_f st t = Some bd.
Proof.
  intros.
  induction H; auto. 
  specialize (extract_subtype_range_f_completeness _ _ _ _ H); intros.
  unfold bound_of_type_f.
  rewrite H0.
  destruct t; auto;
  match goal with
  | [H: extract_subtype_range_x _ _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: subtype_num _ = Some _ |- _] => inversion H; subst
  end.
  destruct H; crush;eauto.
Qed.

Lemma bound_of_array_component_type_f_soundness: forall st t bd,
  bound_of_array_component_type_f st t = Some bd ->
    bound_of_array_component_type st t bd.
Proof.
  intros;
  functional induction bound_of_array_component_type_f st t; crush;eauto;
  apply Array_Component_Value with (ast_num:=ast_num) (tn:=tn) (indexSubtypeMark:=indexSubtypeMark)
                                   (componentType:=componentType); auto;
  apply bound_of_type_f_soundness; auto.
Qed.

Lemma bound_of_array_component_type_f_completeness: forall st t bd,
  bound_of_array_component_type st t bd ->
    bound_of_array_component_type_f st t = Some bd.
Proof.
  intros;
  induction H; auto;
  specialize (bound_of_type_f_completeness _ _ _ H0); intro;
  unfold bound_of_array_component_type_f; crush;eauto.
Qed.

Lemma bound_of_record_field_type_f_soundness: forall st t f bd,
  bound_of_record_field_type_f st t f = Some bd ->
    bound_of_record_field_type st t f bd.
Proof.
  intros;
  functional induction bound_of_record_field_type_f st t f; crush;eauto;
  apply Record_Field_Value with (ast_num:=ast_num) (tn:=tn) (fields:=fields) (ft:=ft); auto;
  apply bound_of_type_f_soundness; auto.
Qed.

Lemma bound_of_record_field_type_f_completeness: forall st t f bd,
  bound_of_record_field_type st t f bd ->
    bound_of_record_field_type_f st t f = Some bd.
Proof.
  intros;
  induction H; auto;
  specialize (bound_of_type_f_completeness _ _ _ H1); intro;
  unfold bound_of_record_field_type_f; crush;eauto.
Qed.

Lemma in_bound_f_soundness: forall v bd b,
  in_bound_f v bd = Some b ->
    in_bound v bd b.
Proof.
  intros;
  functional induction in_bound_f v bd; crush;eauto;
  remember ((l <=? v)%Z && (v <=? u)%Z) as b;
  destruct b; constructor; auto.
Qed.

Lemma in_bound_f_completeness: forall v bd b,
  in_bound v bd b ->
    in_bound_f v bd = Some b.
Proof.
  intros;
  induction H; crush;eauto.  
Qed.

Lemma sub_bound_f_soundness: forall bd1 bd2 b,
  sub_bound_f bd1 bd2 = Some b ->
    sub_bound bd1 bd2 b.
Proof.
  intros.
  functional induction sub_bound_f bd1 bd2; crush;eauto.
  repeat progress constructor; auto. 
  constructor.
  remember ((u' <=? u)%Z && (u <=? v')%Z) as b1; destruct b1.
  right. constructor. destruct ((u' <=? v)%Z && (v <=? v')%Z); crush;eauto.
  left. constructor; auto.
Qed.

Lemma sub_bound_f_completeness: forall bd1 bd2 b,
  sub_bound bd1 bd2 b ->
    sub_bound_f bd1 bd2 = Some b.
Proof.
  intros;
  induction H; auto;
  unfold sub_bound_f.
  specialize (in_bound_f_completeness _ _ _ H); intro;
  specialize (in_bound_f_completeness _ _ _ H0); intro.
  rewrite H1, H2; auto.
  destruct H; specialize (in_bound_f_completeness _ _ _ H); intro;
  rewrite H0; auto.
  unfold in_bound_f.
  destruct ((u' <=? u)%Z && (u <=? v')%Z); auto.
Qed.

Lemma optimize_overflow_check_f_soundness: forall bd cks bd' cks',
  optimize_overflow_check_f bd cks = Some (bd', cks') ->
    optimize_overflow_check bd cks (bd', cks').
Proof.
  intros;
  functional induction optimize_overflow_check_f bd cks; crush;eauto;
  specialize (sub_bound_f_soundness _ _ _ e); intro;
  [destruct bd' | destruct bd]; inversion e;
  [ apply OOC_True; auto |
    apply OOC_False; auto 
  ].
Qed.

Lemma optimize_overflow_check_f_completeness: forall bd cks bd' cks',
  optimize_overflow_check bd cks (bd', cks') ->
    optimize_overflow_check_f bd cks = Some (bd', cks').
Proof.
  intros;
  induction H; auto;
  specialize (sub_bound_f_completeness _ _ _ H); intro;
  unfold optimize_overflow_check_f;
  [rewrite H1 | rewrite H0]; crush;eauto.
Qed.

Lemma optimize_range_check_f_soundness: forall e bd1 bd2 e',
  optimize_range_check_f e bd1 bd2 = Some e' ->
    optimize_range_check e bd1 bd2 e'.
Proof.
  intros;
  functional induction optimize_range_check_f e bd1 bd2; crush;eauto;
  specialize (sub_bound_f_soundness _ _ _ e0); intro;
  destruct bd1, bd2; inversion e0;
  [ apply ORC_True with (cks:=(remove_check_flag Do_Range_Check (exp_exterior_checks e))); auto |
    apply ORC_False; auto
  ].
Qed.

Lemma optimize_range_check_f_completeness: forall e bd1 bd2 e',
  optimize_range_check e bd1 bd2 e' ->
    optimize_range_check_f e bd1 bd2 = Some e'.
Proof.
  intros;
  induction H; auto;
  specialize (sub_bound_f_completeness _ _ _ H); intro;
  unfold optimize_range_check_f; crush;eauto.
Qed.

Lemma optimize_range_check_on_copy_out_f_soundness: forall e bd1 bd2 e',
  optimize_range_check_on_copy_out_f e bd1 bd2 = Some e' ->
    optimize_range_check_on_copy_out e bd1 bd2 e'.
Proof.
  intros;
  functional induction optimize_range_check_on_copy_out_f e bd1 bd2; crush;eauto;
  specialize (sub_bound_f_soundness _ _ _ e0); intro;
  destruct bd1, bd2; inversion e0;
  [ apply ORCOCO_True with (cks:=(remove_check_flag Do_Range_Check_On_CopyOut (exp_exterior_checks e))); auto |
    apply ORCOCO_False; auto
  ].  
Qed.

Lemma optimize_range_check_on_copy_out_f_completeness: forall e bd1 bd2 e',
  optimize_range_check_on_copy_out e bd1 bd2 e' ->
    optimize_range_check_on_copy_out_f e bd1 bd2 = Some e'.
Proof.
  intros;
  induction H; subst;
  specialize (sub_bound_f_completeness _ _ _ H); intro;
  unfold optimize_range_check_on_copy_out_f; crush;eauto.
Qed.

Lemma optimize_rtc_binop_f_soundness: forall op bd1 bd2 cks bd cks',
  optimize_rtc_binop_f op bd1 bd2 cks = Some (bd, cks') ->
    optimize_rtc_binop op bd1 bd2 cks (bd, cks').
Proof.
  intros;
  functional induction optimize_rtc_binop_f op bd1 bd2 cks; crush;eauto.

  specialize (optimize_overflow_check_f_soundness _ _ _ _ e4); intros.
  eapply O_RTC_Plus; crush;eauto.
  
  specialize (optimize_overflow_check_f_soundness _ _ _ _ e4); intros.
  eapply O_RTC_Minus; crush;eauto.  
  
  eapply O_RTC_Multiply; auto.
  
  eapply O_RTC_Divide_T; constructor; auto.
  eapply O_RTC_Divide_F; constructor; auto.
  destruct op; inversion y; constructor; crush;eauto. 
Qed.

Lemma optimize_rtc_binop_f_completeness: forall op bd1 bd2 cks bd cks',
  optimize_rtc_binop op bd1 bd2 cks (bd, cks') ->
    optimize_rtc_binop_f op bd1 bd2 cks = Some (bd, cks').
Proof.
  intros;
  induction H; auto;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => 
    specialize (optimize_overflow_check_f_completeness _ _ _ _ H); intros
  | [H: in_bound _ _ _ |- _] => 
    specialize (in_bound_f_completeness _ _ _ H); intros
  | _ => idtac 
  end;
  unfold optimize_rtc_binop_f;
  try rewrite H; try rewrite H0; 
  try rewrite H1; try rewrite H2; auto.
  destruct op; crush;eauto.
Qed.

Lemma optimize_rtc_unop_f_soundness: forall op bd cks bd' cks',
  optimize_rtc_unop_f op bd cks = Some (bd', cks') ->
    optimize_rtc_unop op bd cks (bd', cks').
Proof.
  intros;
  functional induction optimize_rtc_unop_f op bd cks; crush;eauto.
  specialize (optimize_overflow_check_f_soundness _ _ _ _ e3); intros.
  eapply O_RTC_Unary_Minus; crush;eauto.
  destruct op; inversion y;
  constructor; crush;eauto.
Qed.

Lemma optimize_rtc_unop_f_completeness: forall op bd cks bd' cks',
  optimize_rtc_unop op bd cks (bd', cks') ->
    optimize_rtc_unop_f op bd cks = Some (bd', cks').
Proof.
  intros;
  induction H; auto;
  unfold optimize_rtc_unop_f.
  specialize (optimize_overflow_check_f_completeness _ _ _ _ H1); intros.
  rewrite H, H0, H2; auto. 
  destruct op; crush;eauto.  
Qed.

Lemma extract_array_index_range_f_soundness: forall st t l u,
  extract_array_index_range_f st t = Some (Range_X l u) ->
    extract_array_index_range_x st t (Range_X l u).
Proof.
  intros;
  functional induction extract_array_index_range_f st t; crush;eauto;
  econstructor; crush;eauto.
Qed.

Lemma extract_array_index_range_f_completeness: forall st t l u,
  extract_array_index_range_x st t (Range_X l u) ->
    extract_array_index_range_f st t = Some (Range_X l u).
Proof.
  intros;
  induction H; auto;
  unfold extract_array_index_range_f;
  rewrite H, H0, H1, H2; auto.
Qed.


(**********************************************)
(** *          correctness proof              *)
(*  (1) soundness proof                       *)
(*  (2) completeness proof                    *)
(**********************************************)

Scheme expression_x_ind := Induction for expression_x Sort Prop 
                         with name_x_ind := Induction for name_x Sort Prop.

(** * optimize_literal_f *)
Lemma optimize_literal_f_soundness: forall l cks lbound cks',
  optimize_literal_f l cks = Some (lbound, cks') ->
    optimize_literal_x l cks (lbound, cks').
Proof.
  intros;
  functional induction optimize_literal_f l cks; crush;eauto;
  constructor; auto;
  apply optimize_overflow_check_f_soundness; auto.
Qed.

Lemma optimize_literal_f_completeness: forall l cks lbound cks',
  optimize_literal_x l cks (lbound, cks') ->
    optimize_literal_f l cks = Some (lbound, cks').
Proof.
  intros;
  induction H; auto;
  specialize (optimize_overflow_check_f_completeness _ _ _ _ H); intro;
  unfold optimize_literal_f;
  rewrite H0; auto.
Qed.


(** * optimize_expression_f *)
Lemma optimize_expression_f_soundness: forall e e' ebound st,
  optimize_expression_f st e = Some (e', ebound) ->
    optimize_expression_x st e (e', ebound).
Proof.
  apply (expression_x_ind
      (fun e: expression_x => forall (e' : expression_x) (ebound: bound) (st: symboltable_x),
        optimize_expression_f st e = Some (e', ebound) ->
        optimize_expression_x st e (e', ebound))
      (fun n: name_x => forall (n': name_x) (nbound: bound) (st: symboltable_x),
        optimize_name_f st n = Some (n', nbound) ->
        optimize_name_x st n (n', nbound))
      ); crush;eauto.
  - (*1. literal *)
    remember (optimize_literal_f l i) as x.
    destruct x; inversion H; subst.
    destruct p; inversion H; subst.
    constructor; auto.
    apply optimize_literal_f_soundness; auto.
  - (* 2. name *)
    remember (optimize_name_f st n) as x.
    destruct x; inversion H0; subst.
    destruct p; inversion H0; subst.
    constructor; auto.
  - (* 3. binary expression *)
    remember (optimize_expression_f st e) as x1;
    remember (optimize_expression_f st e0) as x2.
    destruct x1, x2; inversion H1; subst;
    destruct p; try destruct p0; inversion H1; subst.
    clear H3 H4.
    remember (optimize_rtc_binop_f b b0 b1 i) as y. 
    destruct y; inversion H1; subst.
    destruct p; inversion H1; subst.
    symmetry in Heqx1, Heqx2.
    specialize (H _ _ _ Heqx1); specialize (H0 _ _ _ Heqx2).
    eapply O_Binary_Operation_X; crush;eauto.
    apply optimize_rtc_binop_f_soundness; auto.
  - (* 4. unary expression *)
    remember (optimize_expression_f st e) as x.
    destruct x; inversion H0; subst.
    destruct p; inversion H0; subst.
    clear H2 H3.
    remember (optimize_rtc_unop_f u b i) as y.
    destruct y; inversion H0; subst.
    destruct p; inversion H0; subst.
    symmetry in Heqx. specialize (H _ _ _ Heqx).
    eapply O_Unary_Operation_X; crush;eauto.
    apply optimize_rtc_unop_f_soundness; auto.
  - (* 5. identifier *)
    remember (fetch_exp_type_x a st) as x.
    destruct x; inversion H; subst.
    remember (bound_of_type_f st t) as y.
    destruct y; inversion H; subst.
    eapply O_Identifier_X; crush;eauto.
    apply bound_of_type_f_soundness; auto.
  - (* 6. indexed component *)
    remember (optimize_name_f st n) as x1; 
    remember (optimize_expression_f st e) as x2.
    destruct x1, x2; inversion H1; subst;
    destruct p; try destruct p0; inversion H1; subst.
    clear H3 H4.
    destruct b0; inversion H1; subst. clear H3.
    remember (fetch_exp_type_x (name_astnum_x n) st) as y1.
    destruct y1; inversion H1; subst. clear H3.
    destruct t; inversion H1; subst. clear H3.
    remember (extract_array_index_range_f st t) as y2.
    destruct y2; inversion H1; subst. clear H3.
    destruct r; inversion H1; subst. clear H3.
    remember (optimize_range_check_f e1 (Interval l u) (Interval l0 u0)) as y3.
    destruct y3; inversion H1; subst. clear H3.
    remember (bound_of_array_component_type_f st t) as y4.
    destruct y4; inversion H1; subst.
    symmetry in Heqx1, Heqx2.
    specialize (H _ _ _ Heqx1); specialize (H0 _ _ _ Heqx2).
    apply O_Indexed_Component_X with (xBound:=b) (u:=l) (v:=u) (u':=l0) (v':=u0) (e':=e1) (t:=t); auto.
    apply extract_array_index_range_f_soundness; auto.
    apply optimize_range_check_f_soundness; auto.
    apply bound_of_array_component_type_f_soundness; auto.
  - (* 7. selected component *)
    remember (optimize_name_f st n) as x1;
    remember (fetch_exp_type_x (name_astnum_x n) st) as x2.
    destruct x1, x2; inversion H0; subst;
    destruct p; inversion H0; subst.
    clear H2 H3.
    destruct t; inversion H0; subst. clear H2.
    remember (bound_of_record_field_type_f st t i) as y.
    destruct y; inversion H0; subst. 
    symmetry in Heqx1; specialize (H _ _ _ Heqx1).
    eapply O_Selected_Component_X; crush;eauto.
    apply bound_of_record_field_type_f_soundness; auto.
Qed.

Lemma optimize_expression_f_completeness: forall e e' ebound st,
  optimize_expression_x st e (e', ebound) ->
    optimize_expression_f st e = Some (e', ebound).
Proof.
  apply (expression_x_ind
      (fun e: expression_x => forall (e' : expression_x) (ebound: bound) (st: symboltable_x),
        optimize_expression_x st e (e', ebound) ->
        optimize_expression_f st e = Some (e', ebound))
      (fun n: name_x => forall (n': name_x) (nbound: bound) (st: symboltable_x),
        optimize_name_x st n (n', nbound) ->
        optimize_name_f st n = Some (n', nbound))
      ); intros; simpl.
  - (*1. literal *)
    remember (E_Literal_X a l i e) as x.
    inversion H; subst;
    match goal with
    | [H: _ = E_Literal_X _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (optimize_literal_f_completeness _ _ _ _ H3); intro HZ;
    rewrite HZ; auto.
  - (*2. name *)
    remember (E_Name_X a n) as x.
    inversion H0; subst;
    match goal with
    | [H: _ = E_Name_X _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H4);
    rewrite H; auto.
  - (*3. binary expression *)
    remember (E_Binary_Operation_X a b e e0 i e1) as x.
    inversion H1; subst;
    match goal with
    | [H: _ = E_Binary_Operation_X _ _ _ _ _ _ |- _] => inversion H; subst
    end.
    specialize (H _ _ _ H4); 
    specialize (H0 _ _ _ H7).
    specialize (optimize_rtc_binop_f_completeness _ _ _ _ _ _ H8); intro HZ.
    rewrite H, H0; auto.
    rewrite HZ; auto.
  - (*4. unary expression *)
    remember (E_Unary_Operation_X a u e i e0) as x.
    inversion H0; subst;
    match goal with 
    | [H: _ = E_Unary_Operation_X _ _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H5).
    specialize (optimize_rtc_unop_f_completeness _ _ _ _ _ H6); intro HZ.
    rewrite H, HZ; auto.
  - (*5. identifier *)
    remember (E_Identifier_X a i e) as x.
    inversion H; subst;
    match goal with
    | [H: _ = E_Identifier_X _ _ _ |- _] => inversion H; subst 
    end.
    specialize (bound_of_type_f_completeness _ _ _ H5); intro HZ;
    rewrite H4, HZ; auto.     
  - (*6. indexed component *)
    remember (E_Indexed_Component_X a n e e0) as x.
    inversion H1; subst;
    match goal with 
    | [H: _ = E_Indexed_Component_X _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H4).
    specialize (H0 _ _ _ H5).
    rewrite H, H0, H6; auto.
    specialize (extract_array_index_range_f_completeness _ _ _ _ H7); intro HZ1.
    specialize (optimize_range_check_f_completeness _ _ _ _ H10); intro HZ2.
    specialize (bound_of_array_component_type_f_completeness _ _ _ H11); intro HZ3.
    rewrite HZ1, HZ2, HZ3; auto.
  - (*7. selected component *)
    remember (E_Selected_Component_X a n i e) as x.
    inversion H0; subst;
    match goal with 
    | [H: _ = E_Selected_Component_X _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H3).
    rewrite H, H6; auto.
    specialize (bound_of_record_field_type_f_completeness _ _ _ _ H7); intro HZ.
    rewrite HZ; auto.
Qed.

(** * optimize_name_f *)  
Lemma optimize_name_f_soundness: forall st n n' nbound,
  optimize_name_f st n = Some (n', nbound) ->
    optimize_name_x st n (n', nbound).
Proof.
  intros st n.
  induction n; crush;eauto.
  - remember (fetch_exp_type_x a st) as x.
    destruct x; inversion H; subst. clear H1.
    remember (bound_of_type_f st t) as y.
    destruct y; inversion H; subst.
    apply O_Identifier_X with (t:=t); auto.
    apply bound_of_type_f_soundness; auto.
  - remember (optimize_name_f st n) as x.
    destruct x; inversion H; subst. clear H1.
    destruct p; inversion H; subst. clear H1.
    remember (optimize_expression_f st e) as y.
    destruct y; inversion H; subst. clear H1.
    destruct p; inversion H; subst. clear H1.
    destruct b0; inversion H; subst. clear H1.
    remember (fetch_exp_type_x (name_astnum_x n) st) as z.
    destruct z; inversion H; subst. clear H1.
    destruct t; inversion H; subst. clear H1.
    remember (extract_array_index_range_f st t) as z1.
    destruct z1; inversion H; subst. clear H1.
    destruct r; inversion H; subst. clear H1.
    remember (optimize_range_check_f e1 (Interval l u) (Interval l0 u0)) as z2.
    destruct z2; inversion H; subst. clear H1.
    remember (bound_of_array_component_type_f st t) as z3.
    destruct z3; inversion H; subst.
    specialize (IHn n0 b); crush;eauto.
    apply O_Indexed_Component_X with (xBound:=b) (e':=e1) (u:=l) (v:=u) (t:=t) (u':=l0) (v':=u0); auto.
    apply optimize_expression_f_soundness; auto.
    apply extract_array_index_range_f_soundness; auto.
    apply optimize_range_check_f_soundness; auto.
    apply bound_of_array_component_type_f_soundness; auto.
  - remember (optimize_name_f st n) as x.
    destruct x; inversion H; subst. clear H1.
    destruct p; inversion H; subst. clear H1.
    remember (fetch_exp_type_x (name_astnum_x n) st) as y.
    destruct y; inversion H; subst. clear H1.
    destruct t; inversion H; subst. clear H1.
    remember (bound_of_record_field_type_f st t i) as z.
    destruct z; inversion H; subst.
    specialize (IHn n0 b); crush;eauto.
    apply O_Selected_Component_X with (xBound:=b) (t:=t); auto.
    apply bound_of_record_field_type_f_soundness; auto.
Qed.

Lemma optimize_name_f_completeness: forall n n' nbound st,
  optimize_name_x st n (n', nbound) ->
    optimize_name_f st n = Some (n', nbound).
Proof.
  intros;
  induction H; auto; simpl.
  - rewrite H; auto.
    specialize (bound_of_type_f_completeness _ _ _ H0); intro HZ.
    rewrite HZ; auto.
  - rewrite IHoptimize_name_x; auto.
    specialize (optimize_expression_f_completeness _ _ _ _ H0); intro HZ1.
    rewrite HZ1; auto. rewrite H1; auto.
    specialize (extract_array_index_range_f_completeness _ _ _ _ H2); intro HZ2.
    rewrite HZ2; auto.
    specialize (optimize_range_check_f_completeness _ _ _ _ H3); intro HZ3.
    rewrite HZ3; auto.
    specialize (bound_of_array_component_type_f_completeness _ _ _ H4); intro HZ4.
    rewrite HZ4; auto.
  - rewrite IHoptimize_name_x, H0; auto.
    specialize (bound_of_record_field_type_f_completeness _ _ _ _ H1); intro HZ.
    rewrite HZ; auto. 
Qed.

(** * optimize_args_f *)  
Lemma optimize_args_f_soundness: forall st params args args',
  optimize_args_f st params args = Some args' ->
    optimize_args_x st params args args'.
Proof.
  induction params; intros.
  - destruct args; crush;eauto.
    constructor.
  - destruct args;
    inversion H; subst.
    remember (optimize_args_f st params args) as x1.
    remember (parameter_mode_x a) as x2.
    destruct x1, x2; inversion H1; subst; clear H2.
    + remember (is_range_constrainted_type (parameter_subtype_mark_x a)) as y1.
      destruct y1; inversion H1; subst; clear H2.
      {
      remember (extract_subtype_range_f st (parameter_subtype_mark_x a)) as y2.
      destruct y2; inversion H1; subst; clear H2.
      destruct r; inversion H1; subst; clear H2.
      remember (optimize_expression_f st e) as y3.
      destruct y3; inversion H1; subst; clear H2.
      destruct p; destruct b; inversion H1; subst.
      remember (optimize_range_check_f e0 (Interval l1 u0) (Interval l0 u)) as y4.
      destruct y4; inversion H1; subst.
      apply O_Args_Mode_In_RangeCheck with (u:=l0) (v:=u) (arg':=e0) (u':=l1) (v':=u0); auto.
      apply extract_subtype_range_f_soundness; auto.
      apply optimize_expression_f_soundness; auto.
      apply optimize_range_check_f_soundness; auto.
      }
      {
      remember (optimize_expression_f st e) as y2.
      destruct y2; inversion H1; subst.
      destruct p; inversion H1; subst.
      Print optimize_args_x. 
      apply O_Args_Mode_In with (argBound:=b); auto.
      apply optimize_expression_f_soundness; auto.
      }
    + destruct e; inversion H1; subst; clear H2.
      remember (fetch_exp_type_x a0 st) as y1.
      destruct y1; inversion H1; subst; clear H2.
      remember (is_range_constrainted_type t) as y2.
      destruct y2; inversion H1; subst; clear H2.
      {
      remember (bound_of_type_f st (parameter_subtype_mark_x a)) as y3.
      destruct y3; inversion H1; subst; clear H2.
      destruct b; inversion H1; subst; clear H2.
      remember (extract_subtype_range_f st t) as y4.
      destruct y4; inversion H1; subst; clear H2.
      destruct r; inversion H1; subst; clear H2.
      remember (optimize_name_f st n) as y5.
      destruct y5; inversion H1; subst; clear H2.
      destruct p; inversion H1; subst; clear H2.
      remember (optimize_range_check_f (E_Name_X a0 n0) (Interval l0 u) (Interval l1 u0)) as y6.
      destruct y6; inversion H1; subst.
      apply O_Args_Mode_Out_RangeCheck with (u:=l0) (v:=u) (t:=t) (u':=l1) (v':=u0) (n':=n0) (nBound:=b); auto.
      apply bound_of_type_f_soundness; auto.
      apply extract_subtype_range_f_soundness; auto.
      apply optimize_name_f_soundness; auto.
      apply optimize_range_check_f_soundness; auto.
      }
      {
      remember (optimize_name_f st n) as y1.
      destruct y1; inversion H1; subst.
      destruct p; inversion H1; subst.
      apply O_Args_Mode_Out with (t:=t) (nBound:=b); auto.
      apply optimize_name_f_soundness; auto.
      }
    + destruct e; inversion H1; subst; clear H2.
      remember (fetch_exp_type_x a0 st) as x1.
      destruct x1; inversion H1; subst; clear H2.
      remember (is_range_constrainted_type t) as x2.
      destruct x2; inversion H1; subst; clear H2.
      {
      remember (is_range_constrainted_type (parameter_subtype_mark_x a)) as y1.      
      destruct y1; inversion H1; subst; clear H2.
      remember (extract_subtype_range_f st (parameter_subtype_mark_x a)) as y2.
      destruct y2; inversion H1; subst; clear H2.
      destruct r; inversion H1; clear H2.
      remember (extract_subtype_range_f st t) as y3.
      destruct y3; inversion H1; subst; clear H2.
      destruct r; inversion H1; subst; clear H2.
      remember (optimize_name_f st n) as y4.
      destruct y4; inversion H1; subst; clear H2.
      destruct p; inversion H1; subst; clear H2.
      destruct b; inversion H1; subst; clear H2.
      remember (optimize_range_check_f (E_Name_X a0 n0) (Interval l2 u1) (Interval l0 u)) as y5.
      destruct y5; inversion H1; subst; clear H2.
      remember (optimize_range_check_on_copy_out_f e (Interval l0 u) (Interval l1 u0)) as y6.
      destruct y6; inversion H1; subst.
      apply O_Args_Mode_InOut_In_RangeCheck with (u:=l0) (v:=u) (t:=t) (u':=l1) (v':=u0) (n':=n0) 
                                                 (v1:=l2) (v2:=u1) (arg:=e); auto.
      apply extract_subtype_range_f_soundness; auto.
      apply extract_subtype_range_f_soundness; auto.
      apply optimize_expression_f_soundness; auto. simpl.
      rewrite <- Heqy4; auto.
      apply optimize_range_check_f_soundness; auto.
      apply optimize_range_check_on_copy_out_f_soundness; auto.
      
      remember (optimize_name_f st n) as y7.
      destruct y7; inversion H1; subst.
      destruct p; inversion H1; subst.
      apply O_Args_Mode_InOut with (t:=t) (nBound:=b); auto.
      apply optimize_name_f_soundness; auto.
      }
      {
      remember (optimize_name_f st n) as y1.
      destruct y1; inversion H1; subst.
      destruct p; inversion H1; subst.
      apply O_Args_Mode_InOut with (t:=t) (nBound:=b); auto.
      apply optimize_name_f_soundness; auto.
      }
Qed.

Lemma range_constrainted_type_true: forall st t u v,
  extract_subtype_range_x st t (Range_X u v) ->
    is_range_constrainted_type t = true.
Proof.
  intros.
  induction H; subst.
  unfold is_range_constrainted_type.
  destruct t; crush;eauto.
Qed.

Lemma optimize_args_f_completeness: forall st params args args',
  optimize_args_x st params args args' ->
    optimize_args_f st params args = Some args'.
Proof.
  induction params; intros;
  match goal with
  | [H: optimize_args_x _ _ _ _ |- _] => inversion H; clear H; subst; simpl; auto
  end;
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => 
    specialize (optimize_name_f_completeness _ _ _ _ H); intro HZ 
  | [H: optimize_expression_x _ _ _ |- _] => 
    specialize (optimize_expression_f_completeness _ _ _ _ H); intro HZ
  end;
  match goal with
  | [H1: forall args args' : list expression_x,
           optimize_args_x ?st ?params args args' ->
           optimize_args_f ?st ?params args = Some args',
     H2: optimize_args_x ?st ?params _ _ |- _] => specialize (H1 _ _ H2)
  | _ => idtac
  end;
  match goal with
  | [H: optimize_args_f ?st ?params ?args0 = Some _ |- _] => rewrite H; simpl; auto
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ _ |- _] => 
    specialize (range_constrainted_type_true _ _ _ _ H);
    let HZ := fresh HZ in intro HZ
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: optimize_range_check _ _ _ _ |- _] =>
    specialize (optimize_range_check_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ
  | [H: bound_of_type ?st _ _ |- _] =>
    specialize (bound_of_type_f_completeness _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ  
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _ ] => 
    specialize (optimize_range_check_on_copy_out_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ
  | _ => idtac
  end; 
  match goal with
  | [H: extract_subtype_range_x _ _ _ |- _] => 
    specialize (extract_subtype_range_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | _ => idtac
  end; crush;eauto. 
  destruct (is_range_constrainted_type t); auto.
  specialize (range_constrainted_type_true _ _ _ _ H3); intro HZ4.
  rewrite HZ4; auto.
  specialize (extract_subtype_range_f_completeness _ _ _ _ H3); intros HZ5.
  crush;eauto.
Qed.

(** * optimize_statement_f *)  
Lemma optimize_statement_f_soundness: forall st c c',
  optimize_statement_f st c = Some c' ->
    optimize_statement_x st c c'.
Proof.
  induction c; intros;
  simpl in H; auto.
  - inversion H; subst; 
    constructor.
  - remember (optimize_name_f st n) as x1.
    destruct x1; [ | inversion H]; subst. destruct p.
    remember (optimize_expression_f st e) as x2.
    destruct x2; [ | inversion H]; subst. destruct p.
    remember (fetch_exp_type_x (name_astnum_x n) st) as y1.
    destruct y1; [ | inversion H]; subst.
    remember (is_range_constrainted_type t) as y2.
    destruct y2; inversion H; subst.
    
    clear H1.
    remember (extract_subtype_range_f st t) as y3.
    destruct y3; [ | inversion H]; subst. destruct r. 
    destruct b0; inversion H; subst. clear H1.
    remember (optimize_range_check_f e0 (Interval l0 u0) (Interval l u)) as y4.
    destruct y4; inversion H; subst.

    apply O_Assignment_RangeCheck_X with (t:=t) (u:=l) (v:=u) (xBound:=b) 
                                         (e':=e0) (u':=l0) (v':=u0); auto.
    apply extract_subtype_range_f_soundness; auto.
    apply optimize_name_f_soundness; auto.
    apply optimize_expression_f_soundness; auto.
    apply optimize_range_check_f_soundness; auto.
    
    apply O_Assignment_X with (t:=t) (xBound:=b) (eBound:=b0); auto.
    apply optimize_name_f_soundness; auto.
    apply optimize_expression_f_soundness; auto.
  - remember (optimize_expression_f st e) as x.
    destruct x; [ | inversion H]; subst.
    destruct p.
    remember (optimize_statement_f st c1) as y.
    destruct y; [ | inversion H]; subst.
    remember (optimize_statement_f st c2) as z.
    destruct z; inversion H; subst.
    specialize (IHc1 s); specialize (IHc2 s0); crush;eauto.
    apply O_If_X with (eBound:=b); auto.
    apply optimize_expression_f_soundness; auto.
  - remember (optimize_expression_f st e) as x.
    destruct x; [ | inversion H]; subst.
    destruct p.
    remember (optimize_statement_f st c) as y.
    destruct y; inversion H; subst.
    specialize (IHc s); crush;eauto.
    apply O_While_Loop_X with (eBound:=b); auto.
    apply optimize_expression_f_soundness; auto.
  - remember (fetch_proc_x p st) as x.
    destruct x; [ | inversion H]; subst.
    destruct t.
    remember (optimize_args_f st (procedure_parameter_profile_x p0) l) as y.
    destruct y; inversion H; subst.
    apply O_Procedure_Call_X with (n:=l0) (pb:=p0); auto.
    apply optimize_args_f_soundness; auto.
  - remember (optimize_statement_f st c1) as x.
    destruct x; [ | inversion H]; subst.
    remember (optimize_statement_f st c2) as y.
    destruct y; inversion H; subst.
    specialize (IHc1 s); specialize (IHc2 s0); crush;eauto.
    apply O_Sequence_X; auto.
Qed.

Lemma optimize_statement_f_completeness: forall st c c',
  optimize_statement_x st c c' ->
    optimize_statement_f st c = Some c'.
Proof.
  induction c; intros;
  simpl;
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ _ |- _] => 
    specialize (range_constrainted_type_true _ _ _ _ H);
    let HZ := fresh HZ in intro HZ
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: optimize_name_x _ _ _ |- _] => 
    specialize (optimize_name_f_completeness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ
  | [H: optimize_expression_x _ _ _ |- _] => 
    specialize (optimize_expression_f_completeness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ 
  | [H: optimize_args_x _ _ _ _ |- _] => 
    specialize (optimize_args_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | [H: optimize_range_check _ _ _ _ |- _] =>
    specialize (optimize_range_check_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ
  | [H: bound_of_type ?st _ _ |- _] =>
    specialize (bound_of_type_f_completeness _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ  
  | [H: extract_subtype_range_x _ _ _ |- _] => 
    specialize (extract_subtype_range_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | [H1 : forall c' : statement_x,
         optimize_statement_x ?st ?c c' ->
         optimize_statement_f ?st ?c = Some c',
    H2: optimize_statement_x ?st ?c _ |- _] => specialize (H1 _ H2)
  | _ => idtac
  end; crush;eauto.
Qed.

(** * optimize_object_declaration_f *)  
Lemma optimize_object_declaration_f_soundness: forall st o o',
  optimize_object_declaration_f st o = Some o' ->
    optimize_object_declaration_x st o o'.
Proof.
  intros.
  functional induction optimize_object_declaration_f st o; 
  inversion H; subst;
  match goal with
  | [H: optimize_expression_f _ _ = _ |- _] => 
    specialize (optimize_expression_f_soundness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ  
  | _ => idtac
  end.
  constructor.
  apply O_Object_Declaration_NoRangeCheck_X with (eBound:=eBound); auto.
  apply O_Object_Declaration_RangeCheck_X with (u:=u) (v:=v) (e':=e') (u':=u') (v':=v'); auto.
  apply extract_subtype_range_f_soundness; auto.
  apply optimize_range_check_f_soundness; auto.
Qed.

Lemma optimize_object_declaration_f_completeness: forall st o o',
  optimize_object_declaration_x st o o' ->
    optimize_object_declaration_f st o = Some o'.
Proof.
  intros.
  induction H; crush;eauto;
  match goal with
  | [H: extract_subtype_range_x _ _ _ |- _] => 
    specialize (range_constrainted_type_true _ _ _ _ H);
    let HZ := fresh HZ in intro HZ
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: optimize_expression_x _ _ _ |- _] => 
    specialize (optimize_expression_f_completeness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ 
  | [H: optimize_range_check _ _ _ _ |- _] =>
    specialize (optimize_range_check_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ
  | [H: extract_subtype_range_x _ _ _ |- _] => 
    specialize (extract_subtype_range_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | _ => idtac
  end; crush;eauto.
Qed.


Scheme declaration_x_ind := Induction for declaration_x Sort Prop 
                            with procedure_body_x_ind := Induction for procedure_body_x Sort Prop.

(** * optimize_declaration_f *)  
Lemma optimize_declaration_f_soundness: forall d d' st,
  optimize_declaration_f st d = Some d' ->
    optimize_declaration_x st d d'.
Proof.
  apply (declaration_x_ind
      (fun d: declaration_x => forall (d' : declaration_x) (st: symboltable_x),
        optimize_declaration_f st d = Some d' ->
        optimize_declaration_x st d d')
      (fun p: procedure_body_x => forall (p': procedure_body_x) (st: symboltable_x),
        optimize_procedure_body_f st p = Some p' ->
        optimize_procedure_body_x st p p')
      ); crush;eauto;
  try (constructor; auto).
 - remember (optimize_object_declaration_f st o) as x.
   destruct x; inversion H; subst.
   apply O_Object_Declaration_X.
   apply optimize_object_declaration_f_soundness; auto.
  - remember (optimize_procedure_body_f st p) as x.
    destruct x; inversion H0; subst.
    symmetry in Heqx.
    specialize (H _ _ Heqx).
    apply O_Procedure_Body_X; auto.
  - remember (optimize_declaration_f st d) as x.
    destruct x; [ | inversion H1]; subst.
    remember (optimize_declaration_f st d0) as y.
    destruct y; inversion H1; subst.
    symmetry in Heqx, Heqy.
    specialize (H _ _ Heqx); specialize (H0 _ _ Heqy).
    apply O_Seq_Declaration_X; auto.
  - remember (optimize_declaration_f st procedure_declarative_part_x) as x.
    destruct x; [ | inversion H0]; subst.
    remember (optimize_statement_f st procedure_statements_x) as y.
    destruct y; inversion H0; subst.
    symmetry in Heqx; specialize (H _ _ Heqx).
    apply O_Procedure_Body; auto.
    apply optimize_statement_f_soundness; auto.
Qed.

Lemma optimize_declaration_f_completeness: forall d d' st,
  optimize_declaration_x st d d' ->
    optimize_declaration_f st d = Some d'.
Proof.
  apply (declaration_x_ind
      (fun d: declaration_x => forall (d' : declaration_x) (st: symboltable_x),
        optimize_declaration_x st d d' ->
        optimize_declaration_f st d = Some d')
      (fun p: procedure_body_x => forall (p': procedure_body_x) (st: symboltable_x),
        optimize_procedure_body_x st p p' ->
        optimize_procedure_body_f st p = Some p')
      ); crush;eauto;
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; crush;eauto
  | [H: optimize_procedure_body_x _ _ _ |- _] => inversion H; subst; crush;eauto
  | _ => idtac
  end;
  match goal with 
  | [H: optimize_object_declaration_x _ _ _ |- _] => 
    specialize (optimize_object_declaration_f_completeness _ _ _ H);
    let HZ := fresh HZ in intro HZ; try rewrite HZ; auto
  | _ => idtac
  end.
  specialize (H _ _ H5); rewrite H; auto.
  specialize (H _ _ H7); specialize (H0 _ _ H8);
  rewrite H, H0; auto.
  specialize (H _ _ H8).
  rewrite H; auto.
  specialize (optimize_statement_f_completeness _ _ _ H9); intro HZ.
  rewrite HZ; auto.
Qed.

