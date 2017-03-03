(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export rt_opt_impl.

(**********************************************)
(** *             helper lemmas               *)
(**********************************************)

(** ** extract_subtype_range_f soundness and completeness *)
Lemma extract_subtype_range_f_soundness: forall st t l u,
  extract_subtype_range_f st t = Some (RangeRT l u) ->
    extract_subtype_range_rt st t (RangeRT l u).
Proof.
  intros;
  functional induction extract_subtype_range_f st t; smack;
  apply Extract_Range_RT with (td:=td) (tn:=tn); auto.
Qed.

Lemma extract_subtype_range_f_completeness: forall st t l u,
  extract_subtype_range_rt st t (RangeRT l u) ->
    extract_subtype_range_f st t = Some (RangeRT l u).
Proof.
  intros;
  destruct H; auto;
  unfold extract_subtype_range_f; smack.
Qed.

(** ** bound_of_type_f soundness and completeness *)
Lemma bound_of_type_f_soundness: forall st t bd,
  bound_of_type_f st t = Some bd ->
    bound_of_type st t bd.
Proof.
  intros;
  functional induction bound_of_type_f st t; smack;
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
  | [H: extract_subtype_range_rt _ _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: subtype_num _ = Some _ |- _] => inversion H; subst
  end.
  destruct H; smack.
Qed.

(** ** bound_of_array_component_type_f soundness and completeness *)
Lemma bound_of_array_component_type_f_soundness: forall st t bd,
  bound_of_array_component_type_f st t = Some bd ->
    bound_of_array_component_type st t bd.
Proof.
  intros;
  functional induction bound_of_array_component_type_f st t; smack;
  apply Array_Component_Value with (n:=n) (tn:=tn) (indexSubtypeMark:=indexSubtypeMark)
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
  unfold bound_of_array_component_type_f; smack.
Qed.

(** ** bound_of_record_field_type_f soundness and completeness *)
Lemma bound_of_record_field_type_f_soundness: forall st t f bd,
  bound_of_record_field_type_f st t f = Some bd ->
    bound_of_record_field_type st t f bd.
Proof.
  intros;
  functional induction bound_of_record_field_type_f st t f; smack;
  apply Record_Field_Value with (n:=n) (tn:=tn) (fields:=fields) (ft:=ft); auto;
  apply bound_of_type_f_soundness; auto.
Qed.

Lemma bound_of_record_field_type_f_completeness: forall st t f bd,
  bound_of_record_field_type st t f bd ->
    bound_of_record_field_type_f st t f = Some bd.
Proof.
  intros;
  induction H; auto;
  specialize (bound_of_type_f_completeness _ _ _ H1); intro;
  unfold bound_of_record_field_type_f; smack.
Qed.

(** ** in_bound_f soundness and completeness *)
Lemma in_bound_f_soundness: forall v bd b,
  in_bound_f v bd = Some b ->
    in_bound v bd b.
Proof.
  intros;
  functional induction in_bound_f v bd; smack;
  remember ((l <=? v)%Z && (v <=? u)%Z) as b;
  destruct b; constructor; auto.
Qed.

Lemma in_bound_f_completeness: forall v bd b,
  in_bound v bd b ->
    in_bound_f v bd = Some b.
Proof.
  intros;
  induction H; smack.  
Qed.

(** ** sub_bound_f soundness and completeness *)
Lemma sub_bound_f_soundness: forall bd1 bd2 b,
  sub_bound_f bd1 bd2 = Some b ->
    sub_bound bd1 bd2 b.
Proof.
  intros.
  functional induction sub_bound_f bd1 bd2; smack.
  repeat progress constructor; auto. 
  constructor.
  remember ((u' <=? u)%Z && (u <=? v')%Z) as b1; destruct b1.
  right. constructor. destruct ((u' <=? v)%Z && (v <=? v')%Z); smack.
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

(** ** optimize_overflow_check_f soundness and completeness *)
Lemma optimize_overflow_check_f_soundness: forall bd cks bd' cks',
  optimize_overflow_check_f bd cks = Some (bd', cks') ->
    optimize_overflow_check bd cks (bd', cks').
Proof.
  intros;
  functional induction optimize_overflow_check_f bd cks;
  match goal with
  | [H: sub_bound_f _ _ = Some _ |- _] => specialize (sub_bound_f_soundness _ _ _ H); smack
  | _ => smack
  end. 
  destruct bd'; inversion e;
  apply OOC_True; auto.
  apply OOC_False; auto.
Qed.

Lemma optimize_overflow_check_f_completeness: forall bd cks bd' cks',
  optimize_overflow_check bd cks (bd', cks') ->
    optimize_overflow_check_f bd cks = Some (bd', cks').
Proof.
  intros;
  induction H; auto;
  specialize (sub_bound_f_completeness _ _ _ H); intro;
  unfold optimize_overflow_check_f;
  [rewrite H1 | rewrite H0]; smack.
Qed.

(** ** optimize_range_check_f soundness and completeness *)
Lemma optimize_range_check_f_soundness: forall e bd1 bd2 e',
  optimize_range_check_f e bd1 bd2 = Some e' ->
    optimize_range_check e bd1 bd2 e'.
Proof.
  intros;
  functional induction optimize_range_check_f e bd1 bd2; smack;
  specialize (sub_bound_f_soundness _ _ _ e0); intro;
  destruct bd1, bd2; inversion e0;
  [ apply ORC_True with (cks:=(remove_check_flag RangeCheck (exp_exterior_checks e))); auto |
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
  unfold optimize_range_check_f; smack.
Qed.

(** ** optimize_range_check_on_copy_out_f soundness and completeness *)
Lemma optimize_range_check_on_copy_out_f_soundness: forall e bd1 bd2 e',
  optimize_range_check_on_copy_out_f e bd1 bd2 = Some e' ->
    optimize_range_check_on_copy_out e bd1 bd2 e'.
Proof.
  intros;
  functional induction optimize_range_check_on_copy_out_f e bd1 bd2; smack;
  specialize (sub_bound_f_soundness _ _ _ e0); intro;
  destruct bd1, bd2; inversion e0;
  [ apply ORCOCO_True with (cks:=(remove_check_flag RangeCheckOnReturn (exp_exterior_checks e))); auto |
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
  unfold optimize_range_check_on_copy_out_f; smack.
Qed.

(** ** optimize_rtc_binop_f soundness and completeness *)
Lemma optimize_rtc_binop_f_soundness: forall op bd1 bd2 cks bd cks',
  optimize_rtc_binop_f op bd1 bd2 cks = Some (bd, cks') ->
    optimize_rtc_binop op bd1 bd2 cks (bd, cks').
Proof.
  intros;
  functional induction optimize_rtc_binop_f op bd1 bd2 cks; smack.

  specialize (optimize_overflow_check_f_soundness _ _ _ _ H); intros.
  eapply O_RTC_Plus; smack.
  
  specialize (optimize_overflow_check_f_soundness _ _ _ _ H); intros.
  eapply O_RTC_Minus; smack.  
  
  eapply O_RTC_Multiply; auto.
    apply optimize_overflow_check_f_soundness; auto.
  
  eapply O_RTC_Divide_OverflowRTC; smack;
    [ apply in_bound_f_soundness; smack |
      apply optimize_overflow_check_f_soundness; auto ].
  
  eapply O_RTC_Divide_DivisionRTC; smack.
    apply in_bound_f_soundness; smack.
    apply optimize_overflow_check_f_soundness; auto.
  
  eapply O_RTC_Modulus; auto.
    apply in_bound_f_soundness; smack.
  
  eapply O_RTC_Modulus_DivisionRTC; auto.
    apply in_bound_f_soundness; smack.

  destruct op; inversion y; constructor; smack. 
Qed.

Lemma optimize_rtc_binop_f_completeness: forall op bd1 bd2 cks bd cks',
  optimize_rtc_binop op bd1 bd2 cks (bd, cks') ->
    optimize_rtc_binop_f op bd1 bd2 cks = Some (bd, cks').
Proof.
  intros;
  induction H; auto;
  repeat progress match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => 
    specialize (optimize_overflow_check_f_completeness _ _ _ _ H); intros; clear H
  | [H: in_bound _ _ _ |- _] => 
    specialize (in_bound_f_completeness _ _ _ H); intros; clear H
  | _ => idtac 
  end;
  unfold optimize_rtc_binop_f;
  repeat progress match goal with
  | [H1: in_bound_f _ _ = Some _ |- _] => rewrite H1; clear H1; auto
  | [H1: Math.add _ _ = Some _ |- _] => rewrite H1; clear H1; auto
  | [H1: Math.sub _ _ = Some _ |- _] => rewrite H1; clear H1; auto
  | [H1: _ = divide_min_max_f _ _ _ _ |- _] => rewrite <- H1; clear H1; auto
  | [H1: _ = remove_check_flag _ _ |- _] => rewrite <- H1; clear H1; auto
  | [H1: _ = modulus_min_max_f _ _ _ _ |- _] => rewrite <- H1; clear H1; auto
  end; auto.

  destruct op; smack.
Qed.

(** ** optimize_rtc_unop_f soundness and completeness *)
Lemma optimize_rtc_unop_f_soundness: forall op bd cks bd' cks',
  optimize_rtc_unop_f op bd cks = Some (bd', cks') ->
    optimize_rtc_unop op bd cks (bd', cks').
Proof.
  intros;
  functional induction optimize_rtc_unop_f op bd cks; smack.
  specialize (optimize_overflow_check_f_soundness _ _ _ _ H); intros.
  eapply O_RTC_Unary_Minus; smack.
  constructor; auto.
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
Qed.

(** ** extract_array_index_range_f soundness and completeness *)
Lemma extract_array_index_range_f_soundness: forall st t l u,
  extract_array_index_range_f st t = Some (RangeRT l u) ->
    extract_array_index_range_rt st t (RangeRT l u).
Proof.
  intros;
  functional induction extract_array_index_range_f st t; smack;
  econstructor; smack.
Qed.

Lemma extract_array_index_range_f_completeness: forall st t l u,
  extract_array_index_range_rt st t (RangeRT l u) ->
    extract_array_index_range_f st t = Some (RangeRT l u).
Proof.
  intros;
  induction H; auto;
  unfold extract_array_index_range_f;
  rewrite H, H0, H1, H2; auto.
Qed.

Lemma range_constrainted_type_true: forall st t u v,
  extract_subtype_range_rt st t (RangeRT u v) ->
    is_range_constrainted_type t = true.
Proof.
  intros.
  induction H; subst.
  unfold is_range_constrainted_type.
  destruct t; smack.
Qed.

(***************************************************)
(** *  Consistency Proof for RT-OPT Implementation *)
(*  (1) soundness proof                            *)
(*  (2) completeness proof                         *)
(***************************************************)

Scheme expression_x_ind := Induction for expRT Sort Prop 
                         with name_x_ind := Induction for nameRT Sort Prop.

Scheme declaration_x_ind := Induction for declRT Sort Prop 
                            with procedure_body_x_ind := Induction for procBodyDeclRT Sort Prop.


(** * Soundness of RT-OPT Implementation *)

(** ** optLiteralImpl_soundness *)
Lemma optLiteralImpl_soundness: forall l cks lbound cks',
  optLiteralImpl l cks = Some (lbound, cks') ->
    optLiteral l cks (lbound, cks').
Proof.
  intros;
  functional induction optLiteralImpl l cks; smack;
  constructor; auto;
  apply optimize_overflow_check_f_soundness; auto.
Qed.

(** ** optExpImpl_soundness *)
Lemma optExpImpl_soundness: forall e e' ebound st,
  optExpImpl st e = Some (e', ebound) ->
    optExp st e (e', ebound).
Proof.
  apply (expression_x_ind
      (fun e: expRT => forall (e' : expRT) (ebound: bound) (st: symTabRT),
        optExpImpl st e = Some (e', ebound) ->
        optExp st e (e', ebound))
      (fun n: nameRT => forall (n': nameRT) (nbound: bound) (st: symTabRT),
        optNameImpl st n = Some (n', nbound) ->
        optName st n (n', nbound))
      ); smack.
  - (*1. literal *)
    remember (optLiteralImpl l i) as x.
    destruct x; inversion H; subst.
    destruct p; inversion H; subst.
    constructor; auto.
    apply optLiteralImpl_soundness; auto.
  - (* 2. name *)
    remember (optNameImpl st n) as x.
    destruct x; inversion H0; subst.
    destruct p; inversion H0; subst.
    constructor; auto.
  - (* 3. binary expression *)
    remember (optExpImpl st e) as x1;
    remember (optExpImpl st e0) as x2.
    destruct x1, x2; inversion H1; subst;
    destruct p; try destruct p0; inversion H1; subst.
    clear H3 H4.
    remember (optimize_rtc_binop_f b b0 b1 i) as y. 
    destruct y; inversion H1; subst.
    destruct p; inversion H1; subst.
    symmetry in Heqx1, Heqx2.
    specialize (H _ _ _ Heqx1); specialize (H0 _ _ _ Heqx2).
    eapply O_BinOp; smack.
    apply optimize_rtc_binop_f_soundness; auto.
  - (* 4. unary expression *)
    remember (optExpImpl st e) as x.
    destruct x; inversion H0; subst.
    destruct p; inversion H0; subst.
    clear H2 H3.
    remember (optimize_rtc_unop_f u b i) as y.
    destruct y; inversion H0; subst.
    destruct p; inversion H0; subst.
    symmetry in Heqx. specialize (H _ _ _ Heqx).
    eapply O_UnOp; smack.
    apply optimize_rtc_unop_f_soundness; auto.
  - (* 5. identifier *)
    remember (fetch_exp_type_rt a st) as x.
    destruct x; inversion H; subst.
    remember (bound_of_type_f st t) as y.
    destruct y; inversion H; subst.
    eapply O_Identifier; smack.
    apply bound_of_type_f_soundness; auto.
  - (* 6. indexed component *)
    remember (optNameImpl st n) as x1; 
    remember (optExpImpl st e) as x2.
    destruct x1, x2; inversion H1; subst;
    destruct p; try destruct p0; inversion H1; subst.
    clear H3 H4.
    destruct b0; inversion H1; subst. clear H3.
    remember (fetch_exp_type_rt (name_astnum_rt n) st) as y1.
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
    apply O_IndexedComponent with (xBound:=b) (u:=l) (v:=u) (u':=l0) (v':=u0) (e':=e1) (t:=t); auto.
    apply extract_array_index_range_f_soundness; auto.
    apply optimize_range_check_f_soundness; auto.
    apply bound_of_array_component_type_f_soundness; auto.
  - (* 7. selected component *)
    remember (optNameImpl st n) as x1;
    remember (fetch_exp_type_rt (name_astnum_rt n) st) as x2.
    destruct x1, x2; inversion H0; subst;
    destruct p; inversion H0; subst.
    clear H2 H3.
    destruct t; inversion H0; subst. clear H2.
    remember (bound_of_record_field_type_f st t i) as y.
    destruct y; inversion H0; subst. 
    symmetry in Heqx1; specialize (H _ _ _ Heqx1).
    eapply O_SelectedComponent; smack.
    apply bound_of_record_field_type_f_soundness; auto.
Qed.

(** ** optNameImpl_soundness *)  
Lemma optNameImpl_soundness: forall st n n' nbound,
  optNameImpl st n = Some (n', nbound) ->
    optName st n (n', nbound).
Proof.
  intros st n.
  induction n; smack.
  - remember (fetch_exp_type_rt a st) as x.
    destruct x; inversion H; subst. clear H1.
    remember (bound_of_type_f st t) as y.
    destruct y; inversion H; subst.
    apply O_Identifier with (t:=t); auto.
    apply bound_of_type_f_soundness; auto.
  - remember (optNameImpl st n) as x.
    destruct x; inversion H; subst. clear H1.
    destruct p; inversion H; subst. clear H1.
    remember (optExpImpl st e) as y.
    destruct y; inversion H; subst. clear H1.
    destruct p; inversion H; subst. clear H1.
    destruct b0; inversion H; subst. clear H1.
    remember (fetch_exp_type_rt (name_astnum_rt n) st) as z.
    destruct z; inversion H; subst. clear H1.
    destruct t; inversion H; subst. clear H1.
    remember (extract_array_index_range_f st t) as z1.
    destruct z1; inversion H; subst. clear H1.
    destruct r; inversion H; subst. clear H1.
    remember (optimize_range_check_f e1 (Interval l u) (Interval l0 u0)) as z2.
    destruct z2; inversion H; subst. clear H1.
    remember (bound_of_array_component_type_f st t) as z3.
    destruct z3; inversion H; subst.
    specialize (IHn n0 b); smack.
    apply O_IndexedComponent with (xBound:=b) (e':=e1) (u:=l) (v:=u) (t:=t) (u':=l0) (v':=u0); auto.
    apply optExpImpl_soundness; auto.
    apply extract_array_index_range_f_soundness; auto.
    apply optimize_range_check_f_soundness; auto.
    apply bound_of_array_component_type_f_soundness; auto.
  - remember (optNameImpl st n) as x.
    destruct x; inversion H; subst. clear H1.
    destruct p; inversion H; subst. clear H1.
    remember (fetch_exp_type_rt (name_astnum_rt n) st) as y.
    destruct y; inversion H; subst. clear H1.
    destruct t; inversion H; subst. clear H1.
    remember (bound_of_record_field_type_f st t i) as z.
    destruct z; inversion H; subst.
    specialize (IHn n0 b); smack.
    apply O_SelectedComponent with (xBound:=b) (t:=t); auto.
    apply bound_of_record_field_type_f_soundness; auto.
Qed.


(** ** optArgsImpl_soundness *)  
Lemma optArgsImpl_soundness: forall st params args args',
  optArgsImpl st params args = Some args' ->
    optArgs st params args args'.
Proof.
  induction params; intros.
  - destruct args; smack.
    constructor.
  - destruct args;
    inversion H; subst.
    remember (optArgsImpl st params args) as x1.
    remember (parameter_mode_rt a) as x2.
    destruct x1, x2; inversion H1; subst; clear H2.
    + remember (is_range_constrainted_type (parameter_subtype_mark_rt a)) as y1.
      destruct y1; inversion H1; subst; clear H2.
      {
      remember (extract_subtype_range_f st (parameter_subtype_mark_rt a)) as y2.
      destruct y2; inversion H1; subst; clear H2.
      destruct r; inversion H1; subst; clear H2.
      remember (optExpImpl st e) as y3.
      destruct y3; inversion H1; subst; clear H2.
      destruct p; destruct b; inversion H1; subst.
      remember (optimize_range_check_f e0 (Interval l1 u0) (Interval l0 u)) as y4.
      destruct y4; inversion H1; subst.
      apply O_Args_Mode_In_RangeCheck with (u:=l0) (v:=u) (arg':=e0) (u':=l1) (v':=u0); auto.
      apply extract_subtype_range_f_soundness; auto.
      apply optExpImpl_soundness; auto.
      apply optimize_range_check_f_soundness; auto.
      }
      {
      remember (optExpImpl st e) as y2.
      destruct y2; inversion H1; subst.
      destruct p; inversion H1; subst.
      apply O_Args_Mode_In with (argBound:=b); auto.
      apply optExpImpl_soundness; auto.
      }
    + destruct e; inversion H1; subst; clear H2.
      remember (fetch_exp_type_rt a0 st) as y1.
      destruct y1; inversion H1; subst; clear H2.
      remember (is_range_constrainted_type t) as y2.
      destruct y2; inversion H1; subst; clear H2.
      {
      remember (bound_of_type_f st (parameter_subtype_mark_rt a)) as y3.
      destruct y3; inversion H1; subst; clear H2.
      destruct b; inversion H1; subst; clear H2.
      remember (extract_subtype_range_f st t) as y4.
      destruct y4; inversion H1; subst; clear H2.
      destruct r; inversion H1; subst; clear H2.
      remember (optNameImpl st n) as y5.
      destruct y5; inversion H1; subst; clear H2.
      destruct p; inversion H1; subst; clear H2.
      remember (optimize_range_check_on_copy_out_f (NameRT a0 n0) (Interval l0 u) (Interval l1 u0)) as y6.
      destruct y6; inversion H1; subst.
      apply O_Args_Mode_Out_RangeCheck with (u:=l0) (v:=u) (t:=t) (u':=l1) (v':=u0) (n':=n0) (nBound:=b); auto.
      apply bound_of_type_f_soundness; auto.
      apply extract_subtype_range_f_soundness; auto.
      apply optNameImpl_soundness; auto.
      apply optimize_range_check_on_copy_out_f_soundness; auto.
      }
      {
      remember (optNameImpl st n) as y1.
      destruct y1; inversion H1; subst.
      destruct p; inversion H1; subst.
      apply O_Args_Mode_Out with (t:=t) (nBound:=b); auto.
      apply optNameImpl_soundness; auto.
      }
    + destruct e; inversion H1; subst; clear H2.
      remember (fetch_exp_type_rt a0 st) as x1.
      destruct x1; inversion H1; subst; clear H2.
      remember (is_range_constrainted_type t) as x2.
      destruct x2; inversion H1; subst; clear H2.
      {
      remember (is_range_constrainted_type (parameter_subtype_mark_rt a)) as y1.      
      destruct y1; inversion H1; subst; clear H2.
      remember (extract_subtype_range_f st (parameter_subtype_mark_rt a)) as y2.
      destruct y2; inversion H1; subst; clear H2.
      destruct r; inversion H1; clear H2.
      remember (extract_subtype_range_f st t) as y3.
      destruct y3; inversion H1; subst; clear H2.
      destruct r; inversion H1; subst; clear H2.
      remember (optNameImpl st n) as y4.
      destruct y4; inversion H1; subst; clear H2.
      destruct p; inversion H1; subst; clear H2.
      destruct b; inversion H1; subst; clear H2.
      remember (optimize_range_check_f (NameRT a0 n0) (Interval l2 u1) (Interval l0 u)) as y5.
      destruct y5; inversion H1; subst; clear H2.
      remember (optimize_range_check_on_copy_out_f e (Interval l0 u) (Interval l1 u0)) as y6.
      destruct y6; inversion H1; subst.
      apply O_Args_Mode_InOut_In_RangeCheck with (u:=l0) (v:=u) (t:=t) (u':=l1) (v':=u0) (n':=n0) 
                                                 (v1:=l2) (v2:=u1) (arg:=e); auto.
      apply extract_subtype_range_f_soundness; auto.
      apply extract_subtype_range_f_soundness; auto.
      apply optExpImpl_soundness; auto. simpl.
      rewrite <- Heqy4; auto.
      apply optimize_range_check_f_soundness; auto.
      apply optimize_range_check_on_copy_out_f_soundness; auto.
      
      remember (optNameImpl st n) as y7.
      destruct y7; inversion H1; subst.
      destruct p; inversion H1; subst.
      apply O_Args_Mode_InOut with (t:=t) (nBound:=b); auto.
      apply optNameImpl_soundness; auto.
      }
      {
      remember (optNameImpl st n) as y1.
      destruct y1; inversion H1; subst.
      destruct p; inversion H1; subst.
      apply O_Args_Mode_InOut with (t:=t) (nBound:=b); auto.
      apply optNameImpl_soundness; auto.
      }
Qed.

(** ** optStmtImpl_soundness *)  
Lemma optStmtImpl_soundness: forall st c c',
  optStmtImpl st c = Some c' ->
    optStmt st c c'.
Proof.
  induction c; intros;
  simpl in H; auto.
  - inversion H; subst; 
    constructor.
  - remember (optNameImpl st n) as x1.
    destruct x1; [ | inversion H]; subst. destruct p.
    remember (optExpImpl st e) as x2.
    destruct x2; [ | inversion H]; subst. destruct p.
    remember (fetch_exp_type_rt (name_astnum_rt n) st) as y1.
    destruct y1; [ | inversion H]; subst.
    remember (is_range_constrainted_type t) as y2.
    destruct y2; inversion H; subst.
    
    clear H1.
    remember (extract_subtype_range_f st t) as y3.
    destruct y3; [ | inversion H]; subst. destruct r. 
    destruct b0; inversion H; subst. clear H1.
    remember (optimize_range_check_f e0 (Interval l0 u0) (Interval l u)) as y4.
    destruct y4; inversion H; subst.

    apply O_Assign_RangeCheck with (t:=t) (u:=l) (v:=u) (xBound:=b) 
                                         (e':=e0) (u':=l0) (v':=u0); auto.
    apply extract_subtype_range_f_soundness; auto.
    apply optNameImpl_soundness; auto.
    apply optExpImpl_soundness; auto.
    apply optimize_range_check_f_soundness; auto.
    
    apply O_Assign with (t:=t) (xBound:=b) (eBound:=b0); auto.
    apply optNameImpl_soundness; auto.
    apply optExpImpl_soundness; auto.
  - remember (optExpImpl st e) as x.
    destruct x; [ | inversion H]; subst.
    destruct p.
    remember (optStmtImpl st c1) as y.
    destruct y; [ | inversion H]; subst.
    remember (optStmtImpl st c2) as z.
    destruct z; inversion H; subst.
    specialize (IHc1 s); specialize (IHc2 s0); smack.
    apply O_If with (eBound:=b); auto.
    apply optExpImpl_soundness; auto.
  - remember (optExpImpl st e) as x.
    destruct x; [ | inversion H]; subst.
    destruct p.
    remember (optStmtImpl st c) as y.
    destruct y; inversion H; subst.
    specialize (IHc s); smack.
    apply O_While with (eBound:=b); auto.
    apply optExpImpl_soundness; auto.
  - remember (fetch_proc_rt p st) as x.
    destruct x; [ | inversion H]; subst.
    destruct t.
    remember (optArgsImpl st (procedure_parameter_profile_rt p0) l) as y.
    destruct y; inversion H; subst.
    apply O_Call with (n0:=l0) (pb:=p0); auto.
    apply optArgsImpl_soundness; auto.
  - remember (optStmtImpl st c1) as x.
    destruct x; [ | inversion H]; subst.
    remember (optStmtImpl st c2) as y.
    destruct y; inversion H; subst.
    specialize (IHc1 s); specialize (IHc2 s0); smack.
    apply O_Seq; auto.
Qed.

(** ** optObjDeclImpl_soundness *)  
Lemma optObjDeclImpl_soundness: forall st o o',
  optObjDeclImpl st o = Some o' ->
    optObjDecl st o o'.
Proof.
  intros.
  functional induction optObjDeclImpl st o; 
  inversion H; subst;
  match goal with
  | [H: optExpImpl _ _ = _ |- _] => 
    specialize (optExpImpl_soundness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ  
  | _ => idtac
  end.
  constructor.
  apply O_ObjDecl_NoRangeCheck with (eBound:=eBound); auto.
  apply O_ObjDecl_RangeCheck with (u:=u) (v:=v) (e':=e') (u':=u') (v':=v'); auto.
  apply extract_subtype_range_f_soundness; auto.
  apply optimize_range_check_f_soundness; auto.
Qed.

(** ** optDeclImpl_soundness *)  
Lemma optDeclImpl_soundness: forall d d' st,
  optDeclImpl st d = Some d' ->
    optDecl st d d'.
Proof.
  apply (declaration_x_ind
      (fun d: declRT => forall (d' : declRT) (st: symTabRT),
        optDeclImpl st d = Some d' ->
        optDecl st d d')
      (fun p: procBodyDeclRT => forall (p': procBodyDeclRT) (st: symTabRT),
        optProcBodyDeclImpl st p = Some p' ->
        optProcBodyDecl st p p')
      ); smack;
  try (constructor; auto).
 - remember (optObjDeclImpl st o) as x.
   destruct x; inversion H; subst.
   apply O_ObjDecl.
   apply optObjDeclImpl_soundness; auto.
  - remember (optProcBodyDeclImpl st p) as x.
    destruct x; inversion H0; subst.
    symmetry in Heqx.
    specialize (H _ _ Heqx).
    apply O_ProcBody; auto.
  - remember (optDeclImpl st d) as x.
    destruct x; [ | inversion H1]; subst.
    remember (optDeclImpl st d0) as y.
    destruct y; inversion H1; subst.
    symmetry in Heqx, Heqy.
    specialize (H _ _ Heqx); specialize (H0 _ _ Heqy).
    apply O_SeqDecl; auto.
  - remember (optDeclImpl st procedure_declarative_part_rt) as x.
    destruct x; [ | inversion H0]; subst.
    remember (optStmtImpl st procedure_statements_rt) as y.
    destruct y; inversion H0; subst.
    symmetry in Heqx; specialize (H _ _ Heqx).
    apply O_ProcBodyDecl; auto.
    apply optStmtImpl_soundness; auto.
Qed.

(** ** optProgramImpl_soundness *)  
Lemma optProgramImpl_soundness: forall p p' st,
  optProgramImpl st p = Some p' ->
    optProgram st p p'.
Proof.
  intros.
  destruct p, p'. 
  unfold optProgramImpl in H; 
  inversion H; subst; clear H. 
  remember (optDeclImpl st declsRT) as x.
  destruct x; inversion H1; subst.
  constructor;
  apply optDeclImpl_soundness; auto.
Qed.

(** * Completeness of RT-OPT Implementation *)

(** ** optLiteralImpl_completeness *)

Lemma optLiteralImpl_completeness: forall l cks lbound cks',
  optLiteral l cks (lbound, cks') ->
    optLiteralImpl l cks = Some (lbound, cks').
Proof.
  intros;
  induction H; auto;
  specialize (optimize_overflow_check_f_completeness _ _ _ _ H); intro;
  unfold optLiteralImpl;
  rewrite H0; auto.
Qed.

(** ** optExpImpl_completeness *)
Lemma optExpImpl_completeness: forall e e' ebound st,
  optExp st e (e', ebound) ->
    optExpImpl st e = Some (e', ebound).
Proof.
  apply (expression_x_ind
      (fun e: expRT => forall (e' : expRT) (ebound: bound) (st: symTabRT),
        optExp st e (e', ebound) ->
        optExpImpl st e = Some (e', ebound))
      (fun n: nameRT => forall (n': nameRT) (nbound: bound) (st: symTabRT),
        optName st n (n', nbound) ->
        optNameImpl st n = Some (n', nbound))
      ); intros; simpl.
  - (*1. literal *)
    remember (LiteralRT a l i e) as x.
    inversion H; subst;
    match goal with
    | [H: _ = LiteralRT _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (optLiteralImpl_completeness _ _ _ _ H3); intro HZ;
    rewrite HZ; auto.
  - (*2. name *)
    remember (NameRT a n) as x.
    inversion H0; subst;
    match goal with
    | [H: _ = NameRT _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H4);
    rewrite H; auto.
  - (*3. binary expression *)
    remember (BinOpRT a b e e0 i e1) as x.
    inversion H1; subst;
    match goal with
    | [H: _ = BinOpRT _ _ _ _ _ _ |- _] => inversion H; subst
    end.
    specialize (H _ _ _ H4); 
    specialize (H0 _ _ _ H7).
    specialize (optimize_rtc_binop_f_completeness _ _ _ _ _ _ H8); intro HZ.
    rewrite H, H0; auto.
    rewrite HZ; auto.
  - (*4. unary expression *)
    remember (UnOpRT a u e i e0) as x.
    inversion H0; subst;
    match goal with 
    | [H: _ = UnOpRT _ _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H5).
    specialize (optimize_rtc_unop_f_completeness _ _ _ _ _ H6); intro HZ.
    rewrite H, HZ; auto.
  - (*5. identifier *)
    remember (IdentifierRT a i e) as x.
    inversion H; subst;
    match goal with
    | [H: _ = IdentifierRT _ _ _ |- _] => inversion H; subst 
    end.
    specialize (bound_of_type_f_completeness _ _ _ H5); intro HZ;
    rewrite H4, HZ; auto.     
  - (*6. indexed component *)
    remember (IndexedComponentRT a n e e0) as x.
    inversion H1; subst;
    match goal with 
    | [H: _ = IndexedComponentRT _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H4).
    specialize (H0 _ _ _ H5).
    rewrite H, H0, H6; auto.
    specialize (extract_array_index_range_f_completeness _ _ _ _ H7); intro HZ1.
    specialize (optimize_range_check_f_completeness _ _ _ _ H10); intro HZ2.
    specialize (bound_of_array_component_type_f_completeness _ _ _ H11); intro HZ3.
    rewrite HZ1, HZ2, HZ3; auto.
  - (*7. selected component *)
    remember (SelectedComponentRT a n i e) as x.
    inversion H0; subst;
    match goal with 
    | [H: _ = SelectedComponentRT _ _ _ _ |- _] => inversion H; subst 
    end.
    specialize (H _ _ _ H3).
    rewrite H, H6; auto.
    specialize (bound_of_record_field_type_f_completeness _ _ _ _ H7); intro HZ.
    rewrite HZ; auto.
Qed.

(** ** optNameImpl_completeness *)
Lemma optNameImpl_completeness: forall n n' nbound st,
  optName st n (n', nbound) ->
    optNameImpl st n = Some (n', nbound).
Proof.
  intros;
  induction H; auto; simpl.
  - rewrite H; auto.
    specialize (bound_of_type_f_completeness _ _ _ H0); intro HZ.
    rewrite HZ; auto.
  - rewrite IHoptName; auto.
    specialize (optExpImpl_completeness _ _ _ _ H0); intro HZ1.
    rewrite HZ1; auto. rewrite H1; auto.
    specialize (extract_array_index_range_f_completeness _ _ _ _ H2); intro HZ2.
    rewrite HZ2; auto.
    specialize (optimize_range_check_f_completeness _ _ _ _ H3); intro HZ3.
    rewrite HZ3; auto.
    specialize (bound_of_array_component_type_f_completeness _ _ _ H4); intro HZ4.
    rewrite HZ4; auto.
  - rewrite IHoptName, H0; auto.
    specialize (bound_of_record_field_type_f_completeness _ _ _ _ H1); intro HZ.
    rewrite HZ; auto. 
Qed.

(** ** optArgsImpl_completeness *)
Lemma optArgsImpl_completeness: forall st params args args',
  optArgs st params args args' ->
    optArgsImpl st params args = Some args'.
Proof.
  induction params; intros;
  match goal with
  | [H: optArgs _ _ _ _ |- _] => inversion H; clear H; subst; simpl; auto
  end;
  match goal with
  | [H: optName _ _ _ |- _] => 
    specialize (optNameImpl_completeness _ _ _ _ H); intro HZ 
  | [H: optExp _ _ _ |- _] => 
    specialize (optExpImpl_completeness _ _ _ _ H); intro HZ
  end;
  match goal with
  | [H1: forall args args' : list expRT,
           optArgs ?st ?params args args' ->
           optArgsImpl ?st ?params args = Some args',
     H2: optArgs ?st ?params _ _ |- _] => specialize (H1 _ _ H2)
  | _ => idtac
  end;
  match goal with
  | [H: optArgsImpl ?st ?params ?args0 = Some _ |- _] => rewrite H; simpl; auto
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ _ |- _] => 
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
  | [H: extract_subtype_range_rt _ _ _ |- _] => 
    specialize (extract_subtype_range_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | _ => idtac
  end; smack. 
  destruct (is_range_constrainted_type t); auto.
  specialize (range_constrainted_type_true _ _ _ _ H3); intro HZ4.
  rewrite HZ4; auto.
  specialize (extract_subtype_range_f_completeness _ _ _ _ H3); intros HZ5.
  smack.
Qed.


(** ** optStmtImpl_completeness *)
Lemma optStmtImpl_completeness: forall st c c',
  optStmt st c c' ->
    optStmtImpl st c = Some c'.
Proof.
  induction c; intros;
  simpl;
  match goal with
  | [H: optStmt _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ _ |- _] => 
    specialize (range_constrainted_type_true _ _ _ _ H);
    let HZ := fresh HZ in intro HZ
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: optName _ _ _ |- _] => 
    specialize (optNameImpl_completeness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ
  | [H: optExp _ _ _ |- _] => 
    specialize (optExpImpl_completeness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ 
  | [H: optArgs _ _ _ _ |- _] => 
    specialize (optArgsImpl_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | [H: optimize_range_check _ _ _ _ |- _] =>
    specialize (optimize_range_check_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ
  | [H: bound_of_type ?st _ _ |- _] =>
    specialize (bound_of_type_f_completeness _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ  
  | [H: extract_subtype_range_rt _ _ _ |- _] => 
    specialize (extract_subtype_range_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | [H1 : forall c' : stmtRT,
         optStmt ?st ?c c' ->
         optStmtImpl ?st ?c = Some c',
    H2: optStmt ?st ?c _ |- _] => specialize (H1 _ H2)
  | _ => idtac
  end; smack.
Qed.


(** ** optObjDeclImpl_completeness *)
Lemma optObjDeclImpl_completeness: forall st o o',
  optObjDecl st o o' ->
    optObjDeclImpl st o = Some o'.
Proof.
  intros.
  induction H; smack;
  match goal with
  | [H: extract_subtype_range_rt _ _ _ |- _] => 
    specialize (range_constrainted_type_true _ _ _ _ H);
    let HZ := fresh HZ in intro HZ
  | _ => idtac
  end;
  repeat progress match goal with
  | [H: optExp _ _ _ |- _] => 
    specialize (optExpImpl_completeness _ _ _ _ H); clear H;
      let HZ := fresh HZ in intro HZ 
  | [H: optimize_range_check _ _ _ _ |- _] =>
    specialize (optimize_range_check_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ
  | [H: extract_subtype_range_rt _ _ _ |- _] => 
    specialize (extract_subtype_range_f_completeness _ _ _ _ H); clear H;
    let HZ := fresh HZ in intro HZ 
  | _ => idtac
  end; smack.
Qed.


(** ** optDeclImpl_completeness *)
Lemma optDeclImpl_completeness: forall d d' st,
  optDecl st d d' ->
    optDeclImpl st d = Some d'.
Proof.
  apply (declaration_x_ind
      (fun d: declRT => forall (d' : declRT) (st: symTabRT),
        optDecl st d d' ->
        optDeclImpl st d = Some d')
      (fun p: procBodyDeclRT => forall (p': procBodyDeclRT) (st: symTabRT),
        optProcBodyDecl st p p' ->
        optProcBodyDeclImpl st p = Some p')
      ); smack;
  match goal with
  | [H: optDecl _ _ _ |- _] => inversion H; subst; smack
  | [H: optProcBodyDecl _ _ _ |- _] => inversion H; subst; smack
  | _ => idtac
  end;
  match goal with 
  | [H: optObjDecl _ _ _ |- _] => 
    specialize (optObjDeclImpl_completeness _ _ _ H);
    let HZ := fresh HZ in intro HZ; try rewrite HZ; auto
  | _ => idtac
  end.
  specialize (H _ _ H5); rewrite H; auto.
  specialize (H _ _ H7); specialize (H0 _ _ H8);
  rewrite H, H0; auto.
  specialize (H _ _ H8).
  rewrite H; auto.
  specialize (optStmtImpl_completeness _ _ _ H9); intro HZ.
  rewrite HZ; auto.
Qed.

(** ** optProgramImpl_completeness *)  
Lemma optProgramImpl_completeness: forall p p' st,
  optProgram st p p' ->
    optProgramImpl st p = Some p'.
Proof.
  intros.
  destruct p, p'. 
  inversion H; subst; clear H; simpl in H3.
  unfold optProgramImpl; simpl.
  specialize (optDeclImpl_completeness _ _ _ H3); intro HZ.
  rewrite HZ; auto.
Qed.

(** * Consistency of RT-OPT Impl and RT-OPT Spec *)

(** ** optExpImplConsistent *)
Lemma optExpImplConsistent: forall e e' ebound st,
  optExpImpl st e = Some (e', ebound) <-> optExp st e (e', ebound).
Proof.
  intro; 
  split; intro;
  [apply optExpImpl_soundness; auto |
   apply optExpImpl_completeness; auto 
  ].
Qed.

(** ** optNameImplConsistent *)  
Lemma optNameImplConsistent: forall st n n' nbound,
  optNameImpl st n = Some (n', nbound) <-> optName st n (n', nbound).
Proof.
  intro; 
  split; intro;
  [apply optNameImpl_soundness; auto |
   apply optNameImpl_completeness; auto 
  ].
Qed.

(** ** optStmtImplConsistent *)  
Lemma optStmtImplConsistent: forall st c c',
  optStmtImpl st c = Some c' <-> optStmt st c c'.
Proof.
  intro; 
  split; intro;
  [apply optStmtImpl_soundness; auto |
   apply optStmtImpl_completeness; auto 
  ].
Qed.

(** ** optDeclImplConsistent *)  
Lemma optDeclImplConsistent: forall d d' st,
  optDeclImpl st d = Some d' <-> optDecl st d d'.
Proof.
  intro; 
  split; intro;
  [apply optDeclImpl_soundness; auto |
   apply optDeclImpl_completeness; auto 
  ].
Qed.

(** ** optProgramImplConsistent *)
Lemma optProgramImplConsistent: forall p p' st,
  optProgramImpl st p = Some p' <-> optProgram st p p'.
Proof.
  intro; 
  split; intro;
  [apply optProgramImpl_soundness; auto |
   apply optProgramImpl_completeness; auto 
  ].
Qed.
