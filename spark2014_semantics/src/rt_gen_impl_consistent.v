(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export FunInd rt_gen_impl.

(* ***************************************************************
                 Semantics Equivalence Proof
   *************************************************************** *)

(** * Semantics Consistency Proof for Run-Time Check Generator *)

Scheme expression_ind := Induction for exp Sort Prop 
                         with name_ind := Induction for name Sort Prop.

(** * Soundness of RT-GEN Implementation *)

Section Checks_Generator_Implementation_Soundness_Proof.

  (** ** toExpRTImpl_soundness *)
  Lemma toExpRTImpl_soundness: forall e e' st,
    toExpRTImpl st e = e' ->
      toExpRT st e e'.
  Proof.
    apply (expression_ind
      (fun e: exp => forall (e' : expRT) (st: symTab),
        toExpRTImpl st e = e' ->
        toExpRT   st e e')
      (fun n: name => forall (n': nameRT) (st: symTab),
        toNameRTImpl st n = n' ->
        toNameRT   st n n')
      ); smack;
    [ (*Literal*) 
      destruct l;
      [ remember ((min_signed <=? z)%Z && (z <=? max_signed)%Z) as b; destruct b;
        smack; constructor; smack |
        smack; constructor
      ] | 
      (*Name*) | 
      (*BinOp a b e e0*) destruct b |
      (*UnOp a u e*) destruct u |
      (*Identifier a i*) |
      (*IndexedComponent a n e*) |
      (*SelectedComponent a n i*)
    ];
    match goal with
    | [H: _ = ?b |- in_bound _ _ ?b] => rewrite <- H; constructor; smack
    | _ => constructor; smack
    end.
  Qed.

  (** ** toNameRTImpl_soundness *)
  Lemma toNameRTImpl_soundness: forall st n n',
    toNameRTImpl st n = n' ->
      toNameRT st n n'.
  Proof.
    intros st n;
    induction n; smack; constructor; smack;
    apply toExpRTImpl_soundness; auto.
  Qed.

  (** ** toArgsRTImpl_soundness *)
  Lemma toArgsRTImpl_soundness: forall st params args args',
    toArgsRTImpl st params args = Some args' ->
      toArgsRT st params args args'.
  Proof.
    induction params; smack.
  - destruct args; smack;
    constructor.
  - destruct args; smack.
    remember (toArgsRTImpl st params args) as b1;
    remember (parameter_mode a) as b2; 
    destruct b1, b2; smack.
    + (*In Mode*)
      remember (is_range_constrainted_type (parameter_subtype_mark a)) as x;
      destruct x; smack;
      [ apply ToArgsInRangeCheck |
        apply ToArgsIn
      ]; smack; 
      apply toExpRTImpl_soundness; auto.
    + (*Out Mode*)
      destruct e; smack;
      remember (fetch_exp_type a0 st) as b3;
      destruct b3; smack;
      remember (is_range_constrainted_type t) as b4; destruct b4; smack;
      [ apply ToArgsOutRangeCheck with (t := t) |
        apply ToArgsOut with (t := t)
      ]; smack;
      apply toNameRTImpl_soundness; auto.
    + (*In_Out Mode*)
      destruct e; smack;
      remember (is_range_constrainted_type (parameter_subtype_mark a)) as b3;
      remember (fetch_exp_type a0 st) as b4;
      destruct b3, b4; smack;
      remember (is_range_constrainted_type t) as b5;
      destruct b5; smack;
      [ apply ToArgsInOutRangeCheck with (t:=t) |
        apply ToArgsInOutRangeCheckIn with (t:=t) |
        apply ToArgsInOutRangeCheckOut with (t:=t) |
        apply ToArgsInOut with (t:=t)
      ]; auto;
      apply toNameRTImpl_soundness; auto.
  Qed.

  (** ** toStmtRTImpl_soundness *)
  Lemma toStmtRTImpl_soundness: forall st c c',
    toStmtRTImpl st c = Some c' ->
      toStmtRT st c c'.
  Proof.
    induction c; smack.
  - (*Null*)
    constructor.
  - (*Assign*)
    remember (fetch_exp_type (name_astnum n) st ) as b1;
    destruct b1; smack;
    remember (is_range_constrainted_type t) as b2;
    destruct b2; smack;
    [ apply ToAssignRangeCheck with (t := t) |
      apply ToAssign with (t := t)
    ]; auto;
    solve 
    [ apply toNameRTImpl_soundness; auto |
      apply toExpRTImpl_soundness; auto
    ].
  - (*If*)
    remember (toStmtRTImpl st c1) as b1;
    remember (toStmtRTImpl st c2) as b2;
    destruct b1, b2; smack;
    constructor; smack;
    apply toExpRTImpl_soundness; auto.
  - (*While*)
    remember (toStmtRTImpl st c) as b1;
    destruct b1; smack;
    constructor; smack;
    apply toExpRTImpl_soundness; auto.
  - (*Call*)
    remember (fetch_proc p st) as b1;
    destruct b1; smack;
    destruct t;
    remember (toArgsRTImpl st (procedure_parameter_profile p0) l) as b2;
    destruct b2; smack;
    apply ToCall with (n0 := l0) (pb := p0) (params := (procedure_parameter_profile p0)); smack;
    apply toArgsRTImpl_soundness; auto.
  - (*Seq*)
    remember (toStmtRTImpl st c1) as b1;
    remember (toStmtRTImpl st c2) as b2;
    destruct b1, b2; smack;
    constructor; auto.
  Qed.

  Lemma toTypeDeclRTImpl_soundness: forall t t',
    toTypeDeclRTImpl t = t' ->
        toTypeDeclRT t t'.
  Proof.
    destruct t; smack;
    try (destruct r); constructor.
  Qed.

  Lemma toObjDeclRTImpl_soundness: forall st o o',
    toObjDeclRTImpl st o = o' ->
      toObjDeclRT st o o'.
  Proof.
    intros;
    functional induction toObjDeclRTImpl st o; smack;
    [ constructor |
      apply ToObjDeclRangeCheck |
      apply ToObjDecl 
    ]; auto; apply toExpRTImpl_soundness; auto.
  Qed.

  Lemma toObjDeclsRTImpl_soundness: forall st lo lo',
    toObjDeclsRTImpl st lo = lo' ->
      toObjDeclsRT st lo lo'.
  Proof.
    induction lo; smack;
    constructor; smack;
    apply toObjDeclRTImpl_soundness; auto.
  Qed.

  Lemma toParamSpecRTImpl_soundness: forall param param',
    toParamSpecRTImpl param = param' ->
      toParamSpecRT param param'.
  Proof.
    smack;
    destruct param;
    constructor.  
  Qed.

  Lemma toParamSpecsRTImpl_soundness: forall lparam lparam',
    toParamSpecsRTImpl lparam = lparam' ->
      toParamSpecsRT lparam lparam'.
  Proof.
    induction lparam; smack;
    constructor; smack;
    apply toParamSpecRTImpl_soundness; auto.
  Qed.


  Scheme declaration_ind := Induction for decl Sort Prop 
                            with procedure_body_ind := Induction for procBodyDecl Sort Prop.

  (** ** toDeclRTImpl_soundness *)

  Lemma toDeclRTImpl_soundness: forall d d' st,
    toDeclRTImpl st d = Some d' ->
      toDeclRT st d d'.
  Proof.
    apply (declaration_ind
      (fun d: decl => forall (d' : declRT) (st: symTab),
        toDeclRTImpl st d = Some d' ->
        toDeclRT st d d')
      (fun p: procBodyDecl => forall (p': procBodyDeclRT) (st: symTab),
        toProcBodyDeclRTImpl st p = Some p' ->
        toProcBodyDeclRT st p p')
      ); smack.
  - constructor.
  - constructor;
    apply toTypeDeclRTImpl_soundness; auto.
  - constructor;
    apply toObjDeclRTImpl_soundness; auto.
  - remember (toProcBodyDeclRTImpl st p) as x; 
    destruct x; smack;
    constructor; auto.
  - remember (toDeclRTImpl st d) as x;
    remember (toDeclRTImpl st d0) as y;
    destruct x, y; smack;
    constructor; smack.
  - remember (toDeclRTImpl st procedure_declarative_part) as x;
    remember (toStmtRTImpl st procedure_statements) as y;
    destruct x, y; smack;
    constructor;
    [ apply toParamSpecsRTImpl_soundness | |
      apply toStmtRTImpl_soundness
    ]; auto.
  Qed.

  (** ** toProcBodyDeclRTImpl_soundness *)

  Lemma toProcBodyDeclRTImpl_soundness: forall st p p',
    toProcBodyDeclRTImpl st p = Some p' ->
      toProcBodyDeclRT st p p'.
  Proof.
    intros;
    destruct p; smack.
    remember (toDeclRTImpl st procedure_declarative_part) as x;
    remember (toStmtRTImpl st procedure_statements) as y;
    destruct x, y; smack;
    constructor;
    [ apply toParamSpecsRTImpl_soundness |
      apply toDeclRTImpl_soundness |
      apply toStmtRTImpl_soundness 
    ]; auto.
  Qed.

  (** ** toProgramRTImpl_soundness *)

  Lemma toProgramRTImpl_soundness: forall st p p',
    toProgramRTImpl st p = Some p' ->
      toProgramRT st p p'.
  Proof.
    intros.
    destruct p, p'.
    unfold toProgramRTImpl in H; 
    inversion H; subst; clear H.
    remember (toDeclRTImpl st decls) as x.
    destruct x; inversion H1; subst.
    constructor;
    apply toDeclRTImpl_soundness; auto.
  Qed.

End Checks_Generator_Implementation_Soundness_Proof.


(** * Completeness of RT-GEN Implementation *)

Section Checks_Generator_Implementation_Completeness_Proof.

  (** ** toExpRTImpl_completeness *)

  Lemma toExpRTImpl_completeness: forall e e' st,
    toExpRT st e e' ->
      toExpRTImpl st e = e'.
  Proof.
    apply (expression_ind
      (fun e: exp => forall (e' : expRT) (st: symTab),
        toExpRT   st e e' ->
        toExpRTImpl st e = e')
      (fun n: name => forall (n': nameRT) (st: symTab),
        toNameRT   st n n' ->
        toNameRTImpl st n = n')
      ); smack;
    match goal with
    | [H: toExpRT  _ ?e ?e' |- _] => inversion H; clear H; smack
    | [H: toNameRT _ ?n ?n' |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H1:forall (e' : expRT) (st : symTab),
          toExpRT _ ?e e' ->
          toExpRTImpl _ ?e = e',
       H2:toExpRT _ ?e ?e1RT |- _] => specialize (H1 _ _ H2); smack
    | [H1:forall (n' : nameRT) (st : symTab),
          toNameRT _ ?n n' ->
          toNameRTImpl _ ?n = n',
       H2:toNameRT _ ?n ?nRT |- _] => specialize (H1 _ _ H2); smack
    end;
    match goal with
    | [H: in_bound _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    [ destruct b | 
      destruct u 
    ]; smack.
  Qed.

  (** ** toNameRTImpl_completeness *)
  Lemma toNameRTImpl_completeness: forall st n n',
    toNameRT st n n' ->
      toNameRTImpl st n = n'.
  Proof.
    intros;
    induction H; smack;
    match goal with
    | [H: toExpRT ?st ?e ?e' |- _] => 
        specialize (toExpRTImpl_completeness _ _ _ H); smack
    end; auto.
  Qed.

  (** ** toArgsRTImpl_completeness *)

  Lemma toArgsRTImpl_completeness: forall st params args args',
    toArgsRT st params args args' ->
      toArgsRTImpl st params args = Some args'.
  Proof.
    induction params; smack;
    match goal with
    | [H: toArgsRT _ _ ?args ?args' |- _] => inversion H; clear H; smack
    end;
    match goal with
    | [H1: forall (args : list exp) (args' : list expRT),
           toArgsRT _ ?params _ _ ->
           toArgsRTImpl _ ?params _ = Some _,
       H2: toArgsRT _ ?params _ _ |- _] => specialize (H1 _ _ H2)
    end;
    match goal with
    | [H: toArgsRTImpl ?st ?params ?larg = Some _ |- _] => rewrite H; simpl
    end;
    match goal with
    | [H: toExpRT _ ?e ?e' |- _] => specialize (toExpRTImpl_completeness _ _ _ H); smack
    | [H: toNameRT _ ?n ?n' |- _] => specialize (toNameRTImpl_completeness _ _ _ H); smack
    | _ => idtac
    end; auto.
  Qed.

  (** ** toStmtRTImpl_completeness *)

  Lemma toStmtRTImpl_completeness: forall st c c',
    toStmtRT st c c' ->
      toStmtRTImpl st c = Some c'.
  Proof.
    induction c; smack;
    match goal with
    | [H: toStmtRT _ ?c ?c' |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: toExpRT  _ ?e ?e' |- _] => specialize (toExpRTImpl_completeness  _ _ _ H); clear H
    | [H: toNameRT _ ?n ?n' |- _] => specialize (toNameRTImpl_completeness _ _ _ H); clear H
    | [H1: forall c' : stmtRT,
           toStmtRT _ ?c _ ->
           toStmtRTImpl _ ?c = Some _,
       H2: toStmtRT _ ?c _ |- _ ] => specialize (H1 _ H2)
    end; smack;
    match goal with
    | [H: toArgsRT _ _ _ _ |- _ ] => specialize (toArgsRTImpl_completeness _ _ _ _ H); smack
    end.
  Qed.

  Lemma toTypeDeclRTImpl_completeness: forall t t',
    toTypeDeclRT t t' ->
      toTypeDeclRTImpl t = t'.
  Proof.
    destruct t; intros;
    match goal with
    | [H: toTypeDeclRT _ _ |- _] => inversion H; smack
    end.
  Qed.

  Lemma toObjDeclRTImpl_completeness: forall st o o',
    toObjDeclRT st o o' ->
      toObjDeclRTImpl st o = o'.
  Proof.
    intros;
    functional induction toObjDeclRTImpl st o;
    match goal with
    | [H: toObjDeclRT _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: toExpRT _ _ _ |- _] => 
        specialize (toExpRTImpl_completeness _ _ _ H); smack
    end. 
  Qed.

  Lemma toObjDeclsRTImpl_completeness: forall st lo lo',
    toObjDeclsRT st lo lo' ->
      toObjDeclsRTImpl st lo = lo'.
  Proof.
    induction lo; smack;
    match goal with
    | [H: toObjDeclsRT _ _ _ |- _] => inversion H; clear H; smack
    end;
    match goal with
    | [H: toObjDeclRT _ ?o ?o' |- _] => 
        specialize (toObjDeclRTImpl_completeness _ _ _ H); smack
    end;
    specialize (IHlo _ H5); smack.
  Qed.

  Lemma toParamSpecRTImpl_completeness: forall param param',
    toParamSpecRT param param' ->
      toParamSpecRTImpl param = param'.
  Proof.
    intros;
    inversion H; auto.
  Qed.

  Lemma toParamSpecsRTImpl_completeness: forall lparam lparam',
    toParamSpecsRT lparam lparam' ->
      toParamSpecsRTImpl lparam = lparam'.
  Proof.
    induction lparam; intros;
    inversion H; auto;
    specialize (IHlparam _ H4);
    match goal with
    | [H: toParamSpecRT _ _ |- _] => 
        specialize (toParamSpecRTImpl_completeness _ _ H); smack
    end.
  Qed.

  (** ** toDeclRTImpl_completeness *)

  Lemma toDeclRTImpl_completeness: forall d d' st,
    toDeclRT st d d' ->
      toDeclRTImpl st d = Some d'.
  Proof.
    apply (declaration_ind
      (fun d: decl => forall (d' : declRT) (st: symTab),
        toDeclRT st d d' ->
        toDeclRTImpl st d = Some d')
      (fun p: procBodyDecl => forall (p': procBodyDeclRT) (st: symTab),
        toProcBodyDeclRT st p p' ->
        toProcBodyDeclRTImpl st p = Some p')
      ); smack;
    match goal with
    | [H: toDeclRT _ _ _ |- _] => inversion H; clear H; smack
    | [H: toProcBodyDeclRT _ _ _ |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: toTypeDeclRT _ _ |- _] => 
        specialize (toTypeDeclRTImpl_completeness _ _ H); smack
    | [H: toObjDeclRT _ _ _ |- _] =>
        specialize (toObjDeclRTImpl_completeness _ _ _ H); smack
    | [H: toParamSpecsRT _ _ |- _] =>
        specialize (toParamSpecsRTImpl_completeness _ _ H); clear H; smack
    | [H: toStmtRT _ _ _ |- _] =>
        specialize (toStmtRTImpl_completeness _ _ _ H); clear H; smack
    | [H1: forall (p' : procBodyDeclRT) (st : symTab),
           toProcBodyDeclRT _ ?p _ ->
           toProcBodyDeclRTImpl _ ?p = Some _,
       H2: toProcBodyDeclRT _ ?p _ |- _] =>
        specialize (H1 _ _ H2); smack
    | [H1: forall (d' : declRT) (st : symTab),
           toDeclRT _ ?d _ ->
           toDeclRTImpl _ ?d = Some _,
       H2: toDeclRT _ ?d _ |- _] => 
        specialize (H1 _ _ H2); clear H2; smack
    end.
  Qed.

  (** ** toProcBodyDeclRTImpl_completeness *)

  Lemma toProcBodyDeclRTImpl_completeness: forall st p p',
    toProcBodyDeclRT st p p' ->
      toProcBodyDeclRTImpl st p = Some p'.
  Proof.
    intros;
    destruct p;
    match goal with
    [H: toProcBodyDeclRT _ _ _ |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: toParamSpecsRT _ _ |- _] =>
        specialize (toParamSpecsRTImpl_completeness _ _ H); clear H; smack
    | [H: toStmtRT _ _ _ |- _] =>
        specialize (toStmtRTImpl_completeness _ _ _ H); clear H; smack
    | [H: toDeclRT _ _ _ |- _] => 
        specialize (toDeclRTImpl_completeness _ _ _ H); clear H; smack
    end.
  Qed.

  (** ** toProgramRTImpl_completeness *)

  Lemma toProgramRTImpl_completeness: forall st p p',
    toProgramRT st p p' ->
      toProgramRTImpl st p = Some p'.
  Proof.
    intros.
    destruct p, p'.
    inversion H; subst; clear H.
    simpl in H3.
    specialize (toDeclRTImpl_completeness _ _ _ H3); intro HZ.
    unfold toProgramRTImpl; simpl. 
    rewrite HZ; auto.
  Qed.

End Checks_Generator_Implementation_Completeness_Proof.

(** * Consistency of RT-GEN Impl and RT-GEN Spec *)

(** ** toExpRTImplConsistent *)
Lemma toExpRTImplConsistent: forall e e' st,
  toExpRT st e e' <-> 
    toExpRTImpl st e = e'.
Proof.
  intros; split; intro;
  [ apply toExpRTImpl_completeness; auto |
    apply toExpRTImpl_soundness; auto 
  ].
Qed.  

(** ** toStmtRTImplConsistent *)
Lemma toStmtRTImplConsistent: forall st c c',
  toStmtRT st c c' <->
    toStmtRTImpl st c = Some c'.
Proof.
  intros; split; intro;
  [ apply toStmtRTImpl_completeness; auto |
    apply toStmtRTImpl_soundness; auto 
  ].
Qed.

(** ** toProcBodyDeclRTConsistent *)
Lemma toProcBodyDeclRTConsistent: forall st p p',
  toProcBodyDeclRT st p p' <->
    toProcBodyDeclRTImpl st p = Some p'.
Proof.
  intros; split; intro;
  [ apply toProcBodyDeclRTImpl_completeness; auto |
    apply toProcBodyDeclRTImpl_soundness; auto 
  ].
Qed.


(** ** toProgramRTImplConsistent *)
Lemma toProgramRTImplConsistent: forall st p p',
  toProgramRT st p p' <->
    toProgramRTImpl st p = Some p'.
Proof.
  intros; split; intro;
  [ apply toProgramRTImpl_completeness; auto |
    apply toProgramRTImpl_soundness; auto 
  ].
Qed.

