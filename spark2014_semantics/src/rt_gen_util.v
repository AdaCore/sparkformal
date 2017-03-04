(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

(** * Helper Lemmas for RT-GEN *)

Require Import CpdtTactics.
Require Export rt_gen.

Lemma exp_ast_num_eq: forall st e e',
  toExpRT st e e' ->
    expression_astnum e = expression_astnum_rt e'.
Proof.
  intros; inversion H; smack.
Qed.

Lemma name_ast_num_eq: forall st n n',
  toNameRT st n n' ->
    name_astnum n = name_astnum_rt n'.
Proof.
  intros; inversion H; smack.
Qed.

Lemma exp_exterior_checks_beq_nil: forall st e e',
  toExpRT st e e' ->
    exp_exterior_checks e' = nil.
Proof.
  intros; 
  inversion H; smack;
  inversion H; subst;
  destruct n; 
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; smack
  end.
Qed.

Lemma name_exterior_checks_beq_nil: forall st n n',
  toNameRT st n n' ->
    name_exterior_checks n' = nil.
Proof.
  intros; 
  inversion H; smack.
Qed.

Lemma procedure_components_rel: forall st p p',
  toProcBodyDeclRT st p p' ->
  toParamSpecsRT (procedure_parameter_profile p) (procedure_parameter_profile_rt p') /\
  toDeclRT st (procedure_declarative_part p) (procedure_declarative_part_rt p') /\
  toStmtRT st (procedure_statements p) (procedure_statements_rt p').
Proof.
  intros.
  inversion H; smack.
Qed.


(** * SymTabRT Generator *)

Inductive toProcDeclRTMap: symTab ->
                         list (idnum * (level * procBodyDecl)) -> 
                         list (idnum * (level * procBodyDeclRT)) -> Prop :=
    | ToProcDeclMapNull: forall st,
        toProcDeclRTMap st nil nil
    | ToProcDeclMap: forall st pb pb' pl pl' p l,
        toProcBodyDeclRT st pb pb' ->
        toProcDeclRTMap st pl pl' ->
        toProcDeclRTMap st ((p, (l, pb)) :: pl) ((p, (l, pb')) :: pl').

Inductive toTypeDeclRTMap: list (idnum * typeDecl) -> list (idnum * typeDeclRT) -> Prop :=
    | ToTypeDeclMapNull:
        toTypeDeclRTMap nil nil
    | ToTypeDeclMap: forall t t' tl tl' x,
        toTypeDeclRT t t' ->
        toTypeDeclRTMap tl tl' ->
        toTypeDeclRTMap ((x, t) :: tl) ((x, t') :: tl').

Inductive toSymTabRT: symTab -> symTabRT -> Prop := 
  | ToSymTab: forall p p' t t' x e srcloc nametable,
      toProcDeclRTMap (mkSymTab x p t e srcloc nametable) p p' ->
      toTypeDeclRTMap t t' ->
      toSymTabRT (mkSymTab x p t e srcloc nametable) (mkSymTabRT x p' t' e srcloc nametable).


(** ** Help Lemmas for SymTabRT *)

Lemma procedure_declaration_rel: forall st pm pm' p n pb,
  toProcDeclRTMap st pm pm' ->
    Symbol_Table_Module.SymTable_Procs.fetches p pm = Some (n, pb) ->
      exists pb',
        Symbol_Table_Module_RT.SymTable_Procs.fetches p pm' = Some (n, pb') /\ 
        toProcBodyDeclRT st pb pb'.
Proof.
  intros st pm pm' p n pb H; revert p n pb.
  induction H; intros.
- inversion H; inversion H0; auto.
- unfold Symbol_Table_Module.SymTable_Procs.fetches in H1.
  unfold Symbol_Table_Module_RT.SymTable_Procs.fetches.
  remember (beq_nat p0 p) as Beq.
  destruct Beq. 
  + smack.
  + specialize (IHtoProcDeclRTMap _ _ _ H1).
    auto.
Qed.

Lemma procedure_declaration_rel_backward: forall st pm pm' p n pb,
  toProcDeclRTMap st pm pm' ->
    Symbol_Table_Module_RT.SymTable_Procs.fetches p pm' = Some (n, pb) ->
      exists pb',
        Symbol_Table_Module.SymTable_Procs.fetches p pm = Some (n, pb') /\ 
        toProcBodyDeclRT st pb' pb.
Proof.
  intros st pm pm' p n pb H; revert p n pb.
  induction H; intros.
- inversion H; inversion H0; auto.
- unfold Symbol_Table_Module_RT.SymTable_Procs.fetches in H1.
  unfold Symbol_Table_Module.SymTable_Procs.fetches.
  remember (beq_nat p0 p) as Beq.
  destruct Beq. 
  + smack.
  + specialize (IHtoProcDeclRTMap _ _ _ H1);
    auto.
Qed.

Lemma symbol_table_procedure_rel: forall st st' p n pb,
  toSymTabRT st st' ->  
    fetch_proc p st = Some (n, pb) ->
      exists pb',
        fetch_proc_rt p st' = Some (n, pb') /\
        toProcBodyDeclRT st pb pb'.
Proof.
  intros.
  inversion H; subst; clear H.
  unfold fetch_proc_rt;
  unfold fetch_proc in H0;
  simpl in *.
  specialize (procedure_declaration_rel _ _ _ _ _ _ H1 H0);
  auto.
Qed.

Lemma symbol_table_procedure_rel_backward: forall st st' p n pb,
  toSymTabRT st st' ->  
    fetch_proc_rt p st' = Some (n, pb) ->
      exists pb',
        fetch_proc p st = Some (n, pb') /\
        toProcBodyDeclRT st pb' pb.
Proof.
  intros.
  inversion H; subst; clear H.
  unfold fetch_proc;
  unfold fetch_proc_rt in H0;
  simpl in *.
  specialize (procedure_declaration_rel_backward _ _ _ _ _ _ H1 H0);
  auto.
Qed.

Lemma symbol_table_var_rel: forall st st' x,
  toSymTabRT st st' ->
    fetch_var x st = fetch_var_rt x st'.
Proof.
  intros.
  inversion H; smack.
Qed.

Lemma type_declaration_rel: forall tm tm' t td,
  toTypeDeclRTMap tm tm' ->
    Symbol_Table_Module.SymTable_Types.fetches t tm = Some td ->
    exists td',
      Symbol_Table_Module_RT.SymTable_Types.fetches t tm' = Some td' /\
      toTypeDeclRT td td'.
Proof.
  intros tm tm' t td H; revert t td.
  induction H; smack.
  destruct (beq_nat t0 x).
- inversion H; smack.
- apply IHtoTypeDeclRTMap; auto.
Qed.

Lemma type_declaration_rel_backward: forall tm tm' t td,
  toTypeDeclRTMap tm tm' ->
    Symbol_Table_Module_RT.SymTable_Types.fetches t tm' = Some td ->
    exists td',
      Symbol_Table_Module.SymTable_Types.fetches t tm = Some td' /\
      toTypeDeclRT td' td.
Proof.
  intros tm tm' t td H; revert t td.
  induction H; smack.
  destruct (beq_nat t0 x).
- inversion H; smack.
- apply IHtoTypeDeclRTMap; auto.
Qed.

Lemma symbol_table_type_rel: forall st st' t td,
  toSymTabRT st st' ->
    fetch_type t st = Some td ->
      exists td',
        fetch_type_rt t st' = Some td' /\ toTypeDeclRT td td'.
Proof.
  intros.
  inversion H; smack.
  unfold fetch_type, Symbol_Table_Module.fetch_type in H0; 
  unfold fetch_type_rt, Symbol_Table_Module_RT.fetch_type; smack.
  apply type_declaration_rel with (tm := t0); auto.
Qed.

Lemma symbol_table_type_rel_backward: forall st st' t td,
  toSymTabRT st st' ->
    fetch_type_rt t st' = Some td ->
      exists td',
        fetch_type t st = Some td' /\ toTypeDeclRT td' td.
Proof.
  intros.
  inversion H; smack.
  unfold fetch_type, Symbol_Table_Module_RT.fetch_type in H0; 
  unfold fetch_type_rt, Symbol_Table_Module.fetch_type; smack.
  apply type_declaration_rel_backward with (tm' := t'); auto.
Qed.

Lemma symbol_table_exp_type_rel: forall st st' e t,
  toSymTabRT st st' ->
    fetch_exp_type e st = t ->
      fetch_exp_type_rt e st' = t.
Proof.
  intros.
  inversion H; smack.
Qed.

Lemma symbol_table_exp_type_eq: forall st st' e,
  toSymTabRT st st' ->
    fetch_exp_type e st = fetch_exp_type_rt e st'.
Proof.
  intros.
  inversion H; smack.  
Qed.

Lemma subtype_range_rel: forall st st' t l u,
  toSymTabRT st st' ->
    extract_subtype_range st t (Range l u) ->
      extract_subtype_range_rt st' t (RangeRT l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H6); clear H6; smack.
  apply Extract_Range_RT with (tn := tn) (td := x); smack.
  destruct td; inversion H7; subst;
  inversion H2; auto.
Qed.

Lemma subtype_range_rel_backward: forall st st' t l u,
  toSymTabRT st st' ->
    extract_subtype_range_rt st' t (RangeRT l u) ->
      extract_subtype_range st t (Range l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel_backward _ _ _ _ H H6); clear H6; smack.
  apply Extract_Range with (tn := tn) (td := x); smack.
  destruct td; inversion H7; subst;
  inversion H2; auto.
Qed.

Lemma index_range_rel: forall st st' t l u,
  toSymTabRT st st' ->
    extract_array_index_range st t (Range l u) ->
      extract_array_index_range_rt st' t (RangeRT l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H3); clear H3; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H7); clear H7; smack.  
  apply Extract_Index_Range_RT with (a_ast_num := a_ast_num) (tn := tn) (tm := tm) 
                                   (typ := typ) (tn' := tn') (td := x0); smack.
  inversion H2; auto.
  destruct td; inversion H8; subst;
  inversion H5; auto.
Qed.

Lemma index_range_rel_backward: forall st st' t l u,
  toSymTabRT st st' ->
    extract_array_index_range_rt st' t (RangeRT l u) ->
      extract_array_index_range st t (Range l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel_backward _ _ _ _ H H3); clear H3; smack.
  specialize (symbol_table_type_rel_backward _ _ _ _ H H7); clear H7; smack.  
  apply Extract_Index_Range with (a_ast_num := a_ast_num) (tn := tn) (tm := tm) 
                                 (typ := typ) (tn' := tn') (td := x0); smack.
  inversion H2; auto.
  destruct td; inversion H8; subst;
  inversion H5; auto.
Qed.
