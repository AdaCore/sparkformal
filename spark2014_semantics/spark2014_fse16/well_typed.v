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
Require Export checks_optimization.

Import STACK.

(** * Helper Functions *)

(** ** the type of the expression *)

Definition type_of_name_x (st: symTabRT) (n: nameRT): option type :=
  match n with
  | IdentifierRT ast_num _ _ => fetch_exp_type_rt ast_num st
  | IndexedComponentRT ast_num _ _ _ => fetch_exp_type_rt ast_num st
  | SelectedComponentRT ast_num _ _ _ => fetch_exp_type_rt ast_num st
  end.

Definition type_of_exp_x (st: symTabRT) (e: expRT): option type :=
  match e with
  | LiteralRT _ (Integer_Literal _) _ _ => Some Integer
  | LiteralRT _ (Boolean_Literal _) _ _ => Some Boolean
  | NameRT ast_num n => fetch_exp_type_rt ast_num st
  | BinOpRT ast_num _ _ _ _ _ => fetch_exp_type_rt ast_num st
  | UnOpRT ast_num _ _ _ _ => fetch_exp_type_rt ast_num st
  end.

Definition binop_type (op: binary_operator) (t1 t2: type): option type :=
    match op with
    | Equal | Not_Equal | Greater_Than | Greater_Than_Or_Equal
    | Less_Than | Less_Than_Or_Equal =>
        match t1, t2 with
        | Boolean, _ => None
        | _, Boolean => None
        | Array_Type _, _ => None
        | _, Array_Type _ => None
        | Record_Type _, _ => None
        | _, Record_Type _ => None
        | _, _ => Some Boolean
        end
    | And | Or =>
        match t1, t2 with
        | Boolean, Boolean => Some Boolean
        | _, _ => None
        end
    | Plus | Minus | Multiply | Divide | Modulus =>
        match t1, t2 with
        | Boolean, _ => None
        | _, Boolean => None
        | Array_Type _, _ => None
        | _, Array_Type _ => None
        | Record_Type _, _ => None
        | _, Record_Type _ => None
        | _, _ => Some Integer
        end
    end.

Definition unop_type (op: unary_operator) (t: type): option type :=
    match op with
    | Unary_Minus =>
        match t with
        | Integer | Subtype _ | Derived_Type _ | Integer_Type _ => Some Integer
        | _ => None
        end
(*  | Unary_Plus =>
        Some t  *)
    | Not => 
        match t with
        | Boolean => Some Boolean
        | _ => None
        end
    end.

Definition type_match (t: type) (t': type) :=
  match t with
  | Boolean =>
      match t' with
      | Boolean => true
      | _ => false
      end
  | Integer | Subtype _ | Derived_Type _ | Integer_Type _ => (* type match for assignment not exactly correct *)
      match t' with
      | Integer | Subtype _ | Derived_Type _ | Integer_Type _ => true
      | _ => false
      end
  | Array_Type t1 =>
      match t' with
      | Array_Type t2 => beq_nat t1 t2
      | _ => false
      end
  | Record_Type t1 =>
      match t' with
      | Record_Type t2 => beq_nat t1 t2
      | _ => false
      end
  end.

Lemma type_match_ref: forall t t',
  type_match t t' = type_match t' t.
Proof.
  destruct t, t'; smack;
  remember (beq_nat t t0) as b1;
  remember (beq_nat t0 t) as b2;
  destruct b1, b2; auto;
  match goal with
  | [H: true = beq_nat ?x ?y |- _] => rewrite (beq_nat_eq _ _ H) in *
  end;
  match goal with
  | [H: _ = beq_nat ?x ?x |- _] => rewrite <- beq_nat_refl in H; inversion H
  end.
Qed.

(** * Well-Typed Expression *)

Inductive well_typed_exp_x: symTabRT -> expRT -> Prop :=
  | WT_Literal_Int_X: forall st ast_num v in_cks ex_cks,
      fetch_exp_type_rt ast_num st = Some Integer ->
      well_typed_exp_x st (LiteralRT ast_num (Integer_Literal v) in_cks ex_cks)
  | WT_Literal_Bool_X: forall st ast_num v in_cks ex_cks,
      fetch_exp_type_rt ast_num st = Some Boolean ->
      well_typed_exp_x st (LiteralRT ast_num (Boolean_Literal v) in_cks ex_cks)
  | WT_Name_X: forall st ast_num n,
      fetch_exp_type_rt ast_num st = fetch_exp_type_rt (name_astnum_rt n) st ->
      well_typed_name_x st n ->
      well_typed_exp_x st (NameRT ast_num n)
  | WT_Binary_Exp_X: forall st ast_num op e1 e2 in_cks ex_cks t t1 t2,
      well_typed_exp_x st e1 ->
      well_typed_exp_x st e2 ->
      fetch_exp_type_rt ast_num st = Some t -> (* binary expression's type *)
      type_of_exp_x st e1 = Some t1 -> type_of_exp_x st e2 = Some t2 -> 
      binop_type op t1 t2 = Some t -> (* binary expression's type *)
      well_typed_exp_x st (BinOpRT ast_num op e1 e2 in_cks ex_cks)
  | WT_Unary_Exp_X: forall st ast_num op e in_cks ex_cks t t',
      well_typed_exp_x st e ->
      fetch_exp_type_rt ast_num st = Some t -> (* unary expression's type *)
      type_of_exp_x st e = Some t' ->
      unop_type op t' = Some t -> (* unary expression's type *)
      well_typed_exp_x st (UnOpRT ast_num op e in_cks ex_cks)

with well_typed_name_x: symTabRT -> nameRT -> Prop :=
  | WT_Identifier_X: forall st ast_num x ex_cks md t,
      fetch_exp_type_rt ast_num st = Some t ->
      fetch_var_rt x st = Some (md, t) ->
      well_typed_name_x st (IdentifierRT ast_num x ex_cks)
  | WT_Indexed_Component_X: forall st ast_num x e ex_cks t t' a_ast_num tn tm,
      well_typed_name_x st x ->
      well_typed_exp_x st e ->
      fetch_exp_type_rt ast_num st = Some t -> (* indexed component's type *)
      fetch_exp_type_rt (name_astnum_rt x) st = Some (Array_Type t') ->
      fetch_type_rt t' st = Some (ArrayTypeDeclRT a_ast_num tn tm t) -> (* array element's type *)
      well_typed_name_x st (IndexedComponentRT ast_num x e ex_cks)
  | WT_Selected_Component_X: forall st ast_num x f ex_cks t t' r_ast_num tn fields,
      well_typed_name_x st x ->
      fetch_exp_type_rt ast_num st = Some t -> (* selected component's type *)
      fetch_exp_type_rt (name_astnum_rt x) st = Some (Record_Type t') ->
      fetch_type_rt t' st = Some (RecordTypeDeclRT r_ast_num tn fields) ->
      record_field_type fields f = Some t -> (* selected record field's type *)
      well_typed_name_x st (SelectedComponentRT ast_num x f ex_cks).

Inductive well_typed_exps_x: symTabRT -> list expRT -> Prop :=
  | WT_Exps_Nil_X: forall st,
      well_typed_exps_x st nil
  | WT_Exps_X: forall st e le,
      well_typed_exp_x  st e  ->
      well_typed_exps_x st le ->
      well_typed_exps_x st (e :: le).

Inductive well_typed_params_x: symTabRT -> list paramSpecRT -> Prop :=
  | WT_Params_Nil_X: forall st,
      well_typed_params_x st nil
  | WT_Params_X: forall st m x lx,
      fetch_var_rt x.(parameter_nameRT) st = Some (m, x.(parameter_subtype_mark_rt)) ->
      well_typed_params_x st lx ->
      well_typed_params_x st (x :: lx).

Inductive well_typed_args_x: symTabRT -> list expRT -> list paramSpecRT -> Prop :=
  | WT_Args_Nil_X: forall st,
      well_typed_args_x st nil nil
  | WT_Args_X: forall st e le x lx t,
      fetch_exp_type_rt (expression_astnum_rt e) st = Some t ->
      (* argument's type should match its parameter's type *)
      type_match t x.(parameter_subtype_mark_rt) = true ->
      well_typed_args_x st le lx ->
      well_typed_args_x st (e :: le) (x :: lx).

(** * Well-Typed Statement *)

Inductive well_typed_statement_x: symTabRT -> stmtRT -> Prop :=
  | WT_Null_X: forall st,
      well_typed_statement_x st NullRT
  | WT_Assignment_X: forall st ast_num x e t t',
      well_typed_exp_x st e ->
      well_typed_name_x st x ->
      fetch_exp_type_rt (expression_astnum_rt e) st = Some t ->
      fetch_exp_type_rt (name_astnum_rt x) st = Some t' ->
      (* +++ right-hand-side exp's type should be compatible with the left-hand-side exp's type *)
      type_match t t' = true ->
      well_typed_statement_x st (AssignRT ast_num x e)
  | WT_If_X: forall st ast_num e c1 c2,
      well_typed_exp_x st e -> 
      (* have to constrain that e is boolean or not ? *)
      (* fetch_exp_type_rt (expression_astnum_rt e) st = Some Boolean -> *)
      well_typed_statement_x st c1 ->
      well_typed_statement_x st c2 ->
      well_typed_statement_x st (IfRT ast_num e c1 c2)
  | WT_While_X: forall st ast_num e c,
      well_typed_exp_x st e -> 
      well_typed_statement_x st c ->
      well_typed_statement_x st (WhileRT ast_num e c)
  | WT_Procedure_Call_X: forall st ast_num f_ast_num f args n fb,
      well_typed_exps_x st args ->
      fetch_proc_rt f st = Some (n, fb) ->
      (* +++ the type of args shold match the type of params *)
      well_typed_args_x st args (procedure_parameter_profile_rt fb) ->
      well_typed_statement_x st (CallRT ast_num f_ast_num f args)
  | WT_Sequence_X: forall st ast_num c1 c2,
      well_typed_statement_x st c1 ->
      well_typed_statement_x st c2 ->
      well_typed_statement_x st (SeqRT ast_num c1 c2).

(** * Well-Typed Declaration *)

Inductive well_typed_type_decl_x: symTabRT -> typeDeclRT -> Prop :=
  | WT_Subtype_Decl_X: forall st ast_num tid t r,
      well_typed_type_decl_x st (SubtypeDeclRT ast_num tid t r)
  | WT_Derived_Type_Decl_X: forall st ast_num tid t r,
      well_typed_type_decl_x st (DerivedTypeDeclRT ast_num tid t r)
  | WT_Int_Type_Decl_X: forall st ast_num tid r,
      well_typed_type_decl_x st (IntegerTypeDeclRT ast_num tid r)
  | WT_Array_Type_Decl_X: forall st ast_num tid tm t,
      well_typed_type_decl_x st (ArrayTypeDeclRT ast_num tid tm t)
  | WT_Record_Type_Decl_X: forall st ast_num tid fs,
      well_typed_type_decl_x st (RecordTypeDeclRT ast_num tid fs).

Inductive well_typed_decl_x: symTabRT -> declRT -> Prop :=
  | WT_Null_Decl_X: forall st,
      well_typed_decl_x st NullDeclRT
  | WT_Type_Decl_X: forall st ast_num type_decl,
      well_typed_type_decl_x st type_decl ->
      well_typed_decl_x st (TypeDeclRT ast_num type_decl)
  | WT_Object_Decl_None_Init_X: forall st ast_num d m,
      d.(initialization_expRT) = None ->
      fetch_var_rt d.(object_nameRT) st = Some (m, d.(object_nominal_subtype_rt)) ->
      well_typed_decl_x st (ObjDeclRT ast_num d)
  | WT_Object_Decl_X: forall st ast_num d e m t,
      d.(initialization_expRT) = Some e ->
      fetch_var_rt d.(object_nameRT) st = Some (m, d.(object_nominal_subtype_rt)) ->
      well_typed_exp_x st e ->
      fetch_exp_type_rt (expression_astnum_rt e) st = Some t ->
      (* type of the initialization expression should match the type of declared object *)
      type_match t d.(object_nominal_subtype_rt) = true ->
      well_typed_decl_x st (ObjDeclRT ast_num d)
  | WT_Procedure_Body_X: forall st ast_num fb,
      well_typed_proc_body_x st fb ->
      well_typed_decl_x st (ProcBodyDeclRT ast_num fb)
  | WT_Seq_Decl_X: forall st ast_num d1 d2,
      well_typed_decl_x st d1 ->
      well_typed_decl_x st d2 ->
      well_typed_decl_x st (SeqDeclRT ast_num d1 d2)

with well_typed_proc_body_x: symTabRT -> procBodyDeclRT -> Prop :=
  | WT_Proc_Body_X: forall st p,
      well_typed_params_x st (procedure_parameter_profile_rt p) ->
      well_typed_decl_x st (procedure_declarative_part_rt p) ->
      well_typed_statement_x st (procedure_statements_rt p) ->
      well_typed_proc_body_x st p.

(******************************************************************)
(******************************************************************)

(** * well typed symbol table *)

(**
  - SubtypeDeclRT astnum typenum type range_x: "range_x" should be in the range of "type"
  - Derived_Type_Declaration_X astnum typenum type range_x: "range_x" should be in the range of "type"
  - Integer_Type_Declaration_X astnum typenum range_x: "range_x" should be in the range of "int32"
  here in order to make the proof feasible, it's enough to have the subtype range within "int32"
*)

Inductive well_typed_subtype_declaration: symTabRT -> Prop :=
  | TSubtypeDecl: forall st, 
 (* (forall t td l u, 
      fetch_type_rt t st = Some td ->
        subtype_range_x td = Some (RangeRT l u) ->
          sub_bound (Interval l u) int32_bound true) -> *)
    (forall t l u, 
       extract_subtype_range_rt st t (RangeRT l u) ->
         sub_bound (Interval l u) int32_bound true) -> 
    well_typed_subtype_declaration st.
  
Inductive well_typed_proc_declaration: symTabRT -> Prop :=
  | TProcDecl: forall st,
    (forall f n p, fetch_proc_rt f st = Some (n, p) -> 
                   well_typed_proc_body_x st p) ->
    well_typed_proc_declaration st.

Inductive well_typed_symbol_table: symTabRT -> Prop :=
  | TSymbolTable: forall st, 
      well_typed_subtype_declaration st ->
      well_typed_proc_declaration st ->
      well_typed_symbol_table st.


(******************************************************************)
(******************************************************************)

(** * Well-Typed Value *)

Inductive well_typed_value: symTabRT -> type -> value -> Prop := 
  | TV_Undefined: forall st t,
      well_typed_value st t Undefined (*Undefined can be value of any type*)
  | TV_Bool: forall st v,
      v = true \/ v = false ->
      well_typed_value st Boolean (Bool v)
  | TV_Int: forall st v,
      in_bound v int32_bound true ->
      well_typed_value st Integer (Int v)
  | TV_Subtype: forall st t l u v,
      extract_subtype_range_rt st (Subtype t) (RangeRT l u) ->
      in_bound v (Interval l u) true ->
      well_typed_value st (Subtype t) (Int v)
  | TV_Derived_Type: forall st t l u v,
      extract_subtype_range_rt st (Derived_Type t) (RangeRT l u) ->
      in_bound v (Interval l u) true ->
      well_typed_value st (Derived_Type t) (Int v)
  | TV_Integer_Type: forall st t l u v,
      extract_subtype_range_rt st (Integer_Type t) (RangeRT l u) ->
      in_bound v (Interval l u) true ->
      well_typed_value st (Integer_Type t) (Int v)
  | TV_Array_Type: forall st t ast_num tid tm typ a l u,
      fetch_type_rt t st = Some (ArrayTypeDeclRT ast_num tid tm typ) ->
      extract_array_index_range_rt st t (RangeRT l u) ->
      (forall i v, (* for value within the index range *)
         array_select a i = Some v ->
         (rangeCheck i l u (OK (Int i)) /\ well_typed_value st typ v /\ v <> Undefined)) ->
      well_typed_value st (Array_Type t) (ArrayV a)
  | TV_Record_Type: forall st t ast_num tid fields r,
      fetch_type_rt t st = Some (RecordTypeDeclRT ast_num tid fields) ->
      (* ????? *)
      (*
      (forall f v typ, 
         record_select r f = Some v -> 
         record_field_type fields f = Some typ -> (* selected record field's type *)
         well_typed_value st typ v) ->
      *)
      (* ???? represented as the above or in the following way ??? *)
      (forall f v, 
         record_select r f = Some v -> 
         exists typ, (record_field_type fields f = Some typ /\ well_typed_value st typ v /\ v <> Undefined)) ->
      well_typed_value st (Record_Type t) (RecordV r).

(** * Well-Typed Store *)
Inductive well_typed_store: symTabRT -> store -> Prop :=
  | TStore: forall st s,
      (forall x v,
        fetches x s = Some v ->
       exists m t, fetch_var_rt x st = Some (m, t) /\ well_typed_value st t v) ->
      well_typed_store st s.

Inductive well_typed_value_in_store: symTabRT -> store -> Prop :=
  | TVStore_Nil: forall st,
      well_typed_value_in_store st nil
  | TVStore: forall st s x v,
      (exists m t, fetch_var_rt x st = Some (m, t) /\ well_typed_value st t v) ->
      well_typed_value_in_store st s ->
      well_typed_value_in_store st ((x, v) :: s).

Lemma well_typed_store_infer: forall st s,
  well_typed_value_in_store st s ->
    well_typed_store st s.
Proof.
  intros st s; revert st.
  induction s; intros.
- constructor; smack.
- inversion H; subst.
  specialize (IHs _ H4).
  constructor; smack.
  remember (beq_nat x0 x) as b.
  destruct b; smack.
  + rewrite (beq_nat_eq _ _ Heqb).
    exists x1 x2; smack.
  + inversion IHs; smack.
Qed.

Ltac apply_well_typed_store_infer := 
  match goal with
  | [H: well_typed_value_in_store ?st ?s |- _] =>
      specialize (well_typed_store_infer _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * Well-Typed State *)
(** for any variable in state, its value should be in the domain of its type;
    for any procedure declaration in symbol table, the procedure is well-typed;
 *)

Inductive well_typed_stack: symTabRT -> state -> Prop :=
  | TStack: forall st s,
      (forall x v,
         fetchG x s = Some v ->
         exists m t, fetch_var_rt x st = Some (m, t) /\ well_typed_value st t v) ->
      well_typed_stack st s.

Inductive well_typed_value_in_stack: symTabRT -> state -> Prop :=
  | TVStack_Nil: forall st,
      well_typed_value_in_stack st nil 
  | TVStack: forall st s f, 
      well_typed_value_in_store st (snd f) ->
      well_typed_value_in_stack st s ->
      well_typed_value_in_stack st (f :: s).

Lemma well_typed_stack_infer: forall st s,
  well_typed_value_in_stack st s ->
    well_typed_stack st s.
Proof.
  intros st s; revert st.
  induction s; intros.
- constructor; smack.
- inversion H; subst.
  specialize (IHs _ H4).
  constructor; smack.
  remember (fetch x a) as y.
  destruct y.
  + inversion H0; subst.
    apply_well_typed_store_infer.
    inversion HZ; smack.
  + inversion IHs; smack.
Qed.

Ltac apply_well_typed_stack_infer :=
  match goal with
  | [H: well_typed_value_in_stack ?st ?s |- _] =>
      specialize (well_typed_stack_infer _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

(******************************************************************)
(******************************************************************)

(** * Well-Typed State and Symbol Table *)
Inductive well_typed_stack_and_symboltable: symTabRT -> state -> Prop :=
  | TStack_SymbolTable: forall st s,
      well_typed_value_in_stack st s ->
      well_typed_symbol_table st ->
      well_typed_stack_and_symboltable st s.

Ltac combine_well_typed_stack_and_symboltable := 
  match goal with
  | [H1: well_typed_value_in_stack ?st ?s,
     H2: well_typed_symbol_table ?st |- _] =>
      specialize (TStack_SymbolTable _ _ H1 H2); 
      let HZ := fresh "HZ" in intros HZ
  end.

(*
Inductive well_typed_stack: symTabRT -> state -> Prop :=
  | TStack: forall st s,
      (forall x v,
         fetchG x s = Some v ->
         exists m t, fetch_var_rt x st = Some (m, t) /\ well_typed_value st t v) ->
      (forall f n p, 
         fetch_proc_rt f st = Some (n, p) ->
         well_typed_proc_body_x st p) ->
      well_typed_stack st s.
*)




