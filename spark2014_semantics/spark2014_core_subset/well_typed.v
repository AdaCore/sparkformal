Require Export semantics_flagged.
Require Export checks_optimization.

Import STACK.


(** * Helper Functions *)

(** ** the type of the expression *)

Definition type_of_name_x (st: symboltable_x) (n: name_x): option type :=
  match n with
  | E_Identifier_X ast_num _ _ => fetch_exp_type_x ast_num st
  | E_Indexed_Component_X ast_num _ _ _ => fetch_exp_type_x ast_num st
  | E_Selected_Component_X ast_num _ _ _ => fetch_exp_type_x ast_num st
  end.

Definition type_of_exp_x (st: symboltable_x) (e: expression_x): option type :=
  match e with
  | E_Literal_X _ (Integer_Literal _) _ _ => Some Integer
  | E_Literal_X _ (Boolean_Literal _) _ _ => Some Boolean
  | E_Name_X ast_num n => fetch_exp_type_x ast_num st
  | E_Binary_Operation_X ast_num _ _ _ _ _ => fetch_exp_type_x ast_num st
  | E_Unary_Operation_X ast_num _ _ _ _ => fetch_exp_type_x ast_num st
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
    | Plus | Minus | Multiply | Divide =>
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
    | Unary_Plus =>
        Some t
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
  destruct t, t'; crush;eauto;
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

Inductive well_typed_exp_x: symboltable_x -> expression_x -> Prop :=
  | WT_Literal_Int_X: forall st ast_num v in_cks ex_cks,
      fetch_exp_type_x ast_num st = Some Integer ->
      well_typed_exp_x st (E_Literal_X ast_num (Integer_Literal v) in_cks ex_cks)
  | WT_Literal_Bool_X: forall st ast_num v in_cks ex_cks,
      fetch_exp_type_x ast_num st = Some Boolean ->
      well_typed_exp_x st (E_Literal_X ast_num (Boolean_Literal v) in_cks ex_cks)
  | WT_Name_X: forall st ast_num n,
      fetch_exp_type_x ast_num st = fetch_exp_type_x (name_astnum_x n) st ->
      well_typed_name_x st n ->
      well_typed_exp_x st (E_Name_X ast_num n)
  | WT_Binary_Exp_X: forall st ast_num op e1 e2 in_cks ex_cks t t1 t2,
      well_typed_exp_x st e1 ->
      well_typed_exp_x st e2 ->
      fetch_exp_type_x ast_num st = Some t -> (* binary expression's type *)
      type_of_exp_x st e1 = Some t1 -> type_of_exp_x st e2 = Some t2 -> 
      binop_type op t1 t2 = Some t -> (* binary expression's type *)
      well_typed_exp_x st (E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks)
  | WT_Unary_Exp_X: forall st ast_num op e in_cks ex_cks t t',
      well_typed_exp_x st e ->
      fetch_exp_type_x ast_num st = Some t -> (* unary expression's type *)
      type_of_exp_x st e = Some t' ->
      unop_type op t' = Some t -> (* unary expression's type *)
      well_typed_exp_x st (E_Unary_Operation_X ast_num op e in_cks ex_cks)

with well_typed_name_x: symboltable_x -> name_x -> Prop :=
  | WT_Identifier_X: forall st ast_num x ex_cks md t,
      fetch_exp_type_x ast_num st = Some t ->
      fetch_var_x x st = Some (md, t) ->
      well_typed_name_x st (E_Identifier_X ast_num x ex_cks)
  | WT_Indexed_Component_X: forall st ast_num x e ex_cks t t' a_ast_num tn tm,
      well_typed_name_x st x ->
      well_typed_exp_x st e ->
      fetch_exp_type_x ast_num st = Some t -> (* indexed component's type *)
      fetch_exp_type_x (name_astnum_x x) st = Some (Array_Type t') ->
      fetch_type_x t' st = Some (Array_Type_Declaration_X a_ast_num tn tm t) -> (* array element's type *)
      well_typed_name_x st (E_Indexed_Component_X ast_num x e ex_cks)
  | WT_Selected_Component_X: forall st ast_num x f ex_cks t t' r_ast_num tn fields,
      well_typed_name_x st x ->
      fetch_exp_type_x ast_num st = Some t -> (* selected component's type *)
      fetch_exp_type_x (name_astnum_x x) st = Some (Record_Type t') ->
      fetch_type_x t' st = Some (Record_Type_Declaration_X r_ast_num tn fields) ->
      record_field_type fields f = Some t -> (* selected record field's type *)
      well_typed_name_x st (E_Selected_Component_X ast_num x f ex_cks).

Inductive well_typed_exps_x: symboltable_x -> list expression_x -> Prop :=
  | WT_Exps_Nil_X: forall st,
      well_typed_exps_x st nil
  | WT_Exps_X: forall st e le,
      well_typed_exp_x  st e  ->
      well_typed_exps_x st le ->
      well_typed_exps_x st (e :: le).

Inductive well_typed_params_x: symboltable_x -> list parameter_specification_x -> Prop :=
  | WT_Params_Nil_X: forall st,
      well_typed_params_x st nil
  | WT_Params_X: forall st m x lx,
      fetch_var_x x.(parameter_name_x) st = Some (m, x.(parameter_subtype_mark_x)) ->
      well_typed_params_x st lx ->
      well_typed_params_x st (x :: lx).

Inductive well_typed_args_x: symboltable_x -> list expression_x -> list parameter_specification_x -> Prop :=
  | WT_Args_Nil_X: forall st,
      well_typed_args_x st nil nil
  | WT_Args_X: forall st e le x lx t,
      fetch_exp_type_x (expression_astnum_x e) st = Some t ->
      (* argument's type should match its parameter's type *)
      type_match t x.(parameter_subtype_mark_x) = true ->
      well_typed_args_x st le lx ->
      well_typed_args_x st (e :: le) (x :: lx).

(** * Well-Typed Statement *)

Inductive well_typed_statement_x: symboltable_x -> statement_x -> Prop :=
  | WT_Null_X: forall st,
      well_typed_statement_x st S_Null_X
  | WT_Assignment_X: forall st ast_num x e t t',
      well_typed_exp_x st e ->
      well_typed_name_x st x ->
      fetch_exp_type_x (expression_astnum_x e) st = Some t ->
      fetch_exp_type_x (name_astnum_x x) st = Some t' ->
      (* +++ right-hand-side exp's type should be compatible with the left-hand-side exp's type *)
      type_match t t' = true ->
      well_typed_statement_x st (S_Assignment_X ast_num x e)
  | WT_If_X: forall st ast_num e c1 c2,
      well_typed_exp_x st e -> 
      (* have to constrain that e is boolean or not ? *)
      (* fetch_exp_type_x (expression_astnum_x e) st = Some Boolean -> *)
      well_typed_statement_x st c1 ->
      well_typed_statement_x st c2 ->
      well_typed_statement_x st (S_If_X ast_num e c1 c2)
  | WT_While_X: forall st ast_num e c,
      well_typed_exp_x st e -> 
      well_typed_statement_x st c ->
      well_typed_statement_x st (S_While_Loop_X ast_num e c)
  | WT_Procedure_Call_X: forall st ast_num f_ast_num f args n fb,
      well_typed_exps_x st args ->
      fetch_proc_x f st = Some (n, fb) ->
      (* +++ the type of args shold match the type of params *)
      well_typed_args_x st args (procedure_parameter_profile_x fb) ->
      well_typed_statement_x st (S_Procedure_Call_X ast_num f_ast_num f args)
  | WT_Sequence_X: forall st ast_num c1 c2,
      well_typed_statement_x st c1 ->
      well_typed_statement_x st c2 ->
      well_typed_statement_x st (S_Sequence_X ast_num c1 c2).

(** * Well-Typed Declaration *)

Inductive well_typed_type_decl_x: symboltable_x -> type_declaration_x -> Prop :=
  | WT_Subtype_Decl_X: forall st ast_num tid t r,
      well_typed_type_decl_x st (Subtype_Declaration_X ast_num tid t r)
  | WT_Derived_Type_Decl_X: forall st ast_num tid t r,
      well_typed_type_decl_x st (Derived_Type_Declaration_X ast_num tid t r)
  | WT_Int_Type_Decl_X: forall st ast_num tid r,
      well_typed_type_decl_x st (Integer_Type_Declaration_X ast_num tid r)
  | WT_Array_Type_Decl_X: forall st ast_num tid tm t,
      well_typed_type_decl_x st (Array_Type_Declaration_X ast_num tid tm t)
  | WT_Record_Type_Decl_X: forall st ast_num tid fs,
      well_typed_type_decl_x st (Record_Type_Declaration_X ast_num tid fs).

Inductive well_typed_decl_x: symboltable_x -> declaration_x -> Prop :=
  | WT_Null_Decl_X: forall st,
      well_typed_decl_x st D_Null_Declaration_X
  | WT_Type_Decl_X: forall st ast_num type_decl,
      well_typed_type_decl_x st type_decl ->
      well_typed_decl_x st (D_Type_Declaration_X ast_num type_decl)
  | WT_Object_Decl_None_Init_X: forall st ast_num d m,
      d.(initialization_expression_x) = None ->
      fetch_var_x d.(object_name_x) st = Some (m, d.(object_nominal_subtype_x)) ->
      well_typed_decl_x st (D_Object_Declaration_X ast_num d)
  | WT_Object_Decl_X: forall st ast_num d e m t,
      d.(initialization_expression_x) = Some e ->
      fetch_var_x d.(object_name_x) st = Some (m, d.(object_nominal_subtype_x)) ->
      well_typed_exp_x st e ->
      fetch_exp_type_x (expression_astnum_x e) st = Some t ->
      (* type of the initialization expression should match the type of declared object *)
      type_match t d.(object_nominal_subtype_x) = true ->
      well_typed_decl_x st (D_Object_Declaration_X ast_num d)
  | WT_Procedure_Body_X: forall st ast_num fb,
      well_typed_proc_body_x st fb ->
      well_typed_decl_x st (D_Procedure_Body_X ast_num fb)
  | WT_Seq_Decl_X: forall st ast_num d1 d2,
      well_typed_decl_x st d1 ->
      well_typed_decl_x st d2 ->
      well_typed_decl_x st (D_Seq_Declaration_X ast_num d1 d2)

with well_typed_proc_body_x: symboltable_x -> procedure_body_x -> Prop :=
  | WT_Proc_Body_X: forall st p,
      well_typed_params_x st (procedure_parameter_profile_x p) ->
      well_typed_decl_x st (procedure_declarative_part_x p) ->
      well_typed_statement_x st (procedure_statements_x p) ->
      well_typed_proc_body_x st p.

(******************************************************************)
(******************************************************************)

(** * well typed symbol table *)

(**
  - Subtype_Declaration_X astnum typenum type range_x: "range_x" should be in the range of "type"
  - Derived_Type_Declaration_X astnum typenum type range_x: "range_x" should be in the range of "type"
  - Integer_Type_Declaration_X astnum typenum range_x: "range_x" should be in the range of "int32"
  here in order to make the proof feasible, it's enough to have the subtype range within "int32"
*)

Inductive well_typed_subtype_declaration: symboltable_x -> Prop :=
  | TSubtypeDecl: forall st, 
 (* (forall t td l u, 
      fetch_type_x t st = Some td ->
        subtype_range_x td = Some (Range_X l u) ->
          sub_bound (Interval l u) int32_bound true) -> *)
    (forall t l u, 
       extract_subtype_range_x st t (Range_X l u) ->
         sub_bound (Interval l u) int32_bound true) ->
    well_typed_subtype_declaration st.
  
Inductive well_typed_proc_declaration: symboltable_x -> Prop :=
  | TProcDecl: forall st,
    (forall f n p, fetch_proc_x f st = Some (n, p) -> 
                   well_typed_proc_body_x st p) ->
    well_typed_proc_declaration st.

Inductive well_typed_symbol_table: symboltable_x -> Prop :=
  | TSymbolTable: forall st, 
      well_typed_subtype_declaration st ->
      well_typed_proc_declaration st ->
      well_typed_symbol_table st.


(******************************************************************)
(******************************************************************)

(** * Well-Typed Value *)

Inductive well_typed_value: symboltable_x -> type -> value -> Prop := 
  | TV_Undefined: forall st t,
      well_typed_value st t Undefined (*Undefined can be value of any type*)
  | TV_Bool: forall st v,
      v = true \/ v = false ->
      well_typed_value st Boolean (Bool v)
  | TV_Int: forall st v,
      in_bound v int32_bound true ->
      well_typed_value st Integer (Int v)
  | TV_Subtype: forall st t l u v,
      extract_subtype_range_x st (Subtype t) (Range_X l u) ->
      in_bound v (Interval l u) true ->
      well_typed_value st (Subtype t) (Int v)
  | TV_Derived_Type: forall st t l u v,
      extract_subtype_range_x st (Derived_Type t) (Range_X l u) ->
      in_bound v (Interval l u) true ->
      well_typed_value st (Derived_Type t) (Int v)
  | TV_Integer_Type: forall st t l u v,
      extract_subtype_range_x st (Integer_Type t) (Range_X l u) ->
      in_bound v (Interval l u) true ->
      well_typed_value st (Integer_Type t) (Int v)
  | TV_Array_Type: forall st t ast_num tid tm typ a l u,
      fetch_type_x t st = Some (Array_Type_Declaration_X ast_num tid tm typ) ->
      extract_array_index_range_x st t (Range_X l u) ->
      (forall i v, (* for value within the index range *)
         array_select a i = Some v ->
         (do_range_check i l u (Normal (Int i)) /\ well_typed_value st typ v)) ->
      well_typed_value st (Array_Type t) (ArrayV a)
  | TV_Record_Type: forall st t ast_num tid fields r,
      fetch_type_x t st = Some (Record_Type_Declaration_X ast_num tid fields) ->
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
         exists typ, (record_field_type fields f = Some typ /\ well_typed_value st typ v)) ->
      well_typed_value st (Record_Type t) (RecordV r).

(** * Well-Typed Store *)
Inductive well_typed_store: symboltable_x -> store -> Prop :=
  | TStore: forall st s,
      (forall x v,
        fetches x s = Some v ->
       exists m t, fetch_var_x x st = Some (m, t) /\ well_typed_value st t v) ->
      well_typed_store st s.

Inductive well_typed_value_in_store: symboltable_x -> store -> Prop :=
  | TVStore_Nil: forall st,
      well_typed_value_in_store st nil
  | TVStore: forall st s x v,
      (exists m t, fetch_var_x x st = Some (m, t) /\ well_typed_value st t v) ->
      well_typed_value_in_store st s ->
      well_typed_value_in_store st ((x, v) :: s).

Lemma well_typed_store_infer: forall st s,
  well_typed_value_in_store st s ->
    well_typed_store st s.
Proof.
  intros st s; revert st.
  induction s; intros.
- constructor; crush;eauto.
- inversion H; subst.
  specialize (IHs _ H4).
  constructor; crush;eauto.
  remember (beq_nat x0 x) as b.
  destruct b; crush;eauto.
  + rewrite (beq_nat_eq _ _ Heqb).
    exists x1 x2; crush;eauto.
  + inversion IHs; crush;eauto.
Qed.

Ltac apply_well_typed_store_infer := 
  match goal with
  | [H: well_typed_value_in_store ?st ?s |- _] =>
      specialize (well_typed_store_infer _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * Well-Typed Stack *)
(** for any variable in stack, its value should be in the domain of its type;
    for any procedure declaration in symbol table, the procedure is well-typed;
 *)

Inductive well_typed_stack: symboltable_x -> stack -> Prop :=
  | TStack: forall st s,
      (forall x v,
         fetchG x s = Some v ->
         exists m t, fetch_var_x x st = Some (m, t) /\ well_typed_value st t v) ->
      well_typed_stack st s.

Inductive well_typed_value_in_stack: symboltable_x -> stack -> Prop :=
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
- constructor; crush;eauto.
- inversion H; subst.
  specialize (IHs _ H4).
  constructor; crush;eauto.
  remember (fetch x a) as y.
  destruct y.
  + inversion H0; subst.
    apply_well_typed_store_infer.
    inversion HZ; crush;eauto.
  + inversion IHs; crush;eauto.
Qed.

Ltac apply_well_typed_stack_infer :=
  match goal with
  | [H: well_typed_value_in_stack ?st ?s |- _] =>
      specialize (well_typed_stack_infer _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

(******************************************************************)
(******************************************************************)

(** * Well-Typed Stack and Symbol Table *)
Inductive well_typed_stack_and_symboltable: symboltable_x -> stack -> Prop :=
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
Inductive well_typed_stack: symboltable_x -> stack -> Prop :=
  | TStack: forall st s,
      (forall x v,
         fetchG x s = Some v ->
         exists m t, fetch_var_x x st = Some (m, t) /\ well_typed_value st t v) ->
      (forall f n p, 
         fetch_proc_x f st = Some (n, p) ->
         well_typed_proc_body_x st p) ->
      well_typed_stack st s.
*)




