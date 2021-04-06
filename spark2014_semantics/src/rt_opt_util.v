(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export rt_opt.


Scheme expression_ind := Induction for exp Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expRT Sort Prop 
                         with name_x_ind := Induction for nameRT Sort Prop.

(** * Helper Lemmas for RT-OPT *)

(** ** in_bound Lemmas *)

Lemma In_Bound_Refl: forall v,
  in_bound v (Interval v v) true.
Proof.
  intros; constructor;
  specialize (Z.le_refl v). intros H0.
  specialize (Zle_imp_le_bool _ _ H0); 
    intros H1; rewrite H1; auto.
Qed.

Lemma in_bound_conflict: forall v bound,
  in_bound v bound true ->
    in_bound v bound false ->
      False.
Proof.
  intros.
  inversion H; inversion H0; smack.
Qed.

Ltac apply_in_bound_conflict :=
  match goal with
  | [H1: in_bound ?v ?bound true, 
     H2: in_bound ?v ?bound false |- _] => specialize (in_bound_conflict _ _ H1 H2)
  end.

(** l <= v <= u, l' <= l <= u', l' <= u <= u' => l' <= v <= u', where vBound = (l', u') *)
Lemma In_Bound_Trans: forall v l u vBound,
  in_bound v (Interval l u) true ->
    in_bound l vBound true ->
      in_bound u vBound true ->
        in_bound v vBound true.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  constructor; apply andb_true_iff; split.
- specialize (Z.le_trans _ _ _ H3 H0); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
- specialize (Z.le_trans _ _ _ H1 H5); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
Qed.

Ltac apply_In_Bound_Trans :=
  match goal with
  | [H1: in_bound ?v (Interval ?l ?u) true,
     H2: in_bound ?l _ true,
     H3: in_bound ?u _ true |- _ ] =>
      specialize (In_Bound_Trans _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


Lemma In_Bound_SubBound_Trans: forall v vBound vBound',
  in_bound v vBound true ->
    sub_bound vBound vBound' true ->
      in_bound v vBound' true.
Proof.
  intros;
  inversion H0; subst;
  apply_In_Bound_Trans; auto.
Qed.

Ltac apply_In_Bound_SubBound_Trans :=
  match goal with
  | [H1: in_bound _ ?b true,
     H2: sub_bound ?b _ true |- _] =>
      specialize (In_Bound_SubBound_Trans _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma In_Bound_Two: forall v l u l' u',
  in_bound v (Interval l u) true ->
    in_bound v (Interval l' u') true ->
      in_bound v (Interval (Z.max l l') (Z.min u u')) true.
Proof.
  intros.
  inversion H; inversion H0; subst; clear H H0.
  constructor; auto.
  specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H3); intro HZ1.
  specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H7); intro HZ2.
  destruct HZ1 as [HZ1a HZ1b]. destruct HZ2 as [HZ2a HZ2b].
  specialize (Z.max_lub _ _ _ HZ1a HZ2a); intro HZ3.
  specialize (Z.min_glb _ _ _ HZ1b HZ2b); intro HZ4.
  clear HZ1a HZ1b HZ2a HZ2b.
  repeat progress match goal with
  | [H: (?l <= ?v)%Z |- _] => 
      specialize (Zle_imp_le_bool _ _ H); clear H; let HZ := fresh "HZ" in intro HZ
  end; smack.
Qed.


Ltac apply_In_Bound_Two :=
  match goal with
  | [H1: in_bound ?v (Interval ?l ?u) true,
     H2: in_bound ?v (Interval ?l' ?u') true |- _ ] => 
      specialize (In_Bound_Two _ _ _ _ _ H1 H2); let HZ := fresh "HZ" in intro HZ
  end.

Lemma modulus_in_int32_bound: forall v1 v2,
  in_bound v2 int32_bound true -> 
    in_bound (v1 mod v2) int32_bound true.
Proof.
  intros.
  destruct v2; constructor; smack.
 - rewrite Zmod_0_r. smack.
 - assert(HA1: ((Z.pos p) > 0)%Z). smack.
   specialize (Z_mod_lt v1 _ HA1); intro HZ2.
   destruct HZ2 as [HZ2a HZ2b].
   assert(HZ3a: (0 <=? v1 mod Z.pos p)%Z = true).
     apply Zleb_le; auto.
   assert(HZ3b: (v1 mod Z.pos p <? Z.pos p)%Z = true).
     apply Zltb_lt; auto.

   inversion H; subst.
   remember ((min_signed <=? Z.pos p)%Z) as HZ4a.
   remember ((Z.pos p <=? max_signed)%Z) as HZ4b.
   destruct HZ4a, HZ4b; inversion H2.
   assert(HC1: (min_signed <=? v1 mod Z.pos p)%Z = true).
     apply Zle_bool_trans with (m := 0%Z); smack.
   assert(HC2: (v1 mod Z.pos p <=? max_signed)%Z = true).
     apply Zltb_leb_trans_leb with (Z.pos p); smack.
   smack.
 - assert(HA1: ((Z.neg p) < 0)%Z). constructor; auto.
   specialize (Z_mod_neg v1 _ HA1); intro HZ2.
   destruct HZ2 as [HZ2a HZ2b].
   assert(HZ3a: (Z.neg p <? v1 mod Z.neg p)%Z = true).
     apply Zltb_lt; auto.
   assert(HZ3b: (v1 mod Z.neg p <=? 0)%Z = true).
     apply Zleb_le; auto.

   inversion H; subst.
   remember ((min_signed <=? Z.neg p)%Z) as HZ4a.
   remember ((Z.neg p <=? max_signed)%Z) as HZ4b.
   destruct HZ4a, HZ4b; inversion H2.
   assert(HC1: (min_signed <=? v1 mod Z.neg p)%Z = true).
     apply Zleb_ltb_trans_leb with (Z.neg p); smack.
   assert(HC2: (v1 mod Z.neg p <=? max_signed)%Z = true).
     apply Zleb_ltb_trans_leb with (0%Z); smack.
   rewrite HC1, HC2; auto.
Qed.

Lemma modulus_in_bound_trans: forall v1 v2 bound,
  sub_bound bound int32_bound true ->
    in_bound v2 bound true -> 
      in_bound (v1 mod v2) int32_bound true.
Proof.
  intros.
  apply_In_Bound_SubBound_Trans.
  apply modulus_in_int32_bound; auto.
Qed.
  
(** l1 <= v1 <= u1, l2 <= v2 <= u2 => (l1+l2) <= (v1+v2) <= (u1+u2) *)
Lemma In_Bound_Plus_Compat: forall v1 l1 u1 v2 l2 u2,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1+v2) (Interval (l1+l2) (u1+u2)) true.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  constructor; apply andb_true_iff; split.
- specialize (Zplus_le_compat _ _ _ _ H0 H2); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
- specialize (Zplus_le_compat _ _ _ _ H1 H3); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
Qed.

Ltac apply_In_Bound_Plus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true |- _] => 
      specialize (In_Bound_Plus_Compat _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(** l1 <= v1 <= u1, l2 <= v2 <= u2 => (l1-u2) <= (v1-v2) <= (u1-l2) *)
Lemma In_Bound_Minus_Compat: forall v1 l1 u1 v2 l2 u2,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1-v2) (Interval (l1-u2) (u1-l2)) true.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  constructor; apply andb_true_iff; split.
- specialize (Le_Neg_Ge _ _ H3); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H0 HZ1); intros HZ2;
  specialize (Zle_imp_le_bool _ _ HZ2); auto.
- specialize (Le_Neg_Ge _ _ H2); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H1 HZ1); intros HZ2;
  specialize (Zle_imp_le_bool _ _ HZ2); auto.
Qed.

Ltac apply_In_Bound_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true |- _] => 
      specialize (In_Bound_Minus_Compat _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Plus_Compat: forall v1 l1 u1 v2 l2 u2 vBound,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1+v2) vBound false ->
        sub_bound (Interval (l1 + l2) (u1 + u2)) vBound false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  constructor.
- specialize (Zplus_le_compat _ _ _ _ H0 H3); intros HZ1.
  specialize (Z.le_lt_trans _ _ _ HZ1 H2); intros HZ2.
  left. constructor.
  apply andb_false_iff; left.
  apply Lt_Le_Bool_False; auto.
- specialize (Zplus_le_compat _ _ _ _ H1 H4); intros HZ1.
  specialize (Z.lt_le_trans  _ _ _ H2 HZ1); intros HZ2.
  right; constructor.
  apply andb_false_iff; right.
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Plus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true,
     H3: in_bound (?v1+?v2) _ false |- _] => 
      specialize (Sub_Bound_Plus_Compat _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Minus_Compat: forall v1 l1 u1 v2 l2 u2 vBound,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1-v2) vBound false ->
        sub_bound (Interval (l1 - u2) (u1 - l2)) vBound false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  constructor.
- specialize (Le_Neg_Ge _ _ H4); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H0 HZ1); intros HZ2;
  specialize (Z.le_lt_trans _ _ _ HZ2 H2); intros HZ3;
  left; constructor;
  apply andb_false_iff; left;
  apply Lt_Le_Bool_False; auto.
- specialize (Le_Neg_Ge _ _ H3); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H1 HZ1); intros HZ2;
  specialize (Z.lt_le_trans  _ _ _ H2 HZ2); intros HZ3;
  right; constructor;
  apply andb_false_iff; right;
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true,
     H3: in_bound (?v1-?v2) _ false |- _] => 
      specialize (Sub_Bound_Minus_Compat _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Unary_Minus_Compat: forall v l u vBound,
  in_bound v (Interval l u) true ->
    in_bound (- v) vBound false ->
      sub_bound (Interval (- u) (- l)) vBound false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
 match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  constructor;
  [left | right];
  constructor.
- apply andb_false_iff; left;
  specialize (Le_Neg_Ge _ _ H2); intros HZ1;
  specialize (Z.le_lt_trans _ _ _ HZ1 H1); intros HZ2;
  apply Lt_Le_Bool_False; auto.
- apply andb_false_iff; right;
  specialize (Le_Neg_Ge _ _ H0); intros HZ1;
  specialize (Z.lt_le_trans _ _ _ H1 HZ1); intros HZ2;
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Unary_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v _ true,
     H2: in_bound (- ?v) _ false |- _] =>
      specialize (Sub_Bound_Unary_Minus_Compat _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma In_Bound_Unary_Minus_Compat: forall v l u,
  in_bound v (Interval l u) true ->
    in_bound (- v) (Interval (- u) (- l)) true.
Proof.
  intros.
  inversion H; clear H; subst.
  constructor.
  (* smack or lia solves the goal here in v8.13 *)
  specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H2).
  intuition.
  specialize (Le_Neg_Ge _ _ H0); intros HZ1.
  specialize (Le_Neg_Ge _ _ H1); intros HZ2.
  specialize (Zle_imp_le_bool  _ _ HZ1); intros HZ3.
  specialize (Zle_imp_le_bool  _ _ HZ2); intros HZ4.
  smack.
Qed.

Lemma in_bound_value_neq_zero: forall v vBound,
  in_bound v vBound true ->
    in_bound 0 vBound false ->
      Zeq_bool v 0 = false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  [ specialize (Z.lt_le_trans _ _ _ H1 H0); intros HZ1 |
    specialize (Z.le_lt_trans _ _ _ H2 H1); intros HZ1
  ];
  unfold Zeq_bool; 
  destruct v; smack.
Qed.

Ltac apply_in_bound_value_neq_zero :=
  match goal with
  | [H1: in_bound ?v ?b true,
     H2: in_bound 0 ?b false |- _] => 
      specialize (in_bound_value_neq_zero _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)

(** ** run-time erasion Lemmas *)

Lemma removed_check_flag_notin: forall ck cks cks',
 remove_check_flag ck cks = cks' ->
   ~(List.In ck cks').
Proof.
  induction cks; smack.
  remember (beq_check_flag ck a) as b;
  destruct b; smack.
  destruct ck; smack.
Qed.

Ltac apply_removed_check_flag_notin :=
  match goal with
  | [H: remove_check_flag _ _ = _ |- _] => 
      specialize (removed_check_flag_notin _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | [H: _ = remove_check_flag _ _ |- _] => 
      symmetry in H; specialize (removed_check_flag_notin _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma remove_notin_check_flag: forall ck cks,
  ~(List.In ck cks) ->
    remove_check_flag ck cks = cks.
Proof.
  induction cks; smack.
  remember (beq_check_flag ck a) as b;
  destruct b; smack.
  destruct a; destruct ck; smack.
Qed.

Ltac apply_remove_notin_check_flag :=
  match goal with
  | [H: ~(List.In _ _) |- _] => 
      specialize (remove_notin_check_flag _ _ H); let HZ := fresh "HZ" in intros HZ
  | [H: List.In _ _ -> False |- _] => 
      specialize (remove_notin_check_flag _ _ H); let HZ := fresh "HZ" in intros HZ
  end.

Lemma check_flag_in_reserve: forall ck ck' cks,
  beq_check_flag ck ck' = false ->
    List.In ck (remove_check_flag ck' cks) ->
      List.In ck cks.
Proof.
  induction cks; smack.
  remember (beq_check_flag ck' a) as b;
  destruct b; smack.  
Qed.

Ltac apply_check_flag_in_reserve :=
  match goal with
  | [H1: beq_check_flag ?ck ?ck' = false,
     H2: List.In ?ck (remove_check_flag ?ck' _) |- _] =>
      specialize (check_flag_in_reserve _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma check_flag_in_reserve2: forall ck ck' cks,
  beq_check_flag ck ck' = false ->
    List.In ck cks ->
      List.In ck (remove_check_flag ck' cks).      
Proof.
  induction cks; smack.
  remember (beq_check_flag ck' ck) as b; destruct b; smack.
  destruct ck; destruct ck'; smack.
  remember (beq_check_flag ck' a) as b; destruct b; smack.
Qed.

Ltac apply_check_flag_in_reserve2 :=
  match goal with
  | [ H1: beq_check_flag ?ck _ = false,
      H2: List.In ?ck _ |- _] =>
      specialize (check_flag_in_reserve2 _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.


(********************************************************************)
(********************************************************************)


Lemma in_bound_unique: forall v vBound b1 b2,
  in_bound v vBound b1 ->
    in_bound v vBound b2 ->
      b1 = b2.
Proof.
  intros;
  inversion H; inversion H0; smack.
Qed. 

Ltac apply_in_bound_unique :=
  match goal with
  | [H1: in_bound ?v _ _,
     H2: in_bound ?v _ _ |- _] =>
      specialize (in_bound_unique _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma sub_bound_unique: forall bound1 bound2 b1 b2,
  sub_bound bound1 bound2 b1 ->
    sub_bound bound1 bound2 b2 ->
      b1 = b2.
Proof.
  intros;
  inversion H; inversion H0; smack;
  apply_in_bound_unique.
Qed.

Ltac apply_sub_bound_unique :=
  match goal with
  | [H1: sub_bound ?bound1 _ _,
     H2: sub_bound ?bound1 _ _ |- _] =>
      specialize (sub_bound_unique _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

(********************************************************************)
(********************************************************************)

(** ** RT-OPT exterior checks Lemmas *)

Lemma optimize_name_ast_num_eq: forall st n n' nBound,
  optName st n (n', nBound) ->
    fetch_exp_type_rt (name_astnum_rt n) st = fetch_exp_type_rt (name_astnum_rt n') st.
Proof.
  intros;
  inversion H; smack.
Qed.

Ltac apply_optimize_name_ast_num_eq :=
  match goal with
  | [H: optName _ _ _ |- _] =>
      specialize (optimize_name_ast_num_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_exp_ex_cks_eq: forall st e e' eBound,
  optExp st e (e', eBound) ->
    exp_exterior_checks e' = exp_exterior_checks e.
Proof.
  intros;
  inversion H; smack;
  match goal with
  | [H: optName _ _ _ |- _] => inversion H; smack
  end.
Qed.

Ltac apply_optimize_exp_ex_cks_eq :=
  match goal with
  | [H: optExp _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_name_ex_cks_eq: forall st n n' nBound,
  optName st n (n', nBound) ->
    name_exterior_checks n' = name_exterior_checks n.
Proof.
  intros;
  inversion H; smack.
Qed.

Ltac apply_optimize_name_ex_cks_eq :=
  match goal with
  | [H: optName _ _ _ |- _] => 
      specialize (optimize_name_ex_cks_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma range_check_on_copyout_preserve: forall n ast_num ast_num' nBound nBound' n',
  name_exterior_checks n = RangeCheck :: RangeCheckOnReturn :: nil ->
    optimize_range_check (NameRT ast_num n) nBound nBound' (NameRT ast_num' n') ->
      ~ List.In RangeCheckOnReturn (name_exterior_checks n') ->
        False.
Proof.
  intros.
  inversion H0; subst.
  simpl in H4; smack.
  rewrite H in H1; rewrite name_updated_exterior_checks in H1; smack.
  rewrite H in H1; smack.  
Qed.

Ltac apply_range_check_on_copyout_preserve :=
  match goal with
  | [H1: name_exterior_checks ?n = RangeCheck :: RangeCheckOnReturn :: nil,
     H2: optimize_range_check (NameRT ?ast_num ?n) ?nBound ?nBound' (NameRT ?ast_num' ?n'),
     H3: ~ List.In RangeCheckOnReturn (name_exterior_checks ?n') |- _ ] =>
      specialize (range_check_on_copyout_preserve _ _ _ _ _ _ H1 H2 H3); 
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma range_check_opt_subBound_true: forall e e' eBound eBound',
  exp_exterior_checks e = RangeCheck :: nil ->
    optimize_range_check e eBound eBound' e' ->
      exp_exterior_checks e' = nil ->
        sub_bound eBound eBound' true.
Proof.
  intros.
  inversion H0; subst; rewrite H in *; smack.
Qed.

Ltac apply_range_check_opt_subBound_true :=
  match goal with
  | [H1: exp_exterior_checks ?e = RangeCheck :: nil,
     H2: optimize_range_check ?e ?eBound ?eBound' ?e',
     H3: exp_exterior_checks ?e' = nil |- _] => 
    specialize (range_check_opt_subBound_true _ _ _ _ H1 H2 H3); let HZ := fresh "HZ" in intro HZ
  end.

(** ** Other Lemmas *)

Lemma eval_expr_value_reserve: forall e eBound rBound e' st s v,
  optimize_range_check e eBound rBound e' ->
    evalExpRT st s e v ->
      evalExpRT st s e' v.
Proof.
  intros;
  inversion H; subst; auto;
  apply eval_exp_ex_cks_added; auto.
Qed.

Ltac apply_eval_expr_value_reserve :=
  match goal with
  | [H1: optimize_range_check ?e _ _ _,
     H2: evalExpRT _ _ ?e _ |- _] =>
      specialize (eval_expr_value_reserve _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma eval_expr_value_reserve_backward: forall e eBound rBound e' st s v,
  optimize_range_check e eBound rBound e' ->
    evalExpRT st s e' v ->
      evalExpRT st s e v.
Proof.
  intros;
  inversion H; subst; auto;
  eapply eval_exp_ex_cks_stripped; smack.
Qed.

Ltac apply_eval_expr_value_reserve_backward :=
  match goal with
  | [H1: optimize_range_check ?e _ _ ?e',
     H2: evalExpRT _ _ ?e' _ |- _] =>
      specialize (eval_expr_value_reserve_backward _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma eval_expr_value_copy_out_opt_reserve: forall e eBound rBound e' st s v,
  optimize_range_check_on_copy_out e eBound rBound e' ->
    evalExpRT st s e v ->
      evalExpRT st s e' v.
Proof.
  intros;
  inversion H; subst; auto;
  apply eval_exp_ex_cks_added; auto.
Qed.

Ltac apply_eval_expr_value_copy_out_opt_reserve :=
  match goal with
  | [H1: optimize_range_check_on_copy_out ?e _ _ _,
     H2: evalExpRT _ _ ?e _ |- _] =>
      specialize (eval_expr_value_copy_out_opt_reserve _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.
 
Lemma eval_expr_value_copy_out_opt_reserve_backward: forall e eBound rBound e' st s v,
  optimize_range_check_on_copy_out e eBound rBound e' ->
    evalExpRT st s e' v ->
      evalExpRT st s e v.
Proof.
  intros;
  inversion H; subst; auto;
  eapply eval_exp_ex_cks_stripped; smack.
Qed.

Ltac apply_eval_expr_value_copy_out_opt_reserve_backward :=
  match goal with
  | [H1: optimize_range_check_on_copy_out ?e _ _ ?e',
     H2: evalExpRT _ _ ?e' _ |- _] =>
      specialize (eval_expr_value_copy_out_opt_reserve_backward _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma optimize_range_check_preserve: forall st s ast_num n n' n'' v eBound eBound' eBound'',
  optimize_range_check (NameRT ast_num n) eBound eBound' n' ->
    optimize_range_check_on_copy_out n' eBound' eBound'' n'' ->
      evalNameRT st s n v ->
        evalExpRT st s n'' v /\ exists n1, n'' = NameRT ast_num n1.
Proof.
  intros; constructor.
- apply eval_expr_value_copy_out_opt_reserve with (e:=n') (eBound:=eBound') (rBound:=eBound''); auto.
  apply eval_expr_value_reserve with (e:=(NameRT ast_num n)) (eBound:=eBound) (rBound:=eBound'); auto.
  constructor; auto.
- inversion H; subst; inversion H0; subst; simpl; smack.
Qed.

Ltac apply_optimize_range_check_preserve :=
  match goal with
  [H1: optimize_range_check (NameRT ?ast_num ?n) ?eBound ?eBound' ?n',
   H2: optimize_range_check_on_copy_out ?n' ?eBound' ?eBound'' ?n'',
   H3: evalNameRT ?st ?s ?n ?v |- _] =>
    specialize (optimize_range_check_preserve _ _ _ _ _ _ _ _ _ _ H1 H2 H3);
    let HA := fresh "HA" in 
    let HA1 := fresh "HA" in 
    let HA2 := fresh "HA" in
    intros HA; destruct HA as [HA1 HA2]; destruct HA2; subst
  end.

Lemma optimize_range_check_preserve_backward: forall st s ast_num n n' n'' v eBound eBound' eBound'',
  optimize_range_check (NameRT ast_num n) eBound eBound' n' ->
    optimize_range_check_on_copy_out n' eBound' eBound'' n'' ->
      evalExpRT st s n'' v ->
        evalNameRT st s n v /\ exists n1, n'' = NameRT ast_num n1.
Proof.
  intros; constructor.
- specialize (eval_expr_value_copy_out_opt_reserve_backward _ _ _ _ _ _ _ H0 H1); intros HZ1.
  specialize (eval_expr_value_reserve_backward _ _ _ _ _ _ _ H HZ1); intros HZ2.
  inversion HZ2; auto.
- inversion H; subst; inversion H0; subst; simpl; smack.
Qed.

Ltac apply_optimize_range_check_preserve_backward :=
  match goal with
  [H1: optimize_range_check (NameRT ?ast_num ?n) ?eBound ?eBound' ?n',
   H2: optimize_range_check_on_copy_out ?n' ?eBound' ?eBound'' ?n'',
   H3: evalExpRT ?st ?s ?n'' ?v |- _] =>
    specialize (optimize_range_check_preserve_backward _ _ _ _ _ _ _ _ _ _ H1 H2 H3);
    let HA := fresh "HA" in 
    let HA1 := fresh "HA" in 
    let HA2 := fresh "HA" in
    intros HA; destruct HA as [HA1 HA2]; destruct HA2; subst
  end.

(*******************************************************************)

Lemma remove_check_on_binop_reserve: forall cks op v1 v2 v ck,
  evalBinOpRTS cks op v1 v2 (OK v) ->
    evalBinOpRTS (remove_check_flag ck cks) op v1 v2 (OK v).
Proof.
  intros;
  induction cks; smack;
  match goal with
  | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [|- context[beq_check_flag _ OverflowCheck]] => destruct (beq_check_flag ck OverflowCheck); auto
  | [|- context[beq_check_flag _ DivCheck]] => destruct (beq_check_flag ck DivCheck); auto
  end;
  apply ChecksBinOp with (v:=v4); smack.
Qed.

Lemma safe_remove_binop_check: forall cks op v1 v2 v ck v',
  evalBinOpRTS cks op v1 v2 v ->
    evalBinOpRT ck op v1 v2 (OK v') ->
      evalBinOpRTS (remove_check_flag ck cks) op v1 v2 v.
Proof.
  induction cks; smack;
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: evalBinOpRT ?a _ _ _ _ |- context[?a]] => destruct a; inversion H; smack
  end;
  match goal with
  | [H1: ?x = _, H2: ?x = _ |- _] => rewrite H1 in H2; inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [H1: overflowCheck _ _, 
     H2: overflowCheck _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst; apply_in_bound_unique
  | [H1: divCheck _ _ _ _,
     H2: divCheck _ _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; smack
  | _ => idtac
  end;
  solve
  [ apply ChecksBinOpRTE; auto |
    apply ChecksBinOp with (v:=v5); smack |
    apply ChecksBinOp with (v:=v4); smack
  ].
Qed.

Ltac apply_safe_remove_binop_check :=
  match goal with
  | [H1: evalBinOpRTS _ ?op ?v1 ?v2 _,
     H2: evalBinOpRT _ ?op ?v1 ?v2 (OK _) |- _] =>
      specialize (safe_remove_binop_check _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma remove_check_on_unop_reserve: forall cks op v v' ck,
  evalUnOpRTS cks op v (OK v') ->
    evalUnOpRTS (remove_check_flag ck cks) op v (OK v').
Proof.
  intros;
  induction cks; smack;
  match goal with
  | [H: evalUnOpRTS _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: evalUnOpRT _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [|- context[beq_check_flag _ OverflowCheck]] => destruct (beq_check_flag ck OverflowCheck); auto
  end;
  apply Do_Checks_Unop with (v':=v'0); smack.
Qed.

Lemma safe_remove_unop_check: forall cks op v v' ck v'',
  evalUnOpRTS cks op v v' ->
    evalUnOpRT ck op v (OK v'') ->
      evalUnOpRTS (remove_check_flag ck cks) op v v'.
Proof.
  induction cks; smack;
  match goal with
  | [H: evalUnOpRT _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: evalUnOpRTS _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: evalUnOpRT ?a _ _ _ |- context[?a]] => destruct a; inversion H; smack
  end. 
  match goal with
  | [H1: Math.unary_minus _ = _, H2: Math.unary_minus _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H1: overflowCheck _ _, 
     H2: overflowCheck _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst; apply_in_bound_unique
  end.
Qed .

Ltac apply_safe_remove_unop_check :=
  match goal with
  | [H1: evalUnOpRTS _ ?op ?v _,
     H2: evalUnOpRT _ ?op ?v (OK _) |- _] => 
      specialize (safe_remove_unop_check _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.



Lemma do_overflow_checks_reserve: forall v cks v' ck,
  in_bound v int32_bound true ->
    overflowChecks cks v v' ->  
      overflowChecks (remove_check_flag ck cks) v v'.
Proof.
  intros; inversion H0; smack;
  inversion H1; smack.
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
  match goal with
  | [|- context[beq_check_flag _ OverflowCheck]] => destruct (beq_check_flag ck OverflowCheck); auto
  end;
  constructor.
Qed.

Lemma do_range_checks_reserve: forall cks v l u ck,
  rangeChecks cks v l u (OK (Int v)) ->
    rangeChecks (remove_check_flag ck cks) v l u (OK (Int v)).
Proof.
  intros; 
  inversion H; smack;
  match goal with
  | [|- context[beq_check_flag _ RangeCheck]] => destruct (beq_check_flag ck RangeCheck); auto
  end;
  constructor.
Qed.

Lemma do_range_check_same_result: forall e eBound rBound e' v l u,
  optimize_range_check e eBound rBound e' ->
    rangeChecks (exp_exterior_checks e) v l u (OK (Int v)) ->
      rangeChecks (exp_exterior_checks e') v l u (OK (Int v)).
Proof.
  intros;
  inversion H; smack;
  rewrite exp_updated_exterior_checks;
  apply do_range_checks_reserve; auto.
Qed.

Ltac apply_do_range_check_same_result :=
  match goal with
  | [H1: optimize_range_check ?e _ _ ?e',
     H2: rangeChecks (exp_exterior_checks ?e) _ _ _ (OK _) |- _] =>
      specialize (do_range_check_same_result _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_backward: forall v u0 v0 u' v' e e',
  in_bound v (Interval u0 v0) true ->
    optimize_range_check e (Interval u0 v0) (Interval u' v') e' ->
      exp_exterior_checks e = RangeCheck :: nil ->
        rangeChecks (exp_exterior_checks e') v u' v' (OK (Int v)) ->
          rangeChecks (RangeCheck :: nil) v u' v' (OK (Int v)).
Proof.
  intros;
  inversion H0; subst;
  rewrite H1 in *; smack;
  rewrite exp_updated_exterior_checks in H2;
  apply_In_Bound_SubBound_Trans; auto;
  constructor; auto; constructor; auto.
Qed.

Ltac apply_optimize_range_check_backward :=
 match goal with
 | [H1: in_bound ?v (Interval ?u0 ?v0) true,
    H2: optimize_range_check ?e (Interval ?u0 ?v0) (Interval ?u' ?v') ?e',
    H3: exp_exterior_checks ?e = RangeCheck :: nil,
    H4: rangeChecks (exp_exterior_checks ?e') ?v ?u' ?v' (OK (Int ?v)) |- _ 
   ] => 
   specialize (optimize_range_check_backward _ _ _ _ _ _ _ H1 H2 H3 H4);
   let HZ := fresh "HZ" in
   intro HZ
 end.

(*
Lemma optimize_range_check_subBound: forall e u v u' v' e',
  optimize_range_check e (Interval u v) (Interval u' v') e' ->
    List.In RangeCheck (exp_exterior_checks e) ->
      ~(List.In RangeCheck (exp_exterior_checks e')) ->
        sub_bound (Interval u v) (Interval u' v') true.

Lemma optimize_range_check_on_copy_out_subBound: forall v u0 v0 u' v' e e',
  optimize_range_check_on_copy_out e (Interval u v) (Interval u' v') e' ->
    List.In RangeCheck (exp_exterior_checks e) ->
      ~(List.In RangeCheck (exp_exterior_checks e')) ->
        sub_bound (Interval u v) (Interval u' v').
*)

(********************************************************************)
(********************************************************************)

Lemma optimize_overflow_check_reserve: forall vBound cks retBound cks',
  sub_bound vBound int32_bound false ->
    optimize_overflow_check vBound cks (retBound, cks') ->
      cks = cks'.
Proof.
  intros;
  inversion H0; smack;
  apply_sub_bound_unique; smack.
Qed.

Ltac apply_optimize_overflow_check_reserve :=
  match goal with
  | [H1: sub_bound ?b _ false,
     H2: optimize_overflow_check ?b _ _ |- _] =>
      specialize ( optimize_overflow_check_reserve _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_reserve: forall v vBound vBound' e e',
  in_bound v vBound true ->
    in_bound v vBound' false ->
      optimize_range_check e vBound vBound' e' ->
        e' = e.
Proof.
  intros;
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; smack
  end;
  apply_In_Bound_Trans; smack;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
Qed.

Ltac apply_optimize_range_check_reserve :=
  match goal with
  | [H1: in_bound ?v ?eBound true,
     H2: in_bound ?v ?eBound' false,
     H3: optimize_range_check _ ?eBound ?eBound' _ |- _] =>
      specialize (optimize_range_check_reserve _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_on_copy_out_reserve: forall v vBound vBound' e e',
  in_bound v vBound true ->
    in_bound v vBound' false ->
      optimize_range_check_on_copy_out e vBound vBound' e' ->
        e' = e.
Proof.
  intros;
  match goal with
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; smack
  end;
  apply_In_Bound_Trans; smack;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
Qed.

Ltac apply_optimize_range_check_on_copy_out_reserve :=
  match goal with
  | [H1: in_bound ?v ?vBound true,
     H2: in_bound ?v ?vBound' false,
     H3: optimize_range_check_on_copy_out _ ?vBound ?vBound' _ |- _] =>
      specialize (optimize_range_check_on_copy_out_reserve _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)

Lemma do_flagged_checks_on_divide_reserve: forall v1 v1Bound v2 v2Bound bound1 cks' v,
  in_bound v1 v1Bound true ->
    in_bound v2 v2Bound true ->
      optimize_rtc_binop Divide v1Bound v2Bound (DivCheck :: OverflowCheck :: nil) (bound1, cks') ->
        evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide (Int v1) (Int v2) v ->
          evalBinOpRTS cks' Divide (Int v1) (Int v2) v.
Proof.
  intros;
  match goal with
  | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; clear H; subst; smack
  end.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; smack
  end.
  (*case 1*)
  match goal with 
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; subst; smack
  end; 
  constructor; smack.
  (*case 2: conflict*)  
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with 
  | [H: divCheck _ _ _ _ |- _] => inversion H; clear H; subst; smack
  end;
  apply_in_bound_value_neq_zero;
  match goal with
  | [H1: Zeq_bool ?v2 0 = true, H2: Zeq_bool ?v2 0 = false |- _] => rewrite H1 in H2; inversion H2
  end.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; subst; smack
  end.

  (*case 1*)  
  match goal with 
  | [H: divCheck _ _ _ _ |- _] => inversion H; subst; smack
  end.
  match goal with 
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; subst; smack
  end.
  
  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); auto.
  repeat progress match goal with
  | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; clear H; subst; smack
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; clear H; subst; smack
  end.
  apply_divide_in_bound.
  match goal with 
  | [H: overflowCheck _ _ |- _] => inversion H; clear H; subst
  end.
  apply_In_Bound_SubBound_Trans.
  apply_in_bound_conflict; smack.

  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); auto.

  (* case 2 *)
  match goal with 
  | [H: divCheck _ _ _ _ |- _] => inversion H; subst; smack
  end.
  match goal with 
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; subst; smack
  end.
  repeat progress match goal with
  | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; clear H; subst; smack
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; clear H; subst; smack
  end.
  apply_divide_in_bound.
  match goal with 
  | [H: overflowCheck _ _ |- _] => inversion H; clear H; subst
  end.
  apply_In_Bound_SubBound_Trans.
  apply_in_bound_conflict; smack.
Qed.
  
Ltac apply_do_flagged_checks_on_divide_reserve :=
  match goal with
  | [H1: in_bound ?v1 ?v1Bound true,
     H2: in_bound ?v2 ?v2Bound true,
     H3: optimize_rtc_binop Divide ?v1Bound ?v2Bound (DivCheck :: OverflowCheck :: nil) (?bound1, ?cks'),
     H4: evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide (Int ?v1) (Int ?v2) ?v |- _ ] =>
      specialize (do_flagged_checks_on_divide_reserve _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma do_flagged_checks_on_modulus_reserve: forall v1 v1Bound v2 v2Bound bound1 cks' v,
  in_bound v1 v1Bound true ->
    in_bound v2 v2Bound true ->
      optimize_rtc_binop Modulus v1Bound v2Bound (DivCheck :: nil) (bound1, cks') ->
        evalBinOpRTS (DivCheck :: nil) Modulus (Int v1) (Int v2) v ->
          evalBinOpRTS cks' Modulus (Int v1) (Int v2) v.
Proof.
  intros;
  match goal with
  | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; clear H; subst; smack
  end.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; smack
  end.
  (*case 1*)
  constructor; smack.
  (*case 2: conflict*)  
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with 
  | [H: divCheck _ _ _ _ |- _] => inversion H; clear H; subst; smack
  end;
  apply_in_bound_value_neq_zero;
  match goal with
  | [H1: Zeq_bool ?v2 0 = true, H2: Zeq_bool ?v2 0 = false |- _] => rewrite H1 in H2; inversion H2
  end.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with 
  | [H: divCheck _ _ _ _ |- _] => inversion H; subst; smack
  end;  
  apply ChecksBinOp with (v:=(Int (v1 mod v2))); auto.
Qed.

Ltac apply_do_flagged_checks_on_modulus_reserve :=
  match goal with
  | [H1: in_bound ?v1 ?v1Bound true,
     H2: in_bound ?v2 ?v2Bound true,
     H3: optimize_rtc_binop Modulus ?v1Bound ?v2Bound (DivCheck :: nil) _,
     H4: evalBinOpRTS (DivCheck :: nil) Modulus (Int ?v1) (Int ?v2) ?v |- _ ] => 
      specialize (do_flagged_checks_on_modulus_reserve _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma do_flagged_checks_on_plus_reserve: forall v1 v1Bound v2 v2Bound bound1 cks' op v,
  op = Plus \/ op = Minus \/ op = Multiply ->
    in_bound v1 v1Bound true ->
    in_bound v2 v2Bound true ->
      optimize_rtc_binop op v1Bound v2Bound (OverflowCheck :: nil) (bound1, cks') ->
        evalBinOpRTS (OverflowCheck :: nil) op (Int v1) (Int v2) v ->
          evalBinOpRTS cks' op (Int v1) (Int v2) v.
Proof.
  intros;
  match goal with
  | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; subst; auto
  end.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end;
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with
  | [H: overflowCheck _ _ |- _] => inversion H; subst
  | [H: divCheck _ _ _ _ |- _] => inversion H; subst 
  end.
  (** case 1: Plus *)
  apply_Sub_Bound_Plus_Compat.
  apply_sub_bound_unique; smack.
  (** case 2: minus *)
  apply_Sub_Bound_Minus_Compat.
  apply_sub_bound_unique; smack.
  (** case 3: Multiply *)  
  specialize (multiply_in_bound _ _ _ _ _ _ H0 H1); let HZ := fresh "HZ" in intro HZ.
  apply_In_Bound_SubBound_Trans.
  apply_in_bound_conflict; smack.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end;
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; subst; smack
  end;
  match goal with
  | [H: overflowCheck _ _ |- _] => inversion H; subst
  | [H: divCheck _ _ _ _ |- _] => inversion H; subst 
  end.
Qed.

Ltac apply_do_flagged_checks_on_plus_reserve :=
  match goal with
  | [H1: ?op = Plus \/ ?op = Minus \/ ?op = Multiply,
     H2: in_bound ?v1 ?v1Bound true,
     H3: in_bound ?v2 ?v2Bound true,
     H4: optimize_rtc_binop ?op ?v1Bound ?v2Bound (OverflowCheck :: nil) _,
     H5: evalBinOpRTS (OverflowCheck :: nil) ?op (Int ?v1) (Int ?v2) ?v |- _] =>
      specialize (do_flagged_checks_on_plus_reserve _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma evalUnOpRTS_reserve: forall v vBound op cks bound1 cks' v',
  in_bound v vBound true ->
    optimize_rtc_unop op vBound cks (bound1, cks') ->
      evalUnOpRTS cks op (Int v) v' ->
        evalUnOpRTS cks' op (Int v) v'.
Proof.
  intros;
  match goal with
  | [H: evalUnOpRTS _ _ _ _ |- _] => inversion H; smack
  end.
- match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end; constructor; auto.
- match goal with
  | [H: evalUnOpRT _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: overflowCheck _ _ |- _] => inversion H; subst
  end;
  [ apply_Sub_Bound_Unary_Minus_Compat; apply_sub_bound_unique |
    apply Do_Checks_Unop_RTE; auto
  ].
- match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  end;
  destruct ck;
  match goal with
  | [H: evalUnOpRT _ _ _ _ |- _] => inversion H; smack
  end;
  apply_safe_remove_unop_check; smack.
Qed.

Ltac apply_evalUnOpRTS_reserve :=
  match goal with
  | [H1: in_bound ?v ?bound1 true,
     H2: optimize_rtc_unop _ ?bound1 _ _,
     H3: evalUnOpRTS _ _ (Int ?v) _ |- _] =>
      specialize (evalUnOpRTS_reserve _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)
(*binop_arithm_in_bound*)
Lemma plus_result_in_bound: forall op v1 v2 v v1Bound v2Bound vBound in_cks,
  op = Plus \/ op = Minus \/ op = Multiply ->
  in_bound v1 v1Bound true ->
  in_bound v2 v2Bound true -> 
  evalBinOpRTS (OverflowCheck :: nil) op (Int v1) (Int v2) (OK (Int v)) ->
  optimize_rtc_binop op v1Bound v2Bound (OverflowCheck :: nil) (vBound, in_cks) ->
  in_bound v vBound true.
Proof.
  intros.
  match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; clear H; smack
  end.
- inversion H12; clear H12; subst;
  inversion H2; clear H2; subst;
  inversion H5; clear H5; subst;
  inversion H11; clear H11; subst.
  + inversion H6; subst.
    specialize (In_Bound_Plus_Compat _ _ _ _ _ _ H0 H1); auto.
  + rewrite H7 in H2; inversion H2; subst.
    inversion H4; subst.
    inversion H7; subst.
    apply In_Bound_Two; smack.
    specialize (In_Bound_Plus_Compat _ _ _ _ _ _ H0 H1); auto.
- inversion H12; clear H12; subst;
  inversion H2; clear H2; subst;
  inversion H5; clear H5; subst;
  inversion H11; clear H11; subst.
  + inversion H6; subst.
    specialize (In_Bound_Minus_Compat _ _ _ _ _ _ H0 H1); auto.
  + rewrite H7 in H3; inversion H3; subst.
    inversion H4; subst.
    inversion H7; subst.
    apply In_Bound_Two; smack.
    specialize (In_Bound_Minus_Compat _ _ _ _ _ _ H0 H1); auto.
- specialize (multiply_in_bound _ _ _ _ _ _ H0 H1); let HZ := fresh "HZ" in intro HZ.
  inversion H9; clear H9; subst;
  inversion H2; clear H2; subst;
  inversion H5; clear H5; subst;
  inversion H11; clear H11; subst.
  + inversion H6; subst; auto.
  + rewrite H7 in H3; inversion H3; subst.
    inversion H4; subst.
    inversion H7; subst.
    apply In_Bound_Two; smack.
Qed.

Ltac apply_plus_result_in_bound := 
  match goal with
  | [H1: ?op' = Plus \/ ?op' = Minus \/ ?op' = Multiply,
     H2: in_bound ?v1' ?bound1' true,
     H3: in_bound ?v2' ?bound2' true, 
     H4: evalBinOpRTS (OverflowCheck :: nil) ?op' (Int ?v1') (Int ?v2') (OK (Int _)),
     H5: optimize_rtc_binop ?op' ?bound1' ?bound2' (OverflowCheck :: nil) _ |- _] =>
      specialize (plus_result_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma modulus_result_in_bound: forall v1 v2 v v1Bound v2Bound vBound in_cks,
  in_bound v1 v1Bound true ->
  in_bound v2 v2Bound true -> 
  evalBinOpRTS (DivCheck :: nil) Modulus (Int v1) (Int v2) (OK (Int v)) ->
  optimize_rtc_binop Modulus v1Bound v2Bound (DivCheck :: nil) (vBound, in_cks) ->
  in_bound v vBound true.
Proof.
  intros;
  match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; clear H; smack
  end;
  inversion H1; clear H1; subst;
  inversion H4; clear H4; subst;
  inversion H7; clear H7; subst;
  inversion H11; clear H11; subst;
  apply_modulus_in_bound;
  inversion H2; smack.
Qed.


Ltac apply_modulus_result_in_bound :=
  match goal with
  | [H1: in_bound ?v1 ?v1Bound true,
     H2: in_bound ?v2 ?v2Bound true, 
     H3: evalBinOpRTS (DivCheck :: nil) Modulus (Int ?v1) (Int ?v2) (OK (Int ?v)),
     H4: optimize_rtc_binop Modulus ?v1Bound ?v2Bound (DivCheck :: nil) _ |- _] =>
      specialize (modulus_result_in_bound _ _ _ _ _ _ _ H1 H2 H3 H4); 
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma divide_result_in_bound: forall v1 v2 v v1Bound v2Bound vBound in_cks,
  in_bound v1 v1Bound true ->
  in_bound v2 v2Bound true -> 
  evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide (Int v1) (Int v2) (OK (Int v)) ->
  optimize_rtc_binop Divide v1Bound v2Bound (DivCheck :: OverflowCheck :: nil) (vBound, in_cks) ->
  in_bound v vBound true.
Proof.
  intros;
  match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; subst; clear H; smack
  end.
- inversion H10; clear H10; subst;
  inversion H1; clear H1; subst;
  inversion H4; clear H4; subst;
  inversion H9; clear H9; subst;
  inversion H12; clear H12; subst;
  inversion H15; clear H15; subst;
  inversion H9; clear H9; subst;
  apply_divide_in_bound; smack.
  
  apply In_Bound_Two; auto.
  inversion H11; subst.
  inversion H8; subst; auto.
- inversion H11; clear H11; subst;
  inversion H1; clear H1; subst;
  inversion H4; clear H4; subst;
  inversion H9; clear H9; subst;
  inversion H12; clear H12; subst;
  inversion H15; clear H15; subst;
  inversion H9; clear H9; subst;
  apply_divide_in_bound; smack.

  apply In_Bound_Two; auto.
  inversion H11; subst.
  inversion H8; subst; auto.
Qed.

Ltac apply_divide_result_in_bound :=
  match goal with
  | [H1: in_bound ?v1 ?v1Bound true,
     H2: in_bound ?v2 ?v2Bound true, 
     H3: evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide (Int ?v1) (Int ?v2) (OK (Int ?v)),
     H4: optimize_rtc_binop Divide ?v1Bound ?v2Bound (DivCheck :: OverflowCheck :: nil) (?vBound, ?in_cks) |- _] =>
      specialize (divide_result_in_bound _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.

(* binop_arithm_in_bound1 *)
Lemma plus_result_in_bound_backward: forall op v1 v2 v v1Bound v2Bound vBound in_cks,
  op = Plus \/ op = Minus \/ op = Multiply ->
  in_bound v1 v1Bound true ->
  in_bound v2 v2Bound true -> 
  optimize_rtc_binop op v1Bound v2Bound (OverflowCheck :: nil) (vBound, in_cks) ->
  evalBinOpRTS in_cks op (Int v1) (Int v2) v ->
  evalBinOpRTS (OverflowCheck :: nil) op (Int v1) (Int v2) v.
Proof.
  intros.
  inversion H2; clear H2; subst; smack. 
- inversion H12; clear H12; smack.
  inversion H3; smack.
  apply ChecksBinOp with (v := Int (v1+v2)); auto.
  eapply OverflowCheckBinop; smack.
  constructor.
  specialize (In_Bound_Plus_Compat _ _ _ _ _ _ H0 H1); intros.
  apply_In_Bound_SubBound_Trans; auto.
- inversion H12; clear H12; smack.
  inversion H3; smack.
  apply ChecksBinOp with (v := Int (v1-v2)); auto.
  eapply OverflowCheckBinop; smack.
  constructor.
  specialize (In_Bound_Minus_Compat _ _ _ _ _ _ H0 H1); intros.
  apply_In_Bound_SubBound_Trans; auto.
- (** Multiply *)
  inversion H9; clear H9; smack.
  inversion H3; smack.
  apply ChecksBinOp with (v := Int (v1*v2)); auto.
  eapply OverflowCheckBinop; smack.
  constructor.
  specialize (multiply_in_bound _ _ _ _ _ _ H0 H1); intro.
  apply_In_Bound_SubBound_Trans; auto.
Qed.

Ltac apply_plus_result_in_bound_backward := 
  match goal with
  | [H1: ?op' = Plus \/ ?op' = Minus \/ ?op' = Multiply,
     H2: in_bound ?v1' ?bound1' true,
     H3: in_bound ?v2' ?bound2' true, 
     H4: optimize_rtc_binop ?op' ?bound1' ?bound2' (OverflowCheck :: nil) (?vBound, ?in_cks),
     H5: evalBinOpRTS ?in_cks ?op' (Int ?v1') (Int ?v2') _ |- _] =>
      specialize (plus_result_in_bound_backward _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma modulus_result_in_bound_backward: forall v1 v2 v v1Bound v2Bound vBound in_cks,
  in_bound v1 v1Bound true ->
  in_bound v2 v2Bound true -> 
  optimize_rtc_binop Modulus v1Bound v2Bound (DivCheck :: nil) (vBound, in_cks) ->
  evalBinOpRTS in_cks Modulus (Int v1) (Int v2) v ->
  evalBinOpRTS (DivCheck :: nil) Modulus (Int v1) (Int v2) v.
Proof.
  intros.
  inversion H1; clear H1; subst; smack. 
  inversion H2; clear H2; smack.
  specialize (in_bound_value_neq_zero _ _ H0 H5); intro HZ.
  apply_modulus_in_bound.
  apply ChecksBinOp with (v := Int (v1 mod v2)); auto;
  constructor; auto.
  constructor; auto.
Qed.

Ltac apply_modulus_result_in_bound_backward :=
  match goal with
  | [H1: in_bound ?v1 ?v1Bound true,
     H2: in_bound ?v2 ?v2Bound true, 
     H3: optimize_rtc_binop Modulus ?v1Bound ?v2Bound (DivCheck :: nil) (?vBound, ?in_cks),
     H4: evalBinOpRTS ?in_cks Modulus (Int ?v1) (Int ?v2) ?v |- _] =>
      specialize (modulus_result_in_bound_backward _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.  

Lemma divide_result_in_bound_backward: forall v1 v2 v v1Bound v2Bound vBound in_cks,
  in_bound v1 v1Bound true ->
  in_bound v2 v2Bound true -> 
  optimize_rtc_binop Divide v1Bound v2Bound (DivCheck :: OverflowCheck :: nil) (vBound, in_cks) ->
  evalBinOpRTS in_cks Divide (Int v1) (Int v2) v ->
  evalBinOpRTS (DivCheck :: OverflowCheck :: nil) Divide (Int v1) (Int v2) v.
Proof.
  intros.
  inversion H1; clear H1; subst; smack. 
- inversion H10; clear H10; smack.
  match goal with
  | [H1: evalBinOpRTS (DivCheck :: _) Divide _ _ _ |- _] =>
      inversion H1; subst
  end.
  (*case 1*)
  apply ChecksBinOpRTE; auto.
  (*case 2*)
  repeat progress match goal with
  | [H1: evalBinOpRT DivCheck _ _ _ _ |- _] => inversion H1; subst; clear H1
  | [H1: divCheck ?op ?v0 ?v3 _ |- _ ] => inversion H1; subst; clear H1
  end.
  inversion H12; subst.
  inversion H1; subst.
  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); auto.
  constructor; auto. constructor; auto.

  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); auto.
  apply OverflowCheckBinop with (v:=(v1 ÷ v2)%Z); auto.
  constructor; auto.
  apply_divide_in_bound.
  apply_In_Bound_SubBound_Trans; auto.
- apply_in_bound_value_neq_zero; auto.
  apply_divide_in_bound.
  inversion H11; clear H11; smack;
  match goal with
  | [H1: evalBinOpRTS _ _ _ _ _ |- _] => inversion H1; subst; clear H1
  end.

  (* case 1 *)
  inversion H1; subst.
  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); smack.  
  constructor; auto. constructor; smack.

  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); smack.  
  apply OverflowCheckBinop with (v:=(v1 ÷ v2)%Z); auto.
  constructor; auto.
  apply_In_Bound_SubBound_Trans; auto.
  constructor; auto.

  (* case 2 *)
  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); smack;   
  constructor; auto.
  constructor; auto.

  (* case 3 *)
  inversion H12; subst.
  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); smack. 
  constructor; auto.
  constructor; auto.  
  
  inversion H4; subst.
  inversion H2; subst.
  inversion H3; subst.
  apply ChecksBinOp with (v:=(Int (v1 ÷ v2))); smack.
Qed.

Ltac apply_divide_result_in_bound_backward :=
  match goal with
  | [H1: in_bound ?v1 ?v1Bound true,
     H2: in_bound ?v2 ?v2Bound true, 
     H3: optimize_rtc_binop Divide ?v1Bound ?v2Bound (DivCheck :: OverflowCheck :: nil) (?vBound, ?in_cks),
     H4: evalBinOpRTS ?in_cks Divide (Int ?v1) (Int ?v2) ?v |- _] =>
      specialize (divide_result_in_bound_backward _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma unop_arithm_in_bound: forall v v' vBound vBound' in_cks,
  in_bound v vBound true ->
  evalUnOpRTS (OverflowCheck :: nil) Unary_Minus (Int v) (OK (Int v')) ->
  optimize_rtc_unop Unary_Minus vBound (OverflowCheck :: nil) (vBound', in_cks) ->
  in_bound v' vBound' true.
Proof.
  intros. 
  inversion H0; clear H0; subst.
  inversion H4; clear H4; subst.
  inversion H8; clear H8; subst.
  unfold Math.unary_operation in H4.
  rewrite H4 in H0; inversion H0; subst.
  inversion H4; subst.
  
  inversion H1; clear H1; smack.
  inversion H10; smack.
- apply In_Bound_Unary_Minus_Compat; auto.
- inversion H2; smack.
  specialize (In_Bound_Unary_Minus_Compat _ _ _ H); intro HZ.
  unfold int32_bound in H5.
  apply_In_Bound_Two; auto.
Qed.

Ltac apply_unop_arithm_in_bound :=
  match goal with
  | [H1: in_bound ?v ?bound true,
     H2: evalUnOpRTS (OverflowCheck :: nil) Unary_Minus (Int ?v) (OK (Int ?v')),
     H3: optimize_rtc_unop Unary_Minus ?bound (OverflowCheck :: nil) _ |- _] =>
      specialize (unop_arithm_in_bound _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


Lemma literal_checks_optimization_soundness: forall cks l v lBound cks',
  evalLiteralRT cks l v ->
    optLiteral l cks (lBound, cks') ->
      evalLiteralRT cks' l v.
Proof.
  intros;
  inversion H; inversion H0; smack;
  constructor;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; clear H; smack
  end;
  specialize (do_overflow_checks_reserve _ _ _ OverflowCheck H5 H1); auto.
Qed.

Ltac apply_literal_checks_optimization_soundness :=
  match goal with
  | [H1: evalLiteralRT _ ?c _,
     H2: optLiteral ?c _ _ |- _] => 
      specialize (literal_checks_optimization_soundness _ _ _ _ _ H1 H2); auto
  end.

Lemma optimize_exp_ex_cks_stripped: forall e e' st cks vBound,
  optExp st (update_exterior_checks_exp e cks) (e', vBound) ->
    optExp st e (update_exterior_checks_exp e' (exp_exterior_checks e), vBound).
Proof.
  apply (expression_x_ind
    (fun e: expRT =>
       forall (e' : expRT) (st : symTabRT) (cks : exterior_checks) (vBound : bound),
      optExp st (update_exterior_checks_exp e cks) (e', vBound) ->
      optExp st e (update_exterior_checks_exp e' (exp_exterior_checks e), vBound))
    (fun n: nameRT =>
       forall (n' : nameRT) (st : symTabRT) (cks : exterior_checks) (vBound : bound),
      optName st (update_exterior_checks_name n cks) (n', vBound) ->
      optName st n (update_exterior_checks_name n' (name_exterior_checks n), vBound))
    ); intros;
  match goal with
  | [H: optExp _ _ _ |- _] => inversion H; subst
  | [H: optName _ _ _ |- _] => inversion H; subst
  end.
- constructor; auto.
- constructor.
  specialize (H _ _ _ _ H3); auto.
- apply O_BinOp with (e1Bound := e1Bound) (e2Bound := e2Bound); auto.
- apply O_UnOp with (eBound := eBound); auto.
- apply O_Identifier with (t := t); auto.
- apply O_IndexedComponent with (xBound := xBound) (e' := e') (u := u) (v := v) 
                                (t := t) (u' := u') (v' := v'); auto.
- apply O_SelectedComponent with (x' := x') (xBound := xBound) (t := t); auto.
Qed.

Lemma optimize_name_ex_cks_stripped: forall n n' st cks vBound,
  optName st (update_exterior_checks_name n cks) (n', vBound) ->
    optName st n (update_exterior_checks_name n' (name_exterior_checks n), vBound).
Proof.
  induction n; intros; 
  inversion H; subst; simpl.
- apply O_Identifier with (t := t); auto.
- apply O_IndexedComponent with (xBound := xBound) (e':=e') (u:=u) (v:=v) (t:=t) (u':=u') (v':=v'); auto.
- apply O_SelectedComponent with (x':=x') (xBound:=xBound) (t:=t); auto.
Qed.




