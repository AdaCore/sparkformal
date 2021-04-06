(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export Coq.ZArith.Zbool.
Require Export Coq.ZArith.BinInt.
Require Export Coq.ZArith.Zorder.
Require Export Coq.ZArith.Zquot.
Require Export Coq.ZArith.Zdiv.
Require Export Coq.ZArith.Zcompare.
Require Export values.

(*
Coq.ZArith.Zorder: 
     http://coq.inria.fr/V8.1/stdlib/Coq.ZArith.Zorder.html#Zle_ge
     http://coq.inria.fr/V8.1/stdlib/Coq.ZArith.Zbool.html
     http://coq.inria.fr/V8.1/stdlib/Coq.ZArith.Zbool.html#Zle_bool

     https://coq.inria.fr/library/Coq.Numbers.NatInt.NZOrder.html
     http://flint.cs.yale.edu/cs428/coq/library/Coq.ZArith.Zorder.html
     https://coq.inria.fr/V8.1/stdlib/Coq.ZArith.Zorder.html
     https://coq.inria.fr/V8.1/stdlib/Coq.ZArith.BinInt.html

     Logic: https://coq.inria.fr/library/Coq.Init.Logic.html


** MinMax **

   https://coq.inria.fr/library/Coq.Structures.GenericMinMax.html
   - lemmas about min and max
   
   https://coq.inria.fr/library/Coq.ZArith.BinInt.html
   - Lemma max_l n m : m<=n -> max n m = n.
   - Lemma max_r n m : n<=m -> max n m = m.
   - Lemma min_l n m : n<=m -> min n m = n.
   - Lemma min_r n m : m<=n -> min n m = m.

** abs (absolute value) **

   https://coq.inria.fr/library/Coq.ZArith.BinInt.html#Z.abs
   - Lemma abs_eq n : 0 <= n -> abs n = n.
   - Lemma abs_neq n : n <= 0 -> abs n = - n.

** Multiply **
 
    https://coq.inria.fr/library/Coq.ZArith.Zorder.html
    https://coq.inria.fr/library/Coq.ZArith.BinInt.html
    - Compatibility of multiplication, such as: Lemma Zmult_gt_0_lt_compat_r: p > 0 -> n < m -> n * p < m * p.

** Modulus **

    https://coq.inria.fr/library/Coq.ZArith.BinInt.html
    - Lemma mod_pos_bound a b : 0 < b -> 0 <= a mod b < b.
    - Lemma mod_neg_bound a b : b < 0 -> b < a mod b <= 0.

** Zquot (÷) / Divide (/) **
  
    https://coq.inria.fr/library/Coq.ZArith.Zquot.html
    https://coq.inria.fr/library/Coq.ZArith.Zdiv.html

    - Theorem Zquot_Zdiv_pos : forall a b, 0 <= a -> 0 <= b -> a÷b = a/b.
   
  
** neg/pos/opp(e.g. -x) **

    https://coq.inria.fr/library/Coq.ZArith.Zorder.html
    https://coq.inria.fr/library/Coq.ZArith.BinInt.html

    - Lemma Zle_neg_pos : forall p q:positive, Zneg p <= Zpos q.
    - Lemma Zgt_pos_0 : forall p:positive, Zpos p > 0.
    - Lemma Zle_0_pos : forall p:positive, 0 <= Zpos p.
    - Lemma Zlt_neg_0 : forall p:positive, Zneg p < 0.

** Zlt/Zgt/Zle/Zge **
   
    https://coq.inria.fr/library/Coq.ZArith.Zorder.html
    https://coq.inria.fr/library/Coq.ZArith.Zbool.html
    https://coq.inria.fr/library/Coq.ZArith.BinInt.html
    

Theorem le_lt_trans : forall n m p, n <= m -> m < p -> n < p.

Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.

Theorem le_antisymm : forall n m, n <= m -> m <= n -> n == m.

More properties of < and <= with respect to S and 0.

Theorem le_succ_r : forall n m, n <= S m <-> n <= m \/ n == S m.

Theorem lt_succ_l : forall n m, S n < m -> n < m.

Theorem le_le_succ_r : forall n m, n <= m -> n <= S m.

Theorem lt_lt_succ_r : forall n m, n < m -> n < S m.

Theorem succ_lt_mono : forall n m, n < m <-> S n < S m.

Theorem succ_le_mono : forall n m, n <= m <-> S n <= S m.

Lemma gt_lt_iff n m : n > m <-> m < n.

https://coq.inria.fr/library/Coq.ZArith.BinInt.html
https://coq.inria.fr/V8.1/stdlib/Coq.ZArith.BinInt.html
 - Lemma gt_lt n m : n > m -> m < n.
 - Lemma lt_gt n m : n < m -> m > n.
 - Lemma ge_le_iff n m : n >= m <-> m <= n.
 - Lemma ge_le n m : n >= m -> m <= n.
 - Lemma le_ge n m : n <= m -> m >= n.

https://coq.inria.fr/library/Coq.Numbers.NatInt.NZOrder.html
 - Theorem le_succ_r : forall n m, n <= S m <-> n <= m \/ n == S m.
 - Theorem lt_succ_l : forall n m, S n < m -> n < m.
 - Theorem le_le_succ_r : forall n m, n <= m -> n <= S m.
 - Theorem lt_lt_succ_r : forall n m, n < m -> n < S m.
 - Theorem succ_lt_mono : forall n m, n < m <-> S n < S m.
 - Theorem succ_le_mono : forall n m, n <= m <-> S n <= S m.
 - Theorem le_succ_l : forall n m, S n <= m <-> n < m.

 lemma Z_eq_mult : forall n m : Z, m = 0%Z -> (m * n)%Z = 0%Z

 Lemma Zlt_neg_0 : forall p : positive, (Z.neg p < 0)%Z

apply them with: 
  Z.le_succ_r
  Z.le_le_succ_r
*)


(** * ZArith (Mult, Div, Mod) *)

Function min_abs_f (u : Z) (v: Z) : Z :=
  Z.min (Z.abs u) (Z.abs v).

Function max_abs_f (u : Z) (v: Z) : Z :=
  Z.max (Z.abs u) (Z.abs v).

(** ** Mult *)

(** e1: [u, v], e2: [u', v'], e1 * e2: min(u*u', u*v', v*u', v*v') *)
Function multiply_min_f (u : Z) (v: Z) (u' : Z) (v': Z) : Z :=
  Z.min (Z.min (u * u') (u * v')) (Z.min (v * u') (v * v')).
  
(** max(u*u', u*v', v*u', v*v') *)
Function multiply_max_f (u : Z) (v: Z) (u' : Z) (v': Z) : Z :=
  Z.max (Z.max (u * u') (u * v')) (Z.max (v * u') (v * v')).

(** ** Div *)

(** e1: [u, v], e2: [u', v'], e1/e2: min, max *)
Function divide_min_max_f (u : Z) (v: Z) (u' : Z) (v': Z) : Z * Z :=
  if Zle_bool v' (-1) then
    (* case 1: v' < 0 *)
    if Zle_bool v (-1) then
      (* subcase 1: v < 0 *)
      ((Z.quot v u'), (Z.quot u v'))
    else if Zle_bool 1 u then
      (* subcase 2: u > 0 *)
      ((Z.quot v v'), (Z.quot u u'))
    else
      (* subcase 3 *)
      ((Z.quot v v'), (Z.quot u v'))
  else if Zle_bool 1 u' then
    (* case 2: u' > 0 *)
    if Zle_bool v (-1) then
      (* subcase 1: v < 0 *)
      ((Z.quot u u'), (Z.quot v v'))
    else if Zle_bool 1 u then
      (* subcase 2: u > 0 *)
      ((Z.quot u v'), (Z.quot v u'))
    else
      (* subcase 3 *)
      ((Z.quot u u'), (Z.quot v u'))
  else
    (* case 3 *)
    if Zle_bool v (-1) then
      (* subcase 1: v < 0 *)
      (u, (Z.abs u))
    else if Zle_bool 1 u then
      (* subcase 2: u > 0 *)
      (Z.opp v, v)
    else
      (* subcase 3 *)
      (Z.opp (max_abs_f u v), (max_abs_f u v)).

(*
Function divide_min_max_f (u : Z) (v: Z) (u' : Z) (v': Z) : Z * Z :=
  if Zle_bool v' (-1) then
    (* case 1: v' < 0 *)
    if Zle_bool v (-1) then
      (* subcase 1: v < 0 *)
      ((Z.quot v u'), min_f (Z.quot u v') max_signed)
    else if Zle_bool 1 u then
      (* subcase 2: u > 0 *)
      ((Z.quot v v'), (Z.quot u u'))
    else
      (* subcase 3 *)
      ((Z.quot v v'), min_f (Z.quot u v') max_signed)
  else if Zle_bool 1 u' then
    (* case 2: u' > 0 *)
    if Zle_bool v (-1) then
      (* subcase 1: v < 0 *)
      ((Z.quot u u'), (Z.quot v v'))
    else if Zle_bool 1 u then
      (* subcase 2: u > 0 *)
      ((Z.quot u v'), (Z.quot v u'))
    else
      (* subcase 3 *)
      ((Z.quot u u'), (Z.quot v u'))
  else
    (* case 3 *)
    if Zle_bool v (-1) then
      (* subcase 1: v < 0 *)
      (u, min_f (Z.abs u) max_signed)
    else if Zle_bool 1 u then
      (* subcase 2: u > 0 *)
      (Z.opp v, v)
    else
      (* subcase 3 *)
      (Z.opp (max_abs_f u v), min_f (max_abs_f u v) max_signed).
*)

(** ** Mod *)

(** e1: [u, v], e2: [u', v'], e1 mod e2: min, max 
    e.g. x mod 9, then its result range is: [0..8]
*)
Function modulus_min_max_f (u : Z) (v: Z) (u' : Z) (v': Z) : Z * Z :=
  if Zle_bool v' (-1) then
    (* case 1: v' < 0 *)
    ((u'+1)%Z, 0%Z)
  else if Zle_bool 1 u' then
    (* subcase 2: u' > 0 *)
    (0%Z, (v'-1)%Z)
  else
    (if Zeq_bool u' 0 then 0 else (u'+1), if Zeq_bool v' 0 then 0 else (v'-1))%Z.

(** * Relation (Zeq, Zlt, Zle, Zgt, Zge) *)

(** ** Relation between Zlt and Zlt_bool *)

(** the following three lemmas are from Coq.ZArith.BinInt *)
Lemma Zeqb_eq: forall n m : Z, 
  (n =? m)%Z = true <-> n = m.
Proof. 
  apply Z.eqb_eq; auto. 
Qed.

Lemma Zltb_lt: forall n m : Z, 
  (n <? m)%Z = true <-> (n < m)%Z.
Proof.
  intros; apply Z.ltb_lt; auto.
Qed.

Lemma Zleb_le: forall n m : Z, 
  (n <=? m)%Z = true <-> (n <= m)%Z.
Proof.
  intros; apply Z.leb_le; auto.
Qed.

Lemma Lt_Le_Bool_False: forall u v,
  (u < v)%Z ->
    Zle_bool v u = false.
Proof.
  intros.
  specialize (Zltb_lt u v); intro HZ.
  destruct HZ as [HZa HZb].
  specialize (HZb H).
  unfold Zlt_bool in HZb; unfold Zle_bool.
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto. 
Qed.

Lemma Le_False_Lt: forall u v,
  (Zle_bool v u) = false ->
    (u < v)%Z.
Proof.
  intros.
  remember (Zle_bool v u) as b1.
  symmetry in Heqb1.
  destruct b1; inversion H.
  specialize (Zle_cases v u); intros HZ.
  rewrite Heqb1 in HZ; smack.
Qed.

Lemma Lte_Lt_Bool_False: forall u v,
  (u <= v)%Z ->
    Zlt_bool v u = false.
Proof.
  intros.
  specialize (Zleb_le u v); intro HZ.
  destruct HZ as [HZa HZb].
  specialize (HZb H).
  unfold Zle_bool in HZb; unfold Zlt_bool.
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto.
Qed.

Lemma Lt_False_Le: forall u v,
  (Zlt_bool v u) = false ->
    (u <= v)%Z.
Proof.
  intros;
  apply Zleb_le; auto;
  unfold Zle_bool; unfold Zlt_bool in H;
  rewrite <- Zcompare_antisym;
  destruct (v ?= u)%Z; auto.  
Qed.


Lemma Zgele_Bool_Imp_GeLe_T: forall v l u,
  (Zge_bool v l) && (Zle_bool v u) = true ->
    (l <= v)%Z /\ (v <= u)%Z.
Proof.
  intros.
  specialize (andb_prop _ _ H); clear H; intros HZ.
  destruct HZ as [HZ1 HZ2].
  split.
- specialize (Zge_cases v l); intros HZ.
  rewrite HZ1 in HZ; smack.
- apply Zle_bool_imp_le; auto.  
Qed.

Lemma Zgele_Bool_Imp_GeLe_F: forall v l u,
  (Zge_bool v l) && (Zle_bool v u) = false ->
    (v < l)%Z \/ (u < v)%Z.
Proof.
  intros.
  unfold andb in H.
  remember (Zge_bool v l) as b1; 
  remember (Zle_bool v u) as b2.
  symmetry in Heqb1, Heqb2.
  destruct b1, b2; inversion H.
- specialize (Zle_cases v u); intros HZ;
  rewrite Heqb2 in HZ; smack.
- specialize (Zge_cases v l); intros HZ;
  rewrite Heqb1 in HZ; smack.
- specialize (Zge_cases v l); intros HZ;
  rewrite Heqb1 in HZ; smack.  
Qed.

Lemma Zlele_Bool_Imp_LeLe_T: forall v l u,
  (Zle_bool l v) && (Zle_bool v u) = true ->
    (l <= v)%Z /\ (v <= u)%Z.
Proof.
  intros.
  specialize (andb_prop _ _ H); clear H; intros HZ.
  destruct HZ as [HZ1 HZ2].
  split.
- specialize (Zle_cases l v); intros HZ.
  rewrite HZ1 in HZ; smack.
- apply Zle_bool_imp_le; auto.  
Qed.

Lemma Zlele_Bool_Imp_LeLe_F: forall v l u,
  (Zle_bool l v) && (Zle_bool v u) = false ->
    (v < l)%Z \/ (u < v)%Z.
Proof.
  intros.
  unfold andb in H.
  remember (Zle_bool l v) as b1; 
  remember (Zle_bool v u) as b2.
  symmetry in Heqb1, Heqb2.
  destruct b1, b2; inversion H.
- specialize (Zle_cases v u); intros HZ;
  rewrite Heqb2 in HZ; smack.
- specialize (Zle_cases l v); intros HZ;
  rewrite Heqb1 in HZ; smack.
- specialize (Zle_cases l v); intros HZ;
  rewrite Heqb1 in HZ; smack.  
Qed.

Lemma Zleb_true_le_true: forall v l u,
  (Zle_bool l v) && (Zle_bool v u) = true ->
    ((Zle_bool l v) = true /\ (Zle_bool v u) = true) /\ ((l <= v)%Z /\ (v <= u)%Z).
Proof.
  intros.
  remember (Zle_bool l v) as b1.
  remember (Zle_bool v u) as b2.
  destruct b1, b2; inversion H; subst;
  symmetry in Heqb1, Heqb2.
  smack;
  apply Zleb_le; auto.
Qed.

Ltac apply_Zleb_true_le_true :=
  match goal with
  | [H: (Zle_bool ?l ?v) && (Zle_bool ?v ?u) = true |- _] =>
      specialize (Zleb_true_le_true _ _ _ H); 
      let HZ := fresh "HZ" in intro HZ;
      let HZa := fresh "HZa" in
      let HZb := fresh "HZb" in
      let HZa1 := fresh "HZa1" in
      let HZb1 := fresh "HZb1" in
      destruct HZ as [[HZa HZb] [HZa1 HZb1]];
      clear H
  end.

Lemma Zle_true_leb_true: forall u v u' v',
  (u <= v)%Z ->
    (u' <= v')%Z ->
      (Zle_bool u v) && (Zle_bool u' v') = true.
Proof.
  intros.
  assert(HA1: Zle_bool u v = true).
    apply Zleb_le; auto.
  assert(HA2: Zle_bool u' v' = true).
    apply Zleb_le; auto.
  rewrite HA1, HA2; auto.
Qed.

Lemma leb_lt_false: forall x y,
  (x <=? y)%Z = true ->
    (y < x)%Z ->
      False.
Proof.
  intros.
  assert(HA1: ~ (x <= y)%Z).
    apply Zlt_not_le; auto.
  assert(HA2: (x <= y)%Z).
    apply Zleb_le; auto.
  smack.
Qed.

Ltac apply_leb_lt_false :=
  match goal with
  | [H1: (?x <=? ?y)%Z = true,
     H2: (?y < ?x)%Z |- _] => 
      specialize (leb_lt_false _ _ H1 H2); intro; smack
  end.

(** ** Zlt_bool *)

Lemma Zltb_imp_leb: forall u v,
  (Zlt_bool u v) = true ->
    (Zle_bool u v) = true.
Proof.
  intros.
  assert(H1: v = ((v + 1) - 1)%Z). smack.
  rewrite H1.
  apply Zlt_is_le_bool; auto. 
  clear H1.
  apply Zlt_lt_succ; auto.
  apply Zltb_lt; auto.
Qed.

Lemma Zge_le_bool: forall u v b,
  Zge_bool u v = b -> Zle_bool v u = b.
Proof.
  intros;
  unfold Zle_bool; unfold Zge_bool in H;
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto. 
Qed.

Lemma Zle_ge_bool: forall u v b,
  Zle_bool u v = b -> Zge_bool v u = b.
Proof.
  intros;
  unfold Zge_bool; unfold Zle_bool in H;
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto. 
Qed.

Lemma Zgt_lt_bool: forall u v b,
  Zgt_bool u v = b -> Zlt_bool v u = b.
Proof.
  intros;
  unfold Zlt_bool; unfold Zgt_bool in H;
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto. 
Qed.

Lemma Zlt_gt_bool: forall u v b,
  Zlt_bool u v = b -> Zgt_bool v u = b.
Proof.
  intros;
  unfold Zgt_bool; unfold Zlt_bool in H;
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto. 
Qed.

(** u < v /\ v <= w => u <= w *)
Lemma Zltb_leb_trans_leb: forall u v w,
  (Zlt_bool u v) = true ->
    (Zle_bool v w) = true ->
      (Zle_bool u w) = true.
Proof.
  intros.
  apply Zltb_imp_leb.
  apply Zltb_lt.
  apply Z.lt_le_trans with (m:=v); auto;
  [ apply Z.ltb_lt; auto |
    apply Z.leb_le; auto
  ].
Qed.

(** n < m /\ m <= p ==> n < p 
    - Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.
*)
Lemma Zltb_leb_trans_ltb: forall n m p,
  (Zlt_bool n m) = true ->
    (Zle_bool m p) = true ->
      (Zlt_bool n p) = true.
Proof.
  intros.
  apply Zltb_lt.
  apply Z.lt_le_trans with (m:=m);
  [ apply Z.ltb_lt; auto |
    apply Z.leb_le; auto
  ].
Qed.

(** n <= m -> m < p ==> n <= p
 *)
Lemma Zleb_ltb_trans_leb: forall n m p, 
  (Zle_bool n m) = true ->
    (Zlt_bool m p) = true ->
      (Zle_bool n p) = true.
Proof.
  intros.
  apply Zltb_imp_leb.
  apply Zltb_lt.
  apply Z.le_lt_trans with (m:=m);
  [ apply Z.leb_le; auto |
    apply Z.ltb_lt; auto
  ].
Qed.

(** n <= m -> m < p ==> n < p
    - Theorem le_lt_trans : forall n m p, n <= m -> m < p -> n < p.
 *)
Lemma Zleb_ltb_trans_ltb: forall n m p, 
  (Zle_bool n m) = true ->
    (Zlt_bool m p) = true ->
      (Zlt_bool n p) = true.
Proof.
  intros.
  apply Zltb_lt.
  apply Z.le_lt_trans with (m:=m);
  [ apply Z.leb_le; auto |
    apply Z.ltb_lt; auto
  ].
Qed.

(** n < m -> m < p ==> n < p
    - Theorem lt_trans : forall n m p, n < m -> m < p -> n < p.
*)
Lemma Zltb_trans : forall n m p,
  (Zlt_bool n m) = true ->
    (Zlt_bool m p) = true ->
      (Zlt_bool n p) = true.
Proof.
  intros.
  apply Zltb_lt.
  apply Z.lt_trans with (m:=m);
  apply Z.ltb_lt; auto.
Qed.

(** n <= m -> m <= p ==> n <= p
    - Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
*)  
Lemma Zleb_trans : forall n m p,
  (Zle_bool n m) = true ->
    (Zle_bool m p) = true ->
      (Zle_bool n p) = true.
Proof.
  intros.
  apply Zleb_le.
  apply Z.le_trans with (m:=m);
  apply Z.leb_le; auto.
Qed.

(** Lemma lt_succ_r n m : n < succ m <-> n<=m.
*)
Lemma Zltb_pred_r: forall n m, 
  (n <? m)%Z = true <-> (n <=? Z.pred m)%Z = true.
Proof.
  intros.
  assert(HA1: m = Z.succ (Z.pred m)). 
    rewrite Z.succ_pred; auto.
  rewrite HA1; 
  split; intros.  
 - (*case 1*)
  assert(HA2: (n < Z.succ (Z.pred m))%Z).
  apply Zltb_lt; auto.
  apply Zleb_le.
  apply Z.lt_succ_r; auto.
  rewrite Z.succ_pred; auto.
 - (*case 2*)
  assert(HA2: (n <= Z.pred (Z.succ (Z.pred m)))%Z).
  apply Zleb_le; auto.
  rewrite Z.pred_succ in *.
  specialize (Z.lt_succ_r n (Z.pred m)); intro HZ.
  destruct HZ as [HZa HZb].
  specialize (HZb HA2).
  apply Zltb_lt; auto.
Qed.

Lemma Zltb_succ_l: forall n m, 
  (n <? m)%Z = true <-> (Z.succ n <=? m)%Z = true.
Proof.
  intros.
  assert(HA: m = Z.succ (Z.pred m)). 
    rewrite Z.succ_pred; auto.
  rewrite HA.  
  split; intros.
 - (*case 1*)
  apply Zleb_le; auto.
  specialize (Z.succ_le_mono n (Z.pred m)); intro HZ1.
  destruct HZ1 as [HZ1a HZ1b].
  apply HZ1a; auto.
  apply Z.lt_succ_r; auto.
  apply Zltb_lt; auto.
 - (*case 2*)  
  apply Zltb_lt; auto.
  specialize (Z.succ_le_mono n (Z.pred m)); intro HZ1.
  destruct HZ1 as [HZ1a HZ1b].
  apply Z.lt_succ_r; auto.
  apply HZ1b.
  apply Zleb_le; auto.
Qed.

(** ** Zlt *)

Lemma Zlt_le: forall n m, 
  (n < m)%Z -> 
    (n <= m)%Z.
Proof.
  intros.
  assert(HA1: (m <= m)%Z). smack.
  apply Zleb_le; auto.
  apply Zltb_leb_trans_leb with (v:=m); auto.
  apply Zltb_lt; auto.  
  apply Zleb_le; auto.
Qed.

(** 
  - Lemma Zlt_succ_le: forall n m : Z, (n < Z.succ m)%Z -> (n <= m)%Z
  - Lemma Z.le_succ_l: forall n m : Z, (Z.succ n <= m)%Z <-> (n < m)%Z
*)
Lemma Zlt_le_succ_l: forall n m, 
  (n < m)%Z -> 
    (Z.succ n <= m)%Z.
Proof.
  intros.
  specialize (Z.le_succ_l n m); intro HZ.
  destruct HZ as [HZa HZb].
  apply HZb; auto.
Qed.

Lemma Zlt_le_pred_r: forall n m, 
  (n < m)%Z -> 
    (n <= Z.pred m)%Z.
Proof.
  intros.
  apply Zleb_le; auto.
  apply Zltb_pred_r; auto.
  apply Zltb_lt; auto.
Qed.

Lemma Zle_eq_e_l: forall u v,
  Zeq_bool v u = false ->
    (u <= v)%Z ->
      (u < v)%Z.
Proof.
  intros.
  specialize (Zle_lt_or_eq _ _ H0); intro HZ1.
  destruct HZ1; smack.
  specialize (Zeq_bool_neq _ _ H); intro.
  smack.
Qed.

Lemma Zle_eq_e_r: forall u v,
  Zeq_bool u v = false ->
    (u <= v)%Z ->
      (u < v)%Z.
Proof.
  intros.
  specialize (Zle_lt_or_eq _ _ H0); intro HZ1.
  destruct HZ1; smack.
  specialize (Zeq_bool_neq _ _ H); intro.
  smack.
Qed.

Lemma Zle_n1_0: forall v,
  (v <= -1)%Z ->
    (v < 0)%Z /\ (v <= 0)%Z.
Proof.
  intros; split.
  apply Z.le_lt_trans with (m:=(-1)%Z); smack.
  apply Z.le_trans with (m:=(-1)%Z); smack.
Qed.

Ltac apply_Zle_n1_0 :=
  match goal with
  | [H: (?v <= -1)%Z |- _] => 
      specialize (Zle_n1_0 _ H); let HZ := fresh "HZ" in intro HZ; destruct HZ; clear H
  end.

Lemma Zge_p1_0: forall v,
  (1 <= v)%Z ->
    (0 < v)%Z /\ (0 <= v)%Z.
Proof.
  intros; 
  smack.
Qed.

Ltac apply_Zge_p1_0 :=
  match goal with
  | [H: (1 <= ?v)%Z |- _] => 
      specialize (Zge_p1_0 _ H); let HZ := fresh "HZ" in intro HZ; destruct HZ; clear H
  end.


(** In run time check semantics, Zge_bool and Zle_bool is used to define overflow check,
    and in eval_expr_value_in_domain, <= and >= are used, the following lemmas are used
    to build their relationships;
*)
Lemma Le_Neg_Ge: forall x y,  
  (x <= y)%Z ->
    (-y <= -x)%Z.
Proof.
  intros.
  apply Zplus_le_reg_l with (p := y). 
  smack. (*lia*)
Qed.

Lemma Lt_Neg_Gt: forall x y,  
  (x < y)%Z ->
    (-y < -x)%Z.
Proof.
  intros.
  apply Zplus_lt_reg_l with (p := y). 
  smack.
Qed.


(** * ZArith Lemma *)

(** ** Min Lemmas *)

Lemma le_min_ll: forall a b c d,
  (Z.min (Z.min a b) (Z.min c d) <= a)%Z.
Proof.
  intros.
  assert(HA1: (Z.min (Z.min a b) (Z.min c d) <= (Z.min a b))%Z).
    apply Z.le_min_l; auto.
  assert(HA2: ((Z.min a b) <= a)%Z).
    apply Z.le_min_l; auto.
  apply Z.le_trans with (m:=Z.min a b); auto.
Qed.

Lemma le_min_lr: forall a b c d,
  (Z.min (Z.min a b) (Z.min c d) <= b)%Z.
Proof.
  intros.
  assert(HA1: (Z.min (Z.min a b) (Z.min c d) <= (Z.min a b))%Z).
    apply Z.le_min_l; auto.
  assert(HA2: ((Z.min a b) <= b)%Z).
    apply Z.le_min_r; auto.
  apply Z.le_trans with (m:=Z.min a b); auto.
Qed.

Lemma le_min_rl: forall a b c d,
  (Z.min (Z.min a b) (Z.min c d) <= c)%Z.
Proof.
  intros.
  assert(HA1: (Z.min (Z.min a b) (Z.min c d) <= (Z.min c d))%Z).
    apply Z.le_min_r; auto.
  assert(HA2: ((Z.min c d) <= c)%Z).
    apply Z.le_min_l; auto.
  apply Z.le_trans with (m:=Z.min c d); auto.
Qed.

Lemma le_min_rr: forall a b c d,
  (Z.min (Z.min a b) (Z.min c d) <= d)%Z.
Proof.
  intros.
  assert(HA1: (Z.min (Z.min a b) (Z.min c d) <= (Z.min c d))%Z).
    apply Z.le_min_r; auto.
  assert(HA2: ((Z.min c d) <= d)%Z).
    apply Z.le_min_r; auto.
  apply Z.le_trans with (m:=Z.min c d); auto.
Qed.

(** ** Max Lemmas *)

Lemma le_max_ll: forall a b c d,
  (a <= Z.max (Z.max a b) (Z.max c d))%Z.
Proof.
  intros.
  assert(HA1: ((Z.max a b) <= Z.max (Z.max a b) (Z.max c d))%Z).
    apply Z.le_max_l; auto.
  assert(HA2: (a <= (Z.max a b))%Z).
    apply Z.le_max_l; auto.
  apply Z.le_trans with (m:=Z.max a b); auto.
Qed.

Lemma le_max_lr: forall a b c d,
  (b <= Z.max (Z.max a b) (Z.max c d))%Z.
Proof.
  intros.
  assert(HA1: ((Z.max a b) <= Z.max (Z.max a b) (Z.max c d))%Z).
    apply Z.le_max_l; auto.
  assert(HA2: (b <= (Z.max a b))%Z).
    apply Z.le_max_r; auto.
  apply Z.le_trans with (m:=Z.max a b); auto.
Qed.

Lemma le_max_rl: forall a b c d,
  (c <= Z.max (Z.max a b) (Z.max c d))%Z.
Proof.
  intros.
  assert(HA1: ((Z.max c d) <= Z.max (Z.max a b) (Z.max c d))%Z).
    apply Z.le_max_r; auto.
  assert(HA2: (c <= (Z.max c d))%Z).
    apply Z.le_max_l; auto.
  apply Z.le_trans with (m:=Z.max c d); auto.
Qed.

Lemma le_max_rr: forall a b c d,
  (d <= Z.max (Z.max a b) (Z.max c d))%Z.
Proof.
  intros.
  assert(HA1: ((Z.max c d) <= Z.max (Z.max a b) (Z.max c d))%Z).
    apply Z.le_max_r; auto.
  assert(HA2: (d <= (Z.max c d))%Z).
    apply Z.le_max_r; auto.
  apply Z.le_trans with (m:=Z.max c d); auto.
Qed.

Lemma max_abs_f_opp_le0: forall l u,
  (Z.opp (max_abs_f l u) <= 0)%Z.
Proof.
  intros.
  unfold max_abs_f.
  replace 0%Z with (-0)%Z; auto.
  apply Le_Neg_Ge; auto.
  apply Z.le_trans with (m:=(Z.abs l)%Z); auto.
  destruct l; smack.
  apply Z.le_max_l; auto.
Qed.

Lemma max_abs_f_ge0: forall l u,
  (0 <= (max_abs_f l u))%Z.
Proof.
  intros.
  unfold max_abs_f.
  apply Z.le_trans with (m:=(Z.abs l)%Z); auto.
  destruct l; smack.
  apply Z.le_max_l; auto.
Qed.

(** ** Zmult Lemmas *)

(**
   - Lemman Z.mul_comm : forall n m : Z, (n * m)%Z = (m * n)%Z
   - Lemma Z_eq_mult n m : m = 0 -> m * n = 0.
*)

Lemma Zmult_le_le: forall u v,
  (u <= 0)%Z ->
    (v <= 0)%Z ->
      (0 <= u * v)%Z.
Proof.
  intros.
  assert(HA1: (-0 <= (-u))%Z).
    apply Le_Neg_Ge; auto.
  assert(HA2: (-0 <= (-v))%Z).
    apply Le_Neg_Ge; auto.
  simpl in HA1, HA2.  
  assert (HA3: (0*(-v) <= (-u)*(-v))%Z).
    apply Zmult_le_compat_r; auto. 
  clear - HA3. 
  rewrite Zmult_opp_opp in HA3.
  smack.
Qed.

Lemma Zmult_le_lt: forall u v,
  (u <= 0)%Z ->
    (v < 0)%Z ->
      (0 <= u * v)%Z.
Proof.
  intros.
  assert(HA1: (v <= 0)%Z).
    assert(HA2: (v <=? 0)%Z = true).
    apply Zltb_leb_trans_leb with (v:=0%Z); auto.
    apply Zltb_lt; auto.
    apply Zleb_le; auto.
  apply Zmult_le_le; auto.
Qed.

Lemma Zmult_lt_lt: forall u v,
  (u < 0)%Z ->
    (v < 0)%Z ->
      (0 < u * v)%Z.
Proof.
  intros.
  assert(HA1: (-0 < (-u))%Z).
    apply Lt_Neg_Gt; auto. simpl in HA1.
  assert(HA2: (-0 < (-v))%Z).
    apply Lt_Neg_Gt; auto. simpl in HA2.
  assert(HA3: (0 * (-v) < (-u) * (-v))%Z).
    apply Zmult_lt_compat_r; auto. 
  rewrite Zmult_opp_opp in HA3.
  smack.
Qed.

Lemma Zmult_le_ge_r: forall u v,
  (u <= 0)%Z ->
    (0 <= v)%Z ->
      (u * v <= 0)%Z.
Proof.
  intros.
  assert(HA3: (u * v <= 0 * v)%Z).
    apply Zmult_le_compat_r; auto. 
  smack.
Qed.

Lemma Zmult_le_ge_l: forall u v,
  (u <= 0)%Z ->
    (0 <= v)%Z ->
      (v * u <= 0)%Z.
Proof.
  intros.
  assert(HA3: (v*u <= v*0)%Z).
    apply Zmult_le_compat_l; auto. 
  smack.
Qed.

(**
  - https://coq.inria.fr/V8.1/stdlib/Coq.ZArith.BinInt.html
  - Lemma Zopp_mult_distr_l : forall n m:Z, - (n * m) = - n * m.
  - Lemma Zopp_mult_distr_r : forall n m:Z, - (n * m) = n * - m.
  - Lemma Zopp_mult_distr_l_reverse : forall n m:Z, - n * m = - (n * m).
  - Lemma Zmult_opp_comm : forall n m:Z, - n * m = n * - m.
  - Lemma Zmult_opp_opp : forall n m:Z, - n * - m = n * m.
*)

Lemma Zmult_le_rev_l: forall n m p,
  (n <= m)%Z ->
    (p <= 0)%Z ->
      (p * m <= p * n)%Z.
Proof.
  intros.
  specialize (Le_Neg_Ge _ _ H0); intro HZ; smack.
  assert(HA1: ((-p)*n <= (-p)*m)%Z).
    apply Zmult_le_compat_l; auto.
  specialize (Le_Neg_Ge _ _ HA1); intro HZ1.
  rewrite Zmult_opp_comm in HZ1. rewrite Zmult_opp_comm in HZ1. 
  rewrite Zopp_mult_distr_l in HZ1. rewrite Zopp_mult_distr_l in HZ1.
  rewrite Zmult_opp_opp in HZ1.
  rewrite Zmult_opp_opp in HZ1.
  auto.
Qed.

Lemma Zmult_le_rev_r: forall n m p,
  (n <= m)%Z ->
    (p <= 0)%Z ->
      (m * p <= n * p)%Z.
Proof.
  intros.
  specialize (Le_Neg_Ge _ _ H0); intro HZ; smack.
  assert(HA1: (n*(-p) <= m*(-p))%Z).
    apply Zmult_le_compat_r; auto.
  specialize (Le_Neg_Ge _ _ HA1); intro HZ1.
  rewrite Zopp_mult_distr_l in HZ1. rewrite Zopp_mult_distr_l in HZ1.
  rewrite Zmult_opp_opp in HZ1.
  rewrite Zmult_opp_opp in HZ1.
  auto.
Qed.

(** ** Zquot Lemmas *)

(*
   https://coq.inria.fr/V8.1/stdlib/Coq.ZArith.BinInt.html
   - Theorem Zopp_mult_distr_l : forall n m:Z, - (n * m) = - n * m.
   - Theorem Zopp_mult_distr_r : forall n m:Z, - (n * m) = n * - m.
   - Lemma Zopp_mult_distr_l_reverse : forall n m:Z, - n * m = - (n * m).
   - Theorem Zmult_opp_comm : forall n m:Z, - n * m = n * - m.
   - Theorem Zmult_opp_opp : forall n m:Z, - n * - m = n * m.

   https://coq.inria.fr/library/Coq.ZArith.Zquot.html 
   - Lemma Z_quot_monotone a b c : 0<=c -> a<=b -> a÷c <= b÷c.
   - Lemma Zquot_0_r a : a ÷ 0 = 0.
   - Lemma Zquot_0_l a : 0÷a = 0.
   - Theorem Zquot_opp_l a b : (-a)÷b = -(a÷b).
   - Theorem Zquot_opp_r a b : a÷(-b) = -(a÷b).
   - Theorem Zquot_opp_opp a b : (-a)÷(-b) = a÷b.
   - Theorem Z.quot_1_r : forall a : Z, (a ÷ 1)%Z = a
*)

Lemma Zquot_antitone: forall a b c, 
  (c <= 0)%Z -> 
    (a <= b)%Z ->
      (Z.quot b c <= Z.quot a c)%Z.
Proof.
  intros.
  assert(HA1: (-0 <= -c)%Z).
    apply Le_Neg_Ge; auto. simpl in HA1.
  specialize (Z_quot_monotone _ _ _ HA1 H0); intro HZ1.
  assert(HA2: (-(b ÷ -c) <= - (a ÷ -c))%Z).
    apply Le_Neg_Ge; auto.
  repeat progress rewrite <- Zquot_opp_l in HA2.
  repeat progress rewrite Zquot_opp_opp in HA2.
  auto.
Qed.

Lemma Zquot_le_compat_p_p: forall a b c, 
  (0 <= a)%Z -> 
    (0 < b)%Z -> (b <= c)%Z ->
      (Z.quot a c <= Z.quot a b)%Z.
Proof.
  intros.
  assert(Hb: (0 <= b)%Z).
    apply Zlt_le; auto.
  assert(Hc: (0 <= c)%Z).
    apply Z.le_trans with (m:=b); auto.
  specialize (Zle_lt_or_eq _ _ H1); intro HZ1.
  destruct HZ1 as [HZ1a | HZ1b].
  repeat progress rewrite Zquot_Zdiv_pos; auto.
  apply Zdiv_le_compat_l; smack.
  subst.
  apply Z.le_refl.
Qed.

Lemma Zquot_le_compat_n_p: forall a b c, 
  (a <= 0)%Z -> 
    (0 < b)%Z -> (b <= c)%Z ->
      (Z.quot a b <= Z.quot a c)%Z.
Proof.
  intros.
  assert(Ha: (-0 <= -a)%Z).
    apply Le_Neg_Ge; auto. simpl in Ha.
  specialize (Zquot_le_compat_p_p _ _ _ Ha H0 H1); intro HZ1.
  repeat progress rewrite Zquot_opp_l in HZ1.
  specialize (Le_Neg_Ge _ _ HZ1); intro HZ2.
  smack.
Qed.

Lemma Zquot_le_compat_p_n: forall a b c, 
  (0 <= a)%Z -> 
    (c < 0)%Z -> (b <= c)%Z ->
      (Z.quot a c <= Z.quot a b)%Z.
Proof.
  intros.
  assert(Hc: (-0 < -c)%Z).
    apply Lt_Neg_Gt; auto. simpl in Hc.
  assert(Hbc: (-c <= -b)%Z).
    apply Le_Neg_Ge; auto.
  specialize (Zquot_le_compat_p_p _ _ _ H Hc Hbc); intro HZ1.
  specialize (Le_Neg_Ge _ _ HZ1); intro HZ2.
  repeat progress rewrite Zquot_opp_r in HZ2.
  smack.
Qed.

Lemma Zquot_le_compat_n_n: forall a b c, 
  (a <= 0)%Z -> 
    (c < 0)%Z -> (b <= c)%Z ->
      (Z.quot a b <= Z.quot a c)%Z.
Proof.
  intros.
  assert(Ha: (-0 <= -a)%Z).
    apply Le_Neg_Ge; auto. simpl in Ha.
  specialize (Zquot_le_compat_p_n _ _ _ Ha H0 H1); intro HZ1.
  repeat progress rewrite Zquot_opp_l in HZ1.
  specialize (Le_Neg_Ge _ _ HZ1); intro HZ2.
  smack.  
Qed.

Lemma Zquot_p_p_p: forall u v,
  (0 <= u)%Z ->
    (0 < v)%Z ->
      (0 <= Z.quot u v)%Z.
Proof.
  intros.
  assert (HA1: (0 * v <= u)%Z).
    smack.
  specialize (Zquot_le_lower_bound _ _ _ H0 HA1); intro HZ1.
  auto.
Qed.

Lemma Zquot_n_n_p: forall u v,
  (u <= 0)%Z ->
    (v < 0)%Z ->
      (0 <= Z.quot u v)%Z.
Proof.
  intros.
  assert (HA1: (-0 < -v)%Z).
    apply Lt_Neg_Gt; auto. simpl in HA1.
  assert (HA2: (-0 <= -u)%Z).
    apply Le_Neg_Ge; auto. simpl in HA2.
  assert (HA3: (0 * (-v) <= -u)%Z).
    smack.
  specialize (Zquot_le_lower_bound _ _ _ HA1 HA3); intro HZ1.
  rewrite Zquot_opp_opp in HZ1.
  auto.
Qed.

Lemma Zquot_p_n_n: forall u v,
  (0 <= u)%Z ->
    (v < 0)%Z ->
      (Z.quot u v <= 0)%Z.
Proof.
  intros.
  assert (HA1: (-0 < -v)%Z).
    apply Lt_Neg_Gt; auto. simpl in HA1.
  assert (HA2: (0 * (-v) <= u)%Z).
    smack.
  specialize (Zquot_le_lower_bound _ _ _ HA1 HA2); intro HZ1.
  rewrite Zquot_opp_r in HZ1.
  specialize (Le_Neg_Ge _ _ HZ1); intro HZ2.
  smack.
Qed.

Lemma Zquot_n_p_n: forall u v,
  (u <= 0)%Z ->
    (0 < v)%Z ->
      (Z.quot u v <= 0)%Z.
Proof.
  intros.
  assert (HA1: (-0 <= -u)%Z).
    apply Le_Neg_Ge; auto. simpl in HA1.
  specialize (Zquot_p_p_p _ _ HA1 H0); intro HZ1.
  rewrite Zquot_opp_l in HZ1.
  specialize (Le_Neg_Ge _ _ HZ1); intro HZ2.
  smack.
Qed.

(**
   https://coq.inria.fr/library/Coq.ZArith.BinInt.html
   - Lemma abs_eq n : 0 <= n -> abs n = n.
   - Lemma abs_neq n : n <= 0 -> abs n = - n.
*)

Lemma Zabs_ge_v: forall v,
  (v <= Z.abs v)%Z.
Proof.
  intros.
  destruct v; smack.
  (* apply Zle_neg_pos; auto. *)
Qed.

Lemma Zabs_ge_neg_v: forall v,
  (-v <= Z.abs v)%Z.
Proof.
  intros.
  destruct v; smack.
  (* apply Zle_neg_pos; auto. *)
Qed.

Lemma Zquot_n1_opp: forall v,
  (Z.quot v (-1) = -v)%Z.
Proof.
  intros.
  replace (-1)%Z with (Z.opp 1).
  rewrite Zquot_opp_r.
  destruct v.
  smack.
  rewrite Zquot_Zdiv_pos; smack.
    rewrite Zdiv_1_r; auto.
  rewrite <- Zquot_opp_l.
  rewrite Zquot_Zdiv_pos; smack.
  smack.
Qed.

Lemma Zabs_quot_neg1: forall v,
  (v <= 0)%Z ->
    (Z.abs v = Z.quot v (-1))%Z.
Proof.
  intros.
  specialize (Z.abs_neq _ H); intro HZ.
  rewrite HZ.
  rewrite Zquot_n1_opp; auto.
Qed.

Lemma Zquot_p1_interval: forall l v u,
  (l <= v)%Z ->
    (v <= u)%Z ->
      (Z.opp (max_abs_f l u) <= Z.quot v 1 <= (max_abs_f l u))%Z.
Proof.
  intros.
  replace (v ÷ 1)%Z with v.
  unfold max_abs_f;
  split.
 - (*case 1*)
  apply Z.le_trans with (m:=l); auto.
  replace l with (--l)%Z; smack.
(*  apply Le_Neg_Ge; smack.
  replace (--l)%Z with l; smack.
  apply Z.le_trans with (m:=Z.abs l); auto.  
  apply Zabs_ge_neg_v; auto.
  apply Z.le_max_l; auto. *)
 - (*case 2*)  
  apply Z.le_trans with (m:=u); auto.
  apply Z.le_trans with (m:=Z.abs u); auto.
  apply Zabs_ge_v; auto.
  apply Z.le_max_r; auto.
 - (*case 3*)
  smack.  
Qed.

Lemma Zquot_n1_interval: forall l v u,
  (l <= v)%Z ->
    (v <= u)%Z ->
      (Z.opp (max_abs_f l u) <= Z.quot v (-1) <= (max_abs_f l u))%Z.
Proof.
  intros.
  rewrite Zquot_n1_opp.
  unfold max_abs_f.
  split.
 - (*case 1*)  
  apply Z.le_trans with (m:=(-u)%Z); auto.
  apply Le_Neg_Ge; auto.
  apply Z.le_trans with (m:=(Z.abs u)%Z); auto.
  apply Zabs_ge_v; auto.
  apply Z.le_max_r; auto.
  apply Le_Neg_Ge; auto.  
 - (*case 2*)  
  apply Z.le_trans with (m:=(-l)%Z); auto.
  apply Le_Neg_Ge; auto.
  apply Z.le_trans with (m:=(Z.abs l)%Z); auto.
  apply Zabs_ge_neg_v; auto.
  apply Z.le_max_l; auto.
Qed.

(********************************************************************)
(********************************************************************)

(** * Modulus Interval Correctness *)
(**
   The following three lemmas can be manually proved to be correct.
*)
Lemma modulus_in_bound: forall v1 v2 l1 l2 u1 u2 l u,
  in_bound v1 (Interval l1 u1) true ->
  in_bound v2 (Interval l2 u2) true -> 
  Zeq_bool v2 0 = false ->
  modulus_min_max_f l1 u1 l2 u2 = (l, u) ->
  in_bound (Z.modulo v1 v2) (Interval l u) true.
Proof.
  intros;
  destruct v2; auto.
 - (* case 1: v2 = 0: conflict *)
   smack.
 - (* case 2: v2 > 0 *)
   assert(HA1: ((Z.pos p) > 0)%Z). smack.
   specialize (Z_mod_lt v1 _ HA1); intro HZ1.
   destruct HZ1 as [HZ1a HZ1b].
   inversion H0; subst.
   remember ((l2 <=? Z.pos p)%Z) as x1.
   remember ((Z.pos p <=? u2)%Z) as x2.
   destruct x1, x2; inversion H5; clear H5.
   symmetry in Heqx1, Heqx2.
   
   unfold modulus_min_max_f in H2.
   remember ((u2 <=? -1)%Z) as y1.
   destruct y1; subst;
   symmetry in Heqy1.
   (* sub-case 1: [l2, u2] < 0 : conflict *)
   specialize (Zleb_trans _ _ _ Heqx2 Heqy1); smack.

   remember ((1 <=? l2)%Z) as y2; 
   destruct y2; subst;
   symmetry in Heqy2;
   symmetry in H2; inversion H2; subst.
   (* sub-case 2: [l2, u2] > 0 *)
   constructor; auto.
   assert(HA2: (0 <=? v1 mod Z.pos p)%Z = true).
     apply Zleb_le; auto.
   rewrite HA2; simpl.
   assert(HA3: (v1 mod Z.pos p <? Z.pos p)%Z = true).
     apply Zltb_lt; auto.
   assert(HA4: (v1 mod Z.pos p <? u2)%Z = true).
     apply Zltb_leb_trans_ltb with (m:=Z.pos p); auto.
   apply Zltb_pred_r; auto.  
   (* sub-case 3: 0 is in [l2, u2] *)
   constructor; auto.
   assert(HA2: ((if Zeq_bool l2 0 then 0 else l2 + 1) <=? v1 mod Z.pos p)%Z = true).
     remember (Zeq_bool l2 0) as b1.
     destruct b1; subst;
     apply Zleb_le; auto.
     specialize (Le_False_Lt _ _ Heqy2); intro HZ.
     replace 1%Z with (Z.succ 0) in HZ; auto.
     specialize (Zlt_succ_le _ _ HZ); intro HZ2.
     specialize (Zle_lt_or_eq _ _ HZ2); intro HZ3.
     destruct HZ3 as [HZ3a | HZ3b].
     apply Zlt_le_succ; auto.
     apply Z.lt_le_trans with (m:=0%Z); auto. smack.
   rewrite HA2; simpl.
   remember (Zeq_bool u2 0) as b2.
   destruct b2; symmetry in Heqb2.
   rewrite (Zeq_bool_eq _ _ Heqb2) in Heqx2; inversion Heqx2.
   apply Zltb_pred_r; auto.
   apply Zltb_leb_trans_ltb with (m := Z.pos p); auto.
   apply Zltb_lt; auto.
 - (* case 3: v2 < 0 *)
   assert(HA1: ((Z.neg p) < 0)%Z). constructor; auto.
   specialize (Z_mod_neg v1 _ HA1); intro HZ1.
   destruct HZ1 as [HZ1a HZ1b].
   inversion H0; subst.
   remember ((l2 <=? Z.neg p)%Z) as x1.
   remember ((Z.neg p <=? u2)%Z) as x2.
   destruct x1, x2; inversion H5; clear H5.
   symmetry in Heqx1, Heqx2.
   
   unfold modulus_min_max_f in H2.
   remember ((u2 <=? -1)%Z) as y1.
   destruct y1; subst;
   symmetry in Heqy1.
   (* sub-case 1: [l2, u2] < 0 *)
   inversion H2; subst.
   constructor; auto.
   assert(HA2: (v1 mod Z.neg p <=? 0)%Z = true).
     apply Zleb_le; auto.
   rewrite HA2; auto.
   assert(HA3: (l2 <? v1 mod Z.neg p)%Z = true).
     apply Zleb_ltb_trans_ltb with (m:=Z.neg p); auto.
     apply Zltb_lt; auto.
   assert(HA4: (l2 + 1 <=? v1 mod Z.neg p)%Z = true).
     replace (l2 + 1)%Z with (Z.succ l2); smack.
     apply Zltb_succ_l; auto.
   rewrite HA4; auto.
   (* sub-case 2: [l2, u2] > 0 : conflict *)
   remember ((1 <=? l2)%Z) as y2; 
   destruct y2; subst;
   symmetry in Heqy2;
   symmetry in H2; inversion H2; subst.

   specialize (Zleb_trans _ _ _ Heqy2 Heqx1); smack.
   (* sub-case 3: 0 is in [l2, u2] *)
   constructor; auto.
   assert(HA2: ((if Zeq_bool l2 0 then 0 else l2 + 1) <=? v1 mod Z.neg p)%Z = true).
     remember (Zeq_bool l2 0) as b1.
     destruct b1; subst;
     apply Zleb_le; auto;
     symmetry in Heqb1.
     rewrite (Zeq_bool_eq _ _ Heqb1) in Heqx1; inversion Heqx1.
     apply Zlt_le_succ; auto.
     apply Z.le_lt_trans with (m:=Z.neg p); auto.
     apply Zleb_le; auto.
   rewrite HA2; simpl.
   
   remember (Zeq_bool u2 0) as b2.
   destruct b2; symmetry in Heqb2.
   apply Zleb_le; auto.
   specialize (Le_False_Lt _ _ Heqy1); intro HZ.
   specialize (Z.le_succ_l (-1)%Z u2); intro HZ3.
   destruct HZ3 as [HZ3a HZ3b].
   specialize (HZ3b HZ). simpl in HZ3b.
   specialize (Zle_lt_or_eq _ _ HZ3b); intro HZ4.
     destruct HZ4 as [HZ4a | HZ4b]; smack.
   assert(HA3: (v1 mod Z.neg p <? u2)%Z = true).
     apply Zleb_ltb_trans_ltb with (m:=0%Z); auto.
     apply Zleb_le; auto. 
     apply Zltb_lt; auto.
     apply Zltb_pred_r; auto.
Qed.

Ltac apply_modulus_in_bound :=
  match goal with
  | [H1: in_bound ?v1 (Interval ?l1 ?u1) true,
     H2: in_bound ?v2 (Interval ?l2 ?u2) true, 
     H3: Zeq_bool ?v2 0 = false,
     H4: modulus_min_max_f ?l1 ?u1 ?l2 ?u2 = (?l, ?u) |- _] =>
      specialize (modulus_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ:=fresh "HZ" in intro HZ
  | [H1: in_bound ?v1 (Interval ?l1 ?u1) true,
     H2: in_bound ?v2 (Interval ?l2 ?u2) true, 
     H3: Zeq_bool ?v2 0 = false,
     H4: (?l, ?u) = modulus_min_max_f ?l1 ?u1 ?l2 ?u2 |- _] =>
      symmetry in H4;
      specialize (modulus_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ:=fresh "HZ" in intro HZ
  end.

(** * Multiply Interval Correctness *)

Lemma multiply_in_bound: forall v1 v2 l1 l2 u1 u2,
  in_bound v1 (Interval l1 u1) true ->
  in_bound v2 (Interval l2 u2) true -> 
  in_bound (v1*v2) (Interval (multiply_min_f l1 u1 l2 u2) (multiply_max_f l1 u1 l2 u2)) true.
Proof.
  intros;
    unfold multiply_min_f, multiply_max_f;
    destruct v1, v2; smack;
      repeat progress match goal with
                      | [H: in_bound ?v (Interval ?l ?u) true |- _] => inversion H; subst; clear H
                      end;
      repeat progress apply_Zleb_true_le_true;
      constructor; auto.
  - (* case 1: v1 = 0, v2 = 0 *)
    (* l1 <= v1 <= u1, 0 <= u2 ==> l1*u2 <= v1*u2 <= u1 * u2, here v1 is 0*)
    assert (HA1: (l1*u2 <= 0*u2)%Z).
    { apply Zmult_le_compat_r; auto. }
    assert (HA2: (0*u2 <= u1*u2)%Z).
    { apply Zmult_le_compat_r; auto. }
    clear - HA1 HA2. (* smack. lia solves the goal directly with coq 8.13 *)
    assert(HA3: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= 0)%Z).
    { apply Z.le_trans with (m:=(l1*u2)%Z); auto.
      apply le_min_lr; auto. }
    assert(HA4: (0 <= Z.max (Z.max (l1 * l2) (l1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
    { apply Z.le_trans with (m:=(u1*u2)%Z); auto. 
      apply le_max_rr; auto. }
    apply Zle_true_leb_true; auto.
  - (* case 2: v1 = 0, v2 > 0 *)
    assert(HA: (0 <= u2)%Z).
    { apply Z.le_trans with (m:=Z.pos p); smack. }
    (* l1 <= v1 <= u1, 0 <= u2 ==> l1*u2 <= v1*u2 <= u1 * u2, here v1 is 0*)
    assert (HA1: (l1*u2 <= 0*u2)%Z).
    { apply Zmult_le_compat_r; auto. }
    assert (HA2: (0*u2 <= u1*u2)%Z).
    { apply Zmult_le_compat_r; auto. }
    clear - HA1 HA2. (*smack. same: coq 8.13 solved this directly (lia) *)
    assert(HA3: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= 0)%Z).
    { apply Z.le_trans with (m:=(l1*u2)%Z); auto.
      apply le_min_lr; auto. }
    assert(HA4: (0 <= Z.max (Z.max (l1 * l2) (l1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
    { apply Z.le_trans with (m:=(u1*u2)%Z); auto.
      apply le_max_rr; auto. }
    apply Zle_true_leb_true; auto.  
 - (* case 3: v1 = 0, v2 < 0 *)
   assert(HA: (l2 <= 0)%Z).
   { apply Z.le_trans with (m:=Z.neg p); auto.
     apply Pos2Z.neg_is_nonpos; auto. }
   (* l2 <= 0, 0 <= u1 ==> l2*u1 <= 0*)
   assert (HA1: (u1 * l2 <= u1 * 0)%Z).
   { apply Zmult_le_compat_l; auto. }
   rewrite (Z.mul_comm u1 0%Z) in HA1. (*smack. same 8.13 solves *)
  assert (HA2: (0 <= l1 * l2)%Z).
  { apply Zmult_le_le; auto. }
  assert(HA3: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= 0)%Z).
  { apply Z.le_trans with (m:=(u1*l2)%Z); auto. 
    apply le_min_rl; auto. }
  assert(HA4: (0 <= Z.max (Z.max (l1 * l2) (l1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
  { apply Z.le_trans with (m:=(l1*l2)%Z); auto.
    apply le_max_ll; auto. }
  apply Zle_true_leb_true; auto.
 - (* case 4: v1 > 0, v2 = 0 *)
  assert(HA: (0 <= u1)%Z).
  { apply Z.le_trans with (m:=Z.pos p); smack. }
  (* l2 <= 0 <= u2 ==> u1*l2 <= u1*0 <= u1*u2*)
  assert (HA1: (u1 * l2 <= u1 * 0)%Z).
  { apply Zmult_le_compat_l; auto.  }
  rewrite (Z.mul_comm u1 0%Z) in HA1. (* smack. same*)
  assert (HA2: (u1 * 0 <= u1 * u2)%Z).
  { apply Zmult_le_compat_l; auto. }
  rewrite (Z.mul_comm u1 0%Z) in HA2. (* smack. same *)
  assert(HA3: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= 0)%Z).
  { apply Z.le_trans with (m:=(u1*l2)%Z); auto.
    apply le_min_rl; auto. }
  assert(HA4: (0 <= Z.max (Z.max (l1 * l2) (l1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
  { apply Z.le_trans with (m:=(u1*u2)%Z); auto.
    apply le_max_rr; auto. }
  apply Zle_true_leb_true; auto.
 - (* case 5: v1 > 0, v2 > 0 *)
  (* l1 <= v1 <= u1 ==> l1*u2 <= (v1*v2 <=) <= v1*u2 <= u1*u2; l1*l2<=v1*v2 *)
  assert(HA1a: (0 <= u1)%Z).
  {  apply Z.le_trans with (m:=Z.pos p); smack.  }
  assert(HA1b: (0 <= u2)%Z).
  {  apply Z.le_trans with (m:=Z.pos p0); smack. }
  assert (HA2: ((Z.pos p) * u2 <= u1 * u2)%Z).
  {  apply Zmult_le_compat_r; auto. }
  assert (HA3: ((Z.pos p) * (Z.pos p0) <= (Z.pos p) * u2)%Z).
  {  apply Zmult_le_compat_l; smack. }
  assert(HA4: (Z.pos p * Z.pos p0 <= u1 * u2)%Z).
  {  apply Z.le_trans with (m:=(Z.pos p * u2)%Z); auto. }
  assert(HZ1: ((Z.pos p) * (Z.pos p0) <= Z.max (Z.max (l1 * l2) (l1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
  { apply Z.le_trans with (m:=(u1*u2)%Z); auto.
    apply le_max_rr; auto. }
  destruct l1; subst.
  (* 1. l1 = 0 *)
  + assert(HZ2: (Z.min (Z.min (0 * l2) (0 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= (Z.pos p) * (Z.pos p0))%Z).
    { apply Z.le_trans with (m:=(0*l2)%Z); auto.
      apply le_min_lr; auto. }
  apply Zle_true_leb_true; auto.  
  (* 2. l1 > 0 *)
  + destruct l2; subst.
    (* - 2.1 l2 = 0 *)
    * assert(HZ2: (Z.min (Z.min (Z.pos p1 * 0) (Z.pos p1 * u2)) (Z.min (u1 * 0) (u1 * u2)) <= (Z.pos p) * (Z.pos p0))%Z).
      { apply Z.le_trans with (m:=(u1 * 0)%Z); auto.
        apply le_min_rl; auto.
        rewrite (Z.mul_comm u1 0%Z). smack. }
      apply Zle_true_leb_true; auto.  
      (* - 2.2 l2 > 0 *)
    * assert(HZ2: (Z.min (Z.min (Z.pos p1 * Z.pos p2) (Z.pos p1 * u2)) (Z.min (u1 * Z.pos p2) (u1 * u2)) <= (Z.pos p) * (Z.pos p0))%Z).
      { apply Z.le_trans with (m:=((Z.pos p1) * (Z.pos p2))%Z); auto. 
        - apply le_min_ll; auto. 
        - apply Zmult_le_compat; smack. }
      apply Zle_true_leb_true; auto.    
    (* - 2.3 l2 < 0 *)
    * assert(HA_1: (u1 * (Z.neg p2) <= u1 * 0)%Z).
      { apply Zmult_le_compat_l; smack. }
      rewrite (Z.mul_comm u1 0) in HA_1.
      rewrite (Z_eq_mult u1 0%Z) in HA_1; auto.
      assert(HZ2: (Z.min (Z.min (Z.pos p1 * Z.neg p2) (Z.pos p1 * u2)) (Z.min (u1 * Z.neg p2) (u1 * u2)) <= (Z.pos p) * (Z.pos p0))%Z).
      { apply Z.le_trans with (m:=(u1 * (Z.neg p2))%Z); auto.
        apply le_min_rl; auto.
        apply Z.le_trans with (m:=0%Z); auto. }
  apply Zle_true_leb_true; auto.
  (* 3. l1 < 0 *)
  + assert(HA_1: ((Z.neg p1) * u2 <= 0 * u2)%Z).
    { apply Zmult_le_compat_r; smack. }
    rewrite (Z_eq_mult u2 0%Z) in HA_1; auto.
    assert(HZ2: (Z.min (Z.min (Z.neg p1 * l2) (Z.neg p1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= (Z.pos p) * (Z.pos p0))%Z).
    { apply Z.le_trans with (m:=(Z.neg p1 * u2)%Z); auto.
      apply le_min_lr; auto.
      apply Z.le_trans with (m:=0%Z); auto. }
    apply Zle_true_leb_true; auto.
 - (* case 6: v1 > 0, v2 < 0 *)
  assert(HA1a: (0 <= u1)%Z).
  { apply Z.le_trans with (m:=Z.pos p); smack. }
  assert(HA1b: (l2 <= 0)%Z).
  {  apply Z.le_trans with (m:=Z.neg p0); auto.
    specialize (Zlt_neg_0 p0); intro HZ1. smack. }
  assert(HA1c: ((Z.pos p)*(Z.neg p0) <= 0)%Z).
  {  apply Zmult_le_ge_l; auto.
      specialize (Zlt_neg_0 p0); intro; smack.
    smack. }

  (* u1*l2 <= v1*v2 *)
  assert(HA2: (u1*l2 <= (Z.pos p)*(Z.neg p0))%Z).
  { (* l2 <= v2 and 0 <= u1, so u1*l2 <= u1*v2 *)
    assert(HA2a: (u1*l2 <= u1*(Z.neg p0))%Z).
    { apply Zmult_le_compat_l; smack. }
    assert(HA2b: (u1*(Z.neg p0) <= (Z.pos p)*(Z.neg p0))%Z).
    { apply Zmult_le_rev_r; auto. }
    apply Z.le_trans with (m:=(u1 * Z.neg p0)%Z); auto. }

  assert(HZ1: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= Z.neg (p * p0))%Z).
  { apply Z.le_trans with (m:=(u1 * l2)%Z); auto.
    apply le_min_rl; auto. }
      
  destruct l1; subst.
  (* 1. l1 = 0 *)  
  + assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (0 * l2) (0 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
    { apply Z.le_trans with (m:=(0 * u2)%Z); auto.
      apply le_max_lr; auto. }
    apply Zle_true_leb_true; auto.
  (* 2. l1 > 0 *)  
  + destruct u2; subst.
    (* - 2.1. u2 = 0 *)
    * assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (Z.pos p1 * l2) (Z.pos p1 * 0)) (Z.max (u1 * l2) (u1 * 0)))%Z).
      { apply Z.le_trans with (m:=(u1 * 0)%Z); auto.
        rewrite (Z.mul_comm u1 0%Z); smack.
        apply le_max_rr; auto. }
      apply Zle_true_leb_true; auto.
    (* - 2.2. u2 > 0 *)
    * assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (Z.pos p1 * l2) (Z.pos p1 * Z.pos p2)) (Z.max (u1 * l2) (u1 * Z.pos p2)))%Z).
      { apply Z.le_trans with (m:=(u1 * (Z.pos p2))%Z); auto.
        apply Z.le_trans with (m:=(u1 * 0)%Z); smack.
        apply le_max_rr; auto. }
      apply Zle_true_leb_true; auto.
    (* - 2.3. u2 < 0 *)
    (* v1*v2 <= l1*u2 *)
    * assert(HA3: ((Z.pos p)*(Z.neg p0) <= (Z.pos p1)*(Z.neg p2))%Z).
      { (* v1*v2 <= v1*u2 *)
        assert(HA3a: ((Z.pos p)*(Z.neg p0) <= (Z.pos p)*(Z.neg p2))%Z).
        { apply Zmult_le_compat_l; smack. }
        (* v1*u2 <= l1*u2 *)
        assert(HA3b: ((Z.pos p)*(Z.neg p2) <= (Z.pos p1)*(Z.neg p2))%Z).
        { apply Zmult_le_rev_r; smack. }
        apply Z.le_trans with (m:=(Z.pos p * Z.neg p2)%Z); auto. }
      assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (Z.pos p1 * l2) (Z.pos p1 * Z.neg p2)) (Z.max (u1 * l2) (u1 * Z.neg p2)))%Z).
      { apply Z.le_trans with (m:=((Z.pos p1)*(Z.neg p2))%Z); auto.
        apply le_max_lr; auto. }
      apply Zle_true_leb_true; auto.
  (* 3. l1 < 0 *)  
  (* v1*v2 <= l1*l2 *)
  + assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (Z.neg p1 * l2) (Z.neg p1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
    { apply Z.le_trans with (m:=(0)%Z); auto. 
      apply Z.le_trans with (m:=(Z.neg p1 * l2)%Z); auto.
      - apply Zmult_le_le; auto.
      - apply le_max_ll; auto. }
    apply Zle_true_leb_true; auto.
 - (* case 7: v1 < 0, v2 = 0 *)
  assert(HA: (l1 <= 0)%Z).
  { apply Z.le_trans with (m:=Z.neg p); auto.
    specialize (Zlt_neg_0 p); intro; smack. }
  (* l1*u2 <= v1*v2 *)
  assert (HA1: (l1*u2 <= (Z.neg p)*0)%Z).
  { apply Zmult_le_ge_r; auto. }
  (* v1*v2 <= l1*l2 *)
  assert (HA2: ((Z.neg p)*0 <= l1 * l2)%Z).
  { rewrite (Z.mul_comm (Z.neg p) 0). simpl.
    apply Zmult_le_le; auto. }
  rewrite (Z.mul_comm (Z.neg p) 0) in HA2; simpl in HA2.

  assert(HZ1: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= 0)%Z).
  { apply Z.le_trans with (m:=(l1*u2)%Z); auto.
    apply le_min_lr; auto. }
  assert(HZ2: (0 <= Z.max (Z.max (l1 * l2) (l1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
  { apply Z.le_trans with (m:=(l1*l2)%Z); auto.
    apply le_max_ll; auto. }
  apply Zle_true_leb_true; auto.   
 - (* case 8: v1 < 0, v2 > 0 *)
  assert(HA1a: (0 <= u2)%Z).
  { apply Z.le_trans with (m:=Z.pos p0); smack. }
  assert(HA1b: (l1 <= 0)%Z).
  { apply Z.le_trans with (m:=Z.neg p); auto.
    specialize (Zlt_neg_0 p); intro HZ1. smack. }
  assert(HA1c: ((Z.pos p)*(Z.neg p0) <= 0)%Z).
  { apply Zmult_le_ge_l; auto. 
    specialize (Zlt_neg_0 p0); intro; smack.
    smack. }

  (* l1*u2 <= v1*v2 *)
  assert(HA2: (l1*u2 <= (Z.neg p)*(Z.pos p0))%Z).
  { (* l1 <= v1 and 0 <= u2, so l1*u2 <= v1*u2 *)
    assert(HA2a: (l1*u2 <= (Z.neg p)*u2)%Z).
    { apply Zmult_le_compat_r; smack. }
    assert(HA2b: ((Z.neg p)*u2 <= (Z.neg p)*(Z.pos p0))%Z).
    { apply Zmult_le_rev_l; auto. }
    apply Z.le_trans with (m:=((Z.neg p)*u2)%Z); auto. }

  assert(HZ1: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (u1 * l2) (u1 * u2)) <= Z.neg (p * p0))%Z).
  { apply Z.le_trans with (m:=(l1 * u2)%Z); auto.
    apply le_min_lr; auto. }
      
  destruct l2; subst.
  (* 1. l2 = 0 *)  
  + assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (l1 * 0) (l1 * u2)) (Z.max (u1 * 0) (u1 * u2)))%Z).
    { apply Z.le_trans with (m:=(u1*0)%Z); auto.
      rewrite (Z.mul_comm u1 0%Z); smack.
      apply le_max_rl; auto. }
    apply Zle_true_leb_true; auto.
  (* 2. l2 > 0 *)  
  + destruct u1; subst.
  (* - 2.1. u1 = 0 *)
    * assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (l1 * Z.pos p1) (l1 * u2)) (Z.max (0 * Z.pos p1) (0 * u2)))%Z).
      { apply Z.le_trans with (m:=(0*u2)%Z); auto.
        apply le_max_rr; auto. }
      apply Zle_true_leb_true; auto.
  (* - 2.2. u1 > 0 *)
  * assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (l1 * Z.pos p1) (l1 * u2)) (Z.max (Z.pos p2 * Z.pos p1) (Z.pos p2 * u2)))%Z).
    { apply Z.le_trans with (m:=((Z.pos p2)*u2)%Z); auto.
      apply Z.le_trans with (m:=(0*u2)%Z); auto. 
      apply Zmult_le_compat_r; smack.
      apply le_max_rr; auto. }
    apply Zle_true_leb_true; auto.
  (* - 2.3. u1 < 0 *)
  (* v1*v2 <= u1*l2 *)
  * assert(HA3: ((Z.neg p)*(Z.pos p0) <= (Z.neg p2)*(Z.pos p1))%Z).
    (* v1*v2 <= u1*v2 *)
    { assert(HA3a: ((Z.neg p)*(Z.pos p0) <= (Z.neg p2)*(Z.pos p0))%Z).
      { apply Zmult_le_compat_r; auto. }
    (* u1*v2 <= u1*l2 *)
      assert(HA3b: ((Z.neg p2)*(Z.pos p0) <= (Z.neg p2)*(Z.pos p1))%Z).
      { apply Zmult_le_rev_l; smack. }
      apply Z.le_trans with (m:=(Z.neg p2 * Z.pos p0)%Z); auto. }
    assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (l1 * Z.pos p1) (l1 * u2)) (Z.max (Z.neg p2 * Z.pos p1) (Z.neg p2 * u2)))%Z).
    { apply Z.le_trans with (m:=((Z.neg p2)*(Z.pos p1))%Z); auto.
      apply le_max_rl; auto. }
    apply Zle_true_leb_true; auto.
  (* 3. l2 < 0 *)  
  (* v1*v2 <= l1*l2 *)
  + assert(HZ2: (Z.neg (p * p0) <= Z.max (Z.max (l1 * Z.neg p1) (l1 * u2)) (Z.max (u1 * Z.neg p1) (u1 * u2)))%Z).
    { apply Z.le_trans with (m:=(0)%Z); auto.
      apply Z.le_trans with (m:=(l1*Z.neg p1)%Z); auto.
      - apply Zmult_le_le; auto.
      - apply le_max_ll; auto. }
  apply Zle_true_leb_true; auto.
 - (* case 9: v1 < 0, v2 < 0 *)
  (* v1*v2 <= l1*l2 *)
   assert(HA1a: (l1 <= 0)%Z).
   {  apply Z.le_trans with (m:=Z.neg p); auto. 
      specialize (Zlt_neg_0 p); intro; smack. }
   assert(HA1b: (l2 <= 0)%Z).
   { apply Z.le_trans with (m:=Z.neg p0); auto. 
     specialize (Zlt_neg_0 p0); intro; smack. }
  (* v1*l2 <= l1*l2 *)
   assert (HA2: ((Z.neg p) * l2 <= l1 * l2)%Z).
   { apply Zmult_le_rev_r; auto. }
   (* v1*v2 <= v1*l2 *)
   assert (HA3: ((Z.neg p) * (Z.neg p0) <= (Z.neg p) * l2)%Z).
   { apply Zmult_le_rev_l; auto.
     specialize (Zlt_neg_0 p); intro; smack. }
  (* v1*v2 <= l1*l2 *)
   assert(HA4: (Z.neg p * Z.neg p0 <= l1 * l2)%Z).
   { apply Z.le_trans with (m:=(Z.neg p * l2)%Z); auto. }
   assert(HZ1: (Z.pos (p * p0) <= Z.max (Z.max (l1 * l2) (l1 * u2)) (Z.max (u1 * l2) (u1 * u2)))%Z).
   { apply Z.le_trans with (m:=(l1*l2)%Z); auto.
     apply le_max_ll; auto. }

   destruct u1; subst.
   (* 1. u1 = 0 *)
   + assert(HZ2: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (0 * l2) (0 * u2)) <= Z.pos (p * p0))%Z).
     { apply Z.le_trans with (m:=(0*l2)%Z); auto.
       apply le_min_rl; auto. }
     apply Zle_true_leb_true; auto.  
   (* 2. u1 > 0 *)
   (* u1*l2 <= 0 <= v1*v2 *)
   + assert(HZ2: (Z.min (Z.min (l1 * l2) (l1 * u2)) (Z.min (Z.pos p1 * l2) (Z.pos p1 * u2)) <= Z.pos (p * p0))%Z).
     { apply Z.le_trans with (m:=((Z.pos p1)*l2)%Z); auto.
       apply le_min_rl; auto.
       (* u1*l2 <= v1*v2 *)
       apply Z.le_trans with (m:=0%Z); auto.
       (* u1*l2 <= 0 *)
       apply Zmult_le_ge_l; auto. }
     (* 0 <= v1*v2 *)
     apply Zle_true_leb_true; auto.
   (* 3. u1 < 0 *)    
   + destruct u2; subst.
     (* - 3.1 u2 = 0 *)
     * assert(HZ2: (Z.min (Z.min (l1 * l2) (l1 * 0)) (Z.min (Z.neg p1 * l2) (Z.neg p1 * 0)) <= Z.pos (p * p0))%Z).
       { apply Z.le_trans with (m:=(l1 * 0)%Z); auto.
         apply le_min_lr; auto.
         rewrite (Z.mul_comm l1 0%Z). smack. }
       apply Zle_true_leb_true; auto.  
     (* - 3.2 u2 > 0 *)
     (* u1*u2 <= 0 <= v1*v2 *)
     * assert(HZ2: (Z.min (Z.min (l1 * l2) (l1 * Z.pos p2)) (Z.min (Z.neg p1 * l2) (Z.neg p1 * Z.pos p2)) <= Z.pos (p * p0))%Z).
       { apply Z.le_trans with (m:=((Z.neg p1) * (Z.pos p2))%Z); auto.
         apply le_min_rr; auto. }
       apply Zle_true_leb_true; auto.    
     (* - 3.3 u2 < 0 *)
     (* u1*u2 <= v1*v2 *)
     (* step 1: u1*u2 <= v1*u2 *)
     * assert(HA_1: ((Z.neg p1) * (Z.neg p2) <= (Z.neg p) * (Z.neg p2))%Z).
       { apply Zmult_le_rev_r; auto.
         specialize (Zlt_neg_0 p2); intro; smack. }
       (* step 2: v1*u2 <= v1*v2 *)
       assert(HA_2: ((Z.neg p) * (Z.neg p2) <= (Z.neg p) * (Z.neg p0))%Z).
       { apply Zmult_le_rev_l; auto.
         specialize (Zlt_neg_0 p); intro; smack. }
       (* final: u1*u2 <= v1*v2 *)
       assert(HA_3: ((Z.neg p1) * (Z.neg p2) <= (Z.neg p) * (Z.neg p0))%Z).
       { apply Z.le_trans with (m:=((Z.neg p) * (Z.neg p2))%Z); auto. }

       assert(HZ2: (Z.min (Z.min (l1 * l2) (l1 * Z.neg p2)) (Z.min (Z.neg p1 * l2) (Z.neg p1 * Z.neg p2)) <= 
                    Z.pos (p * p0))%Z).
       { apply Z.le_trans with (m:=((Z.neg p1) * (Z.neg p2))%Z); auto.
         apply le_min_rr; auto. }
       apply Zle_true_leb_true; auto.
Qed.

Ltac apply_multiply_in_bound := 
  match goal with
  | [H1: in_bound ?v1 (Interval ?l1 ?u1) true,
     H2: in_bound ?v2 (Interval ?l2 ?u2) true |- _] =>
      specialize (multiply_in_bound _ _ _ _ _ _ H1 H2); 
      let HZ := fresh "HZ" in intro HZ
  end.
  
(** * Divide Interval Correctness *)
  
Lemma divide_in_bound: forall v1 v2 l1 l2 u1 u2 l u,
  in_bound v1 (Interval l1 u1) true ->
  in_bound v2 (Interval l2 u2) true -> 
  Zeq_bool v2 0 = false ->
  divide_min_max_f l1 u1 l2 u2 = (l, u) ->
  in_bound (Z.quot v1 v2) (Interval l u) true.
Proof.
  intros.
  repeat progress match goal with
  | [H: in_bound ?v (Interval ?l ?u) true |- _] => inversion H; subst; clear H
  end;
  repeat progress apply_Zleb_true_le_true;
  constructor; auto.
  clear HZa HZb HZa0 HZb0.
  unfold divide_min_max_f in H2.
  remember ((u2 <=? -1)%Z) as u2b.
  destruct u2b; subst.
  symmetry in Hequ2b.
  assert(Hu2bT: (u2 <= -1)%Z).
    apply Zleb_le; auto.
  apply_Zle_n1_0.
 - (* 1. [l2, u2] <= -1 *)
  assert(HA1: (v2 < 0)%Z).
    apply Z.le_lt_trans with (m:=u2); auto.
  remember ((u1 <=? -1)%Z) as u1b.
  destruct u1b; subst.
  assert(Hu1bT: (u1 <= -1)%Z).
    apply Zleb_le; auto.
  apply_Zle_n1_0.
  (* - case 1.1: [l2, u2] <= -1, [l1, u1] <= -1 *)
  inversion H2; subst.  
  assert(HZ1: (u1 ÷ l2 <= v1 ÷ v2)%Z).
    (* u1/l2 <= [u1/v2] <= v1/v2 *)
    apply Z.le_trans with (m:=(u1 ÷ v2)%Z); auto.
    apply Zquot_le_compat_n_n; auto.
    apply Zquot_antitone; auto.
    apply Zlt_le; auto.
  assert(HZ2: (v1 ÷ v2 <= l1 ÷ u2)%Z).
    (* v1/v2 <= [l1/v2] <= l1/u2 *)
    apply Z.le_trans with (m:=(l1 ÷ v2)%Z); auto.
    apply Zquot_antitone; auto.
    apply Zlt_le; auto.
    apply Zquot_le_compat_n_n; auto.
    apply Z.le_trans with (m:=u1); auto.
    apply Z.le_trans with (m:=v1); auto.
  apply Zle_true_leb_true; auto.
  
  remember ((1 <=? l1)%Z) as l1b.   
  destruct l1b; subst. 
  symmetry in Heql1b.
  assert(Hl1bT: (1 <= l1)%Z).
    apply Zleb_le; auto.
  apply_Zge_p1_0.
  (* - case 1.2: [l2, u2] <= -1, 1 <= [l1, u1] *)  
  inversion H2; subst.
  assert(HZ1: (u1 ÷ u2 <= v1 ÷ v2)%Z).
    (* u1/u2 <= [u1/v2] <= v1/v2 *)  
    apply Z.le_trans with (m:=(u1 ÷ v2)%Z); auto.
    apply Zquot_le_compat_p_n; auto.
      apply Z.le_trans with (m:=l1); auto.
      apply Z.le_trans with (m:=v1); auto.
    apply Zquot_antitone; auto.
      apply Zlt_le; auto.
  assert(HZ2: (v1 ÷ v2 <= l1 ÷ l2)%Z).
    (* v1/v2 <= [v1/l2] <= l1/l2 *)  
    apply Z.le_trans with (m:=(v1 ÷ l2)%Z); auto.
    apply Zquot_le_compat_p_n; auto.
      apply Z.le_trans with (m:=l1); auto.
    apply Zquot_antitone; auto.
      apply Z.le_trans with (m:=u2); auto.
      apply Z.le_trans with (m:=v2); auto.
  apply Zle_true_leb_true; auto.
  (* - case 1.3: [l2, u2] <= -1, 0 in [l1, u1] *)  
  inversion H2; subst.
  assert(HZ12: (u1 ÷ u2 <= v1 ÷ v2)%Z /\ (v1 ÷ v2 <= l1 ÷ u2)%Z).
    (* u1/u2 <= [u1/v2] <= v1/v2;  v1/v2 <= [v1/u2] <= l1/u2*)
    remember (0 <=? v1)%Z as v1b.
    destruct v1b;
    symmetry in Heqv1b.
    (* 1.3.1. 0 <= v1 *)
    assert(Hv1bT: (0 <= v1)%Z).
      apply Zleb_le; auto.
    split.
    (* - *)
    apply Z.le_trans with (m:=(u1 ÷ v2)%Z); auto.
    apply Zquot_le_compat_p_n; auto.
      apply Z.le_trans with (m:=v1); auto.
    apply Zquot_antitone; auto.
      apply Zlt_le; auto.
    (* - *)
    (* v1/v2 <= 0 <= l1/u2*)
    apply Z.le_trans with (m:=0%Z); auto.
    apply Zquot_p_n_n; auto.
    apply Zquot_n_n_p; auto.
      symmetry in Heql1b.
      specialize (Le_False_Lt _ _ Heql1b); intro HZ2.
      replace (0%Z) with (Z.pred 1); auto.
      apply Zlt_le_pred_r; auto.
    (* 1.3.2. v1 <= 0 *)
    assert(Hv1bT: (v1 <= 0)%Z).
      specialize (Le_False_Lt _ _ Heqv1b); intro.
      apply Zlt_le; auto.
    split.
    (* - *)
    (* u1/u2 <= 0 <= v1/v2 *)
    apply Z.le_trans with (m:=0%Z); auto.
    apply Zquot_p_n_n; auto.
      symmetry in Hequ1b.
      specialize (Le_False_Lt _ _ Hequ1b); intro HZ2.
      replace (0%Z) with (Z.succ (-1)%Z); auto.
      apply Zlt_le_succ_l; auto.    
    apply Zquot_n_n_p; auto.
    (* - *)
    (* v1/v2 <= [v1/u2] <= l1/u2*)
    apply Z.le_trans with (m:=(v1 ÷ u2)%Z); auto.
    apply Zquot_le_compat_n_n; auto.
    apply Zquot_antitone; auto.
  destruct HZ12 as [HZ1 HZ2].
  apply Zle_true_leb_true; auto.
 - (* 2. 1 <= [l2, u2] *)
  remember ((1 <=? l2)%Z) as l2b.
  destruct l2b; subst.
  symmetry in Heql2b.
  assert(Hl2bT: (1 <= l2)%Z).
    apply Zleb_le; auto.
  apply_Zge_p1_0.
  
  remember ((u1 <=? -1)%Z) as u1b.
  destruct u1b; subst.
  symmetry in Hequ1b.
  assert(Hu1bT: (u1 <= -1)%Z).
    apply Zleb_le; auto.
  apply_Zle_n1_0.

  (* - case 2.1: 1 <= [l2, u2], [l1, u1] <= -1 *)
  inversion H2; subst.  
  assert(HZ1: (l1 ÷ l2 <= v1 ÷ v2)%Z).
    (* l1/l2 <= [l1/v2] <= v1/v2 *)
    apply Z.le_trans with (m:=(l1 ÷ v2)%Z); auto.
    apply Zquot_le_compat_n_p; auto.
      apply Z.le_trans with (m:=u1); auto.
      apply Z.le_trans with (m:=v1); auto.
    apply Z_quot_monotone; auto.
      apply Z.le_trans with (m:=l2); auto.
  assert(HZ2: (v1 ÷ v2 <= u1 ÷ u2)%Z).
    (* v1/v2 <= [v1/u2] <= u1/u2 *)
    apply Z.le_trans with (m:=(v1 ÷ u2)%Z); auto.
    apply Zquot_le_compat_n_p; auto.
      apply Z.le_trans with (m:=u1); auto.
      apply Z.lt_le_trans with (m:=l2); auto.
    apply Z_quot_monotone; auto.
      apply Z.le_trans with (m:=l2); auto.    
      apply Z.le_trans with (m:=v2); auto.
  apply Zle_true_leb_true; auto.
  
  remember ((1 <=? l1)%Z) as l1b.
  destruct l1b; subst.
  symmetry in Heql1b.
  assert(Hl1bT: (1 <= l1)%Z).
    apply Zleb_le; auto.
  apply_Zge_p1_0.  

  (* - case 2.2: 1 <= [l2, u2], 1 <= [l1, u1] *)
  inversion H2; subst.  
  assert(HZ1: (l1 ÷ u2 <= v1 ÷ v2)%Z).
    (* l1/u2 <= [l1/v2] <= v1/v2 *)
    apply Z.le_trans with (m:=(l1 ÷ v2)%Z); auto.
    apply Zquot_le_compat_p_p; auto.
      apply Z.lt_le_trans with (m:=l2); auto.
    apply Z_quot_monotone; auto.
      apply Z.le_trans with (m:=l2); auto.
  assert(HZ2: (v1 ÷ v2 <= u1 ÷ l2)%Z).
    (* v1/v2 <= [v1/l2] <= u1/l2 *)
    apply Z.le_trans with (m:=(v1 ÷ l2)%Z); auto.
    apply Zquot_le_compat_p_p; auto.
      apply Z.le_trans with (m:=l1); auto.
    apply Z_quot_monotone; auto.
  apply Zle_true_leb_true; auto.
  
  (* - case 2.3: 1 <= [l2, u2], 0 in [l1, u1] *)
  inversion H2; subst.
  assert(HA1: (l1 <= 0)%Z).
    symmetry in Heql1b.
    specialize (Le_False_Lt _ _ Heql1b); intro HZ2.
    replace (0%Z) with (Z.pred 1); auto.
    apply Zlt_le_pred_r; auto.
  assert(HZ12: (l1 ÷ l2 <= v1 ÷ v2)%Z /\ (v1 ÷ v2 <= u1 ÷ l2)%Z).
    (* l1/l2 <= [l1/v2] <= v1/v2;  v1/v2 <= [v1/l2] <= u1/l2*)
    remember (0 <=? v1)%Z as v1b.
    destruct v1b;
    symmetry in Heqv1b.
    (* 2.3.1. 0 <= v1 *)
    assert(Hv1bT: (0 <= v1)%Z).
      apply Zleb_le; auto.
    split.
    (* - *)
    (* l1/l2 <= [l1/v2] <= v1/v2 *)
    apply Z.le_trans with (m:=(l1 ÷ v2)%Z); auto.
    apply Zquot_le_compat_n_p; auto.
    apply Z_quot_monotone; auto.
      apply Z.le_trans with (m:=l2%Z); auto.
    (* - *)
    (* v1/v2 <= [v1/l2] <= u1/l2*)
    apply Z.le_trans with (m:=(v1 ÷ l2)%Z); auto.
    apply Zquot_le_compat_p_p; auto.
    apply Z_quot_monotone; auto.
    (* 2.3.2. v1 <= 0 *)
    assert(Hv1bT: (v1 <= 0)%Z).
      specialize (Le_False_Lt _ _ Heqv1b); intro.
      apply Zlt_le; auto.
    split.
    (* - *)
    (* l1/l2 <= [l1/v2] <= v1/v2 *)
    apply Z.le_trans with (m:=(l1 ÷ v2)%Z); auto.
    apply Zquot_le_compat_n_p; auto.
    apply Z_quot_monotone; auto.
      apply Z.le_trans with (m:=l2%Z); auto.
    (* - *)
    (* v1/v2 <= 0 <= u1/l2*)
    apply Z.le_trans with (m:=0%Z); auto.
    apply Zquot_n_p_n; auto.
      apply Z.lt_le_trans with (m:=l2); auto.
    apply Zquot_p_p_p; auto.
      symmetry in Hequ1b.
      specialize (Le_False_Lt _ _ Hequ1b); intro HZ2.
      replace (0%Z) with (Z.succ (-1)%Z); auto.
      apply Zlt_le_succ_l; auto.    
  destruct HZ12 as [HZ1 HZ2].
  apply Zle_true_leb_true; auto.  
  
  (* - case 3: 0 in [l2, u2] *)

  remember ((u1 <=? -1)%Z) as u1b.
  destruct u1b; subst.
  symmetry in Hequ1b.
  assert(Hu1bT: (u1 <= -1)%Z).
    apply Zleb_le; auto.
  apply_Zle_n1_0.
  
  (* - case 3.1: 0 in [l2, u2], [l1, u1] <= -1 *)
  inversion H2; subst.
  (* assert(Hv1lt0: ) *)
  assert(HZ12: (l ÷ 1 <= v1 ÷ v2)%Z /\ (v1 ÷ v2 <= (Z.abs l))%Z).
    (* l1/1 <= [l1/v2] <= v1/v2, v1/v2 <= v1/1 <= (Z.abs l1) *)  
    remember (0 <=? v2)%Z as v2b.
    destruct v2b;
    symmetry in Heqv2b.
    (* 3.1.1. 0 <= v2 *)
    assert(Hv2bT: (0 <= v2)%Z).
      apply Zleb_le; auto.
    split.
    (* - *)
    (* l1/1 <= [l1/v2] <= v1/v2 *)
    apply Z.le_trans with (m:=(l ÷ v2)%Z); auto.
      specialize (Zle_lt_or_eq _ _ Hv2bT); intro HZ2.
      destruct HZ2; subst.
    apply Zquot_le_compat_n_p; smack.
    inversion H1.
    apply Z_quot_monotone; auto.
    (* - *)
    (* v1/v2 <= 0 <= (Z.abs l1) *) 
    apply Z.le_trans with (m:=0%Z); auto.
      apply Zquot_n_p_n; auto.
      apply Z.le_trans with (m:=u1%Z); auto.
      apply Zle_eq_e_l; auto.
      smack.
    (* 3.1.2. v2 <= 0 *)
    assert(Hv2bT: (v2 <= 0)%Z).
      specialize (Le_False_Lt _ _ Heqv2b); intro.
      apply Zlt_le; auto.
    split.
    (* - *)
    (* l1/1 <= 0 <= v1/v2 *)
    apply Z.le_trans with (m:=0%Z); auto.
      rewrite Z.quot_1_r.
      apply Z.le_trans with (m:=u1%Z); auto.
      apply Z.le_trans with (m:=v1%Z); auto.
    apply Zquot_n_n_p; auto.
      apply Z.le_trans with (m:=u1%Z); auto.
      apply Zle_eq_e_r; auto.
    (* - *)
    (* v1/v2 <= v1/(-1) <= (Z.abs l1)/(-1) *)
    assert(HA1: (l <= 0)%Z).
      apply Z.le_trans with (m:= u1%Z); auto.
      apply Z.le_trans with (m:= v1%Z); auto.
    rewrite Zabs_quot_neg1; auto.
    apply Z.le_trans with (m:= (v1 ÷ -1)%Z); auto.
      apply Zquot_le_compat_n_n; auto.
      apply Z.le_trans with (m:= u1%Z); auto.
      smack.
      apply Zlt_succ_le; auto. simpl.
      apply Zle_eq_e_r; auto.
    apply Zquot_antitone; smack.
  rewrite Z.quot_1_r in HZ12.
  destruct HZ12 as [HZ3 HZ4].
  apply Zle_true_leb_true; auto.


  remember ((1 <=? l1)%Z) as l1b.
  destruct l1b; subst.
  symmetry in Heql1b.
  assert(Hl1bT: (1 <= l1)%Z).
    apply Zleb_le; auto.
  apply_Zge_p1_0.
  
  (* - case 3.2: 0 in [l2, u2], 1 <= [l1, u1] *)
  inversion H2; subst.
  assert(HZ12: (-u <= v1 ÷ v2)%Z /\ (v1 ÷ v2 <= u)%Z).
    (* -u/1 <= [-u/v2] <= v1/v2, v1/v2 <= v1/1 <= u/1 *)  
    remember (0 <=? v2)%Z as v2b.
    destruct v2b;
    symmetry in Heqv2b.
    (* 3.1.1. 0 <= v2 *)
    assert(Hv2bT: (0 <= v2)%Z).
      apply Zleb_le; auto.
    split.
    (* - *)
    (* -u <= 0 <= v1/v2 *)
    apply Z.le_trans with (m:=0%Z); auto.
      replace 0%Z with (-0)%Z; auto.
      apply Le_Neg_Ge; auto.
      apply Z.le_trans with (m:= l1%Z); auto.
      apply Z.le_trans with (m:= v1%Z); auto.
      apply Zquot_p_p_p; auto.
      apply Z.le_trans with (m:= l1%Z); auto.
      apply Zle_eq_e_l; auto.
    (* - *)
    (* v1/v2 <= v1/1 <= u1/1 *) 
    apply Z.le_trans with (m:=(v1 ÷ 1)%Z); auto.
      apply Zquot_le_compat_p_p; auto.
      apply Z.le_trans with (m:= l1%Z); auto.
      smack.
      replace 1%Z with (Z.succ 0); auto.
      apply Zlt_le_succ_l; auto.
      apply Zle_eq_e_l; auto.
      replace u with (u ÷ 1)%Z; auto.
      apply Z_quot_monotone; auto. smack.
      smack.
    (* 3.1.2. v2 <= 0 *)
    assert(Hv2bT: (v2 <= 0)%Z).
      specialize (Le_False_Lt _ _ Heqv2b); intro.
      apply Zlt_le; auto.
    split.
    (* - *)
    (* u1/-1 <= u/v2 <= v1/v2 *)
    assert(HA1: (-u = (u ÷ -1))%Z).
      rewrite Zquot_n1_opp; auto.
    rewrite HA1. 
    apply Z.le_trans with (m:=(u ÷ v2)%Z); auto.
      apply Zquot_le_compat_p_n; auto.
      apply Z.le_trans with (m:= l1%Z); auto.
      apply Z.le_trans with (m:= v1%Z); auto.
      smack.
      replace (-1)%Z with (Z.pred 0); auto.
      apply Zlt_le_pred_r; auto.
      apply Zle_eq_e_r; auto.
      apply Zquot_antitone; auto.
    (* - *)
    (* v1/v2 <= 0 <= u *)
    apply Z.le_trans with (m:= 0%Z); auto.
      apply Zquot_p_n_n; auto.
      apply Z.le_trans with (m:= l1%Z); auto.
      apply Zle_eq_e_r; auto.
      apply Z.le_trans with (m:= l1%Z); auto.
      apply Z.le_trans with (m:= v1%Z); auto.
  destruct HZ12 as [HZ3 HZ4].
  apply Zle_true_leb_true; auto.

  (* - case 3.3: 0 in [l2, u2], 0 in [l1, u1] *)
  inversion H2; subst.
  assert(HZ12: (- max_abs_f l1 u1 <= v1 ÷ v2)%Z /\ (v1 ÷ v2 <= max_abs_f l1 u1)%Z).
    repeat progress match goal with
    | [H: false = (_ <=? _)%Z |- _] => 
        symmetry in H; specialize (Le_False_Lt _ _ H);
        let HZ := fresh "HZ" in intro HZ; clear H
    end.
    repeat progress match goal with
    | [H: (-1 < ?v)%Z |- _] =>
        specialize (Zlt_le_succ_l _ _ H); 
        let HZ := fresh "HZ" in intro HZ; simpl in HZ; clear H
    | [H: (?v < 1)%Z |- _] => 
        specialize (Zlt_le_pred_r _ _ H);
        let HZ := fresh "HZ" in intro HZ; simpl in HZ; clear H
    end.

    remember (0 <=? v1)%Z as v1b.
    destruct v1b;
    symmetry in Heqv1b.
    (* 3.3.1. 0 <= v1 *)
    assert(Hv1bT: (0 <= v1)%Z).
      apply Zleb_le; auto.
      split.
    (* - *)
    (* - max_abs_f l1 u1 <= v1 ÷ v2)%Z *)
    destruct v2.
    (* 3.3.1.1: 0 <= v1, v2 = 0: conflict *)
    inversion H1.
    (* 3.3.1.2: 0 <= v1, v2 > 0 *)
    apply Z.le_trans with (m:=0%Z).
      apply max_abs_f_opp_le0; auto.
      apply Zquot_p_p_p; smack.
    (* 3.3.1.3: 0 <= v1, v2 < 0 *)
    apply Z.le_trans with (m:=(v1 ÷ (-1))%Z).    
      apply Zquot_n1_interval; auto.
      apply Zquot_le_compat_p_n; auto.
      smack.
      replace (-1)%Z with (Z.pred 0); auto.
      apply Zlt_le_pred_r; auto.
      apply Zlt_neg_0.
    (* - *)
    (* (v1 ÷ v2 <= max_abs_f l1 u1)%Z *)
    destruct v2.
    (* 3.3.1.1: 0 <= v1, v2 = 0: conflict *)
    inversion H1.
    (* 3.3.1.2: 0 <= v1, v2 > 0 *)
    apply Z.le_trans with (m:=(v1 ÷ 1)%Z).
      apply Zquot_le_compat_p_p; auto.
      smack.
      replace 1%Z with (Z.succ 0); auto.
      apply Zlt_le_succ_l; smack.
      apply Zquot_p1_interval; auto.
    (* 3.3.1.3: 0 <= v1, v2 < 0 *)
    apply Z.le_trans with (m:=0%Z).
      apply Zquot_p_n_n; auto.
      apply Zlt_neg_0; auto.
      apply max_abs_f_ge0; auto.

    (* 3.3.2. v1 <= 0 *)
    assert(Hv1bT: (v1 <= 0)%Z).
      specialize (Le_False_Lt _ _ Heqv1b); intro.
      apply Zlt_le; auto.
    split.
    (* - *)
    (* - max_abs_f l1 u1 <= v1 ÷ v2)%Z *)
    destruct v2.
    (* 3.3.2.1: v1 <= 0, v2 = 0: conflict *)
    inversion H1.
    (* 3.3.2.2: v1 <= 0, v2 > 0 *)
    apply Z.le_trans with (m:=(v1 ÷ 1)%Z).    
      apply Zquot_p1_interval; auto.
      apply Zquot_le_compat_n_p; auto.
      smack.
      replace 1%Z with (Z.succ 0); auto.
      apply Zlt_le_succ_l; smack.
    (* 3.3.2.3: v1 <= 0, v2 < 0 *)
    apply Z.le_trans with (m:=0%Z).
      apply max_abs_f_opp_le0; auto.
      apply Zquot_n_n_p; auto.
      apply Zlt_neg_0; auto.
    (* - *)
    (* (v1 ÷ v2 <= max_abs_f l1 u1)%Z *)
    destruct v2.
    (* 3.3.2.1: v1 <= 0, v2 = 0: conflict *)
    inversion H1.
    (* 3.3.2.2: v1 <= 0, v2 > 0 *)
    apply Z.le_trans with (m:=0%Z).
      apply Zquot_n_p_n; smack.
      apply max_abs_f_ge0; auto.    
    (* 3.3.2.3: v1 <= 0, v2 < 0 *)
    apply Z.le_trans with (m:=(v1 ÷ -1)%Z).
      apply Zquot_le_compat_n_n; auto.
      smack.
      replace (-1)%Z with (Z.pred 0); auto.
      apply Zlt_le_pred_r; auto.
      apply Zlt_neg_0; auto.
      apply Zquot_n1_interval; auto.
  destruct HZ12 as [HZ3 HZ4].
  apply Zle_true_leb_true; auto.
Qed.

Ltac apply_divide_in_bound :=
  match goal with
  | [H1: in_bound ?v1 (Interval ?l1 ?u1) true,
     H2: in_bound ?v2 (Interval ?l2 ?u2) true,
     H3: Zeq_bool ?v2 0 = false,
     H4: divide_min_max_f ?l1 ?u1 ?l2 ?u2 = (?l, ?u) |- _] =>
      specialize (divide_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  | [H1: in_bound ?v1 (Interval ?l1 ?u1) true,
     H2: in_bound ?v2 (Interval ?l2 ?u2) true,
     H3: Zeq_bool ?v2 0 = false,
     H4: (?l, ?u) = divide_min_max_f ?l1 ?u1 ?l2 ?u2 |- _] =>
      symmetry in H4;
      specialize (divide_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intro HZ
  end.
  
