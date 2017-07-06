Require Import environment.
Require Import FunInd Morphisms Relations SetoidList.

(* Import STACK. *)

(* Functional Scheme update_ind := Induction for update Sort Prop. *)
(* Functional Scheme updates_ind := Induction for updates Sort Prop. *)
(* Functional Scheme fetch_ind := Induction for fetch Sort Prop. *)


Module STORE_PROP (V:ENTRY).
  Module ST := STORE(V).
  Include ST.
  (* Functional Scheme update_ind := Induction for ST.update Sort Prop. *)
(*   Functional Scheme updates_ind := Induction for ST.updates Sort Prop. *)
  Functional Scheme fetch_ind := Induction for fetch Sort Prop.

  (* The AST provided by gnat/sireum are supposed to have no two variables sharing
   the same name. This should imply that there are no duplication of name in stacks. *)
  (* intra-store *)
  Definition NoDup (s : state) := 
    forall nme lvl sto (sto' sto'':store),
      frameG nme s = Some (lvl,sto) ->
      cuts_to nme sto = (sto',sto'') ->
      resides nme (List.tl sto'') = false.

  (* extra-store *)
  Definition NoDup_G (s : state) := 
    forall nme lvl sto s' s'',
      frameG nme s = Some (lvl,sto) ->
      cut_until s lvl s' s'' ->
      resideG nme s'' = false.



(** levels in the global stack match exactly their nesting levels. *)
Inductive exact_levelG:  state -> Prop :=
  | exact_levelG_nil: exact_levelG nil
  | exact_levelG_cons: forall stk fr,
      exact_levelG stk -> exact_levelG ((List.length stk, fr)::stk).


  Ltac rename_hyp1 h th :=
    match th with
    | in_bound _ _ _ => fresh "h_inbound"
    | updates ?sto ?x _ = _ => fresh "heq_updates_" sto "_" x
    | updates ?sto ?x _ = _ => fresh "heq_updates_" sto
    | updates ?sto ?x _ = _ => fresh "heq_updates_" x
    | updates ?sto ?x _ = _ => fresh "heq_updates"
    | update ?frm ?x _ = _ => fresh "heq_update_" frm "_" x
    | update ?frm ?x _ = _ => fresh "heq_update_" frm
    | update ?frm ?x _ = _ => fresh "heq_update_" x
    | update ?frm ?x _ = _ => fresh "heq_update"
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" stk "_" x
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" stk
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" x
    | updateG ?stk ?x _ = _ => fresh "heq_updateG"
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG_" x "_" stk
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG_" stk
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG_" x
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG"
    | fetch ?x ?frm = _ => fresh "heq_fetch_" x "_" frm
    | fetch ?x ?frm = _ => fresh "heq_fetch_" frm
    | fetch ?x ?frm = _ => fresh "heq_fetch_" x
    | fetch ?x ?frm = _ => fresh "heq_fetch"
    | fetches ?x ?sto = _ => fresh "heq_fetches_" x "_" sto
    | fetches ?x ?sto = _ => fresh "heq_fetches_" sto
    | fetches ?x ?sto = _ => fresh "heq_fetches_" x
    | fetches ?x ?sto = _ => fresh "heq_fetches"
    | cut_until ?st ?s ?fr ?paramsprf ?args (RTE ?er) => fresh "h_cut_until_RE"
    | cut_until ?st ?s ?fr ?paramsprf ?args (OK ?fr') => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args ?fr' => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until_" fr
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until"
    | exact_levelG ?CE => fresh "h_exct_lvl_" CE
    | exact_levelG ?CE => fresh "h_exct_lvl"
    end.

(*   Ltac rename_hyp ::= rename_hyp1. *)

  Lemma updates_ok_none : forall sto x v, updates sto x v = None <-> fetches x sto = None.
  Proof.
    intros.
    split;intro.
    - functional induction (updates sto x v).
      + discriminate.
      + discriminate.
      + unfold id in *. (* scorie from libhyprenaming *)
        simpl.
        rewrite e0.
        apply IHo.
        assumption.
      + reflexivity.
    - functional induction (fetches x sto).
      + discriminate.
      + unfold id in *. (* scorie from libhyprenaming *)
        simpl.
        rewrite e0.
        rewrite IHo;auto.
      + reflexivity.
  Qed.


  (* the none version could be solved by functiona inversion but it is
     not applicable here due to a bug in Function with functors. *)
  Lemma update_ok_none : forall frm x v, update frm x v = None <-> fetch x frm = None.
  Proof.
    intros.
    split.
    - functional induction (ST.update frm x v);intro.
      + discriminate.
      + unfold fetch.
        eapply updates_ok_none;eauto.
    - unfold fetch, update.
      intro heq_fetches_x.
      rewrite <- updates_ok_none in heq_fetches_x.
      rewrite heq_fetches_x.
      reflexivity.
  Qed.



  (* the none version could be solved by functiona inversion but it is
   ot applicable here due to a bug in Function with functors. *)
  Lemma updateG_ok_none : forall stk x v, updateG stk x v = None <-> fetchG x stk = None.
  Proof.
    intros.
    split.
    - functional induction (updateG stk x v);intro.
      + discriminate.
      + discriminate.
      + unfold id in *.
        simpl.
        apply update_ok_none in e0.
        rewrite e0.
        auto.
      + reflexivity.
    - functional induction (fetchG x stk);intro.
      + discriminate.
      + simpl.
        rewrite IHo;auto.
        rewrite <- update_ok_none in e0;eauto.
        rewrite e0;auto.
      + reflexivity.
  Qed.

  Lemma fetches_ok: forall id sto v, fetches id sto = Some v -> resides id sto = true.
  Proof.
    intros id sto v.
    functional induction (fetches id sto);intros heq;try discriminate.
    - inversion heq.
      subst.
      cbn.
      rewrite e0.
      reflexivity.
    - cbn.
      rewrite e0.
      auto.
  Qed.

  Lemma fetches_resides: forall nme x,
      (exists res, fetches nme x = Some res) <->
      resides nme x = true.
  Proof.
    intros ? ?.
    functional induction (fetches nme x);cbn;intros;subst.
    - rewrite e0.
      split;eauto.
    - rewrite e0.
      assumption.
    - split;intros; try discriminate.
      decompose [ex] H.
      discriminate.
  Qed.


  Lemma fetches_ok_none_1: forall id sto, fetches id sto = None -> resides id sto = false.
  Proof.
    intros id sto.
    functional induction (fetches id sto);intros;try discriminate.
    - cbn.
      rewrite e0.
      auto.
    - cbn.
      reflexivity.
  Qed.

  Lemma fetches_ok_none_2: forall id sto, resides id sto = false -> fetches id sto = None.
  Proof.
    intros id sto.
    functional induction (fetches id sto);intros;try discriminate; try auto.
    - cbn in H.
      rewrite e0 in H.
      discriminate.
    - cbn in H.
      rewrite e0 in H.
      auto.
  Qed.

  Lemma fetches_ok_none: forall id sto, fetches id sto = None <-> resides id sto = false.
  Proof.
    intros id sto.
    split.
    - apply fetches_ok_none_1;auto.
    - apply fetches_ok_none_2;auto.
  Qed.

  Lemma fetch_ok: forall id sto v, fetch id sto = Some v -> reside id sto = true.
  Proof.
    unfold fetch, reside.
    intros.
    apply fetches_ok in H.
    assumption.
  Qed.

  Lemma fetch_ok_none: forall id sto, fetch id sto = None -> reside id sto = false.
  Proof.
    unfold fetch, reside.
    intros.
    apply fetches_ok_none in H.
    assumption.
  Qed.

  Lemma fetchG_ok_none: forall id sto, fetchG id sto = None -> resideG id sto = false.
  Proof.
    intros id sto.
    functional induction (fetchG id sto);intros;try discriminate.
    - simpl.
      destruct (reside id f) eqn:heq_reside.
      + apply fetch_ok_none in e0.
        rewrite e0 in heq_reside;discriminate.
      + auto.
    - reflexivity. 
  Qed.

  Lemma fetchG_ok: forall id sto v, fetchG id sto = Some v -> resideG id sto = true.
  Proof.
    intros id sto.
    functional induction (fetchG id sto);intros;try discriminate.
    - simpl.
      destruct (reside id f) eqn:heq_reside.
      + reflexivity.
      + apply fetch_ok in e0.
        rewrite e0 in heq_reside;discriminate.
    - simpl.
      destruct (reside id f) eqn:heq_reside.
      + reflexivity.
      + apply IHo in H.
        assumption.
  Qed.

  Lemma reside_false_fetch_none: forall (id : idnum) (fr : frame), reside id fr = false <-> fetch id fr = None.
  Proof.
    intros id fr. 
    unfold reside, fetch in *.
    symmetry.
    apply fetches_ok_none.
  Qed.

  Lemma fetch_ok_some: forall id sto,
      reside id sto = true -> 
      exists v, fetch id sto = Some v.
  Proof.
    intros id sto H. 
    destruct (fetch id sto) eqn:heq.
    - eauto.
    - apply reside_false_fetch_none in heq.
      now rewrite H in heq.
  Qed.

  Lemma updates_ok_same: forall sto id v sto',
      updates sto id v = Some sto'
      -> fetches id sto' = Some v.
  Proof.
    intros until v.
    functional induction (updates sto id v);intros;simpl in *;intros.
    - inversion H;simpl.
      rewrite e0.
      reflexivity.
    - inversion H;simpl.
      inversion e1;simpl.
      rewrite e0.
      apply IHo.
      assumption.
    - discriminate.
    - discriminate.
  Qed.

  Lemma updates_ok_same_orig: forall sto id v sto',
      updates sto id v = Some sto'
      -> exists v', fetches id sto = Some v'.
  Proof.
    intros sto id v.
    functional induction (updates sto id v);intros;simpl in *;intros.
    - rewrite e0.
      eauto.
    - rewrite e0.
      eapply IHo;eauto.
    - discriminate.
    - discriminate.
  Qed.

  Lemma updates_ok_same_resides: forall sto id v sto',
      updates sto id v = Some sto'
      -> resides id sto' = true.
  Proof.
    intros.
    eapply fetches_ok.
    eapply updates_ok_same;eauto.
  Qed.

  Lemma updates_ok_same_resides_orig: forall sto id v sto',
      updates sto id v = Some sto'
      -> resides id sto = true.
  Proof.
    intros.
    pose proof updates_ok_same_orig _ _ _ _ H.
    destruct H0.
    eapply fetches_ok;eauto.
  Qed.

  Lemma update_ok_same: forall frm id v frm',
      update frm id v = Some frm'
      -> fetch id frm' = Some v.
  Proof.
    intros until v.
    unfold fetch, update.
    intros.
    destruct (updates (store_of frm) id v) eqn:heq_upd.
    - inversion H;simpl.
      eapply updates_ok_same;eauto.
    - discriminate.
  Qed.


  Lemma update_ok_same_orig: forall frm id v frm',
      update frm id v = Some frm'
      -> exists v', fetch id frm = Some v'.
  Proof.
    intros until v.
    unfold fetch, update.
    intros.
    destruct (updates (store_of frm) id v) eqn:heq_upd.
    - inversion H;simpl.
      pose proof updates_ok_same_orig _ _ _ _ heq_upd.
      assumption.
    - discriminate.
  Qed.

  Lemma update_ok_same_reside: forall sto id v sto',
      update sto id v = Some sto'
      -> reside id sto' = true.
  Proof.
    intros.
    eapply fetch_ok.
    eapply update_ok_same;eauto.
  Qed.

  Lemma update_ok_same_reside_orig: forall sto id v sto',
      update sto id v = Some sto'
      -> reside id sto = true.
  Proof.
    intros.
    pose proof update_ok_same_orig _ _ _ _ H.
    destruct H0.
    eapply fetch_ok;eauto.
  Qed.

  Lemma updateG_ok_same: forall stk id v stk',
      updateG stk id v = Some stk'
      -> fetchG id stk' = Some v.
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros.
    - inversion H;simpl.
      apply update_ok_same in e0.
      rewrite e0.
      reflexivity.
    - inversion H;simpl.
      specialize (IHo _ e1).
      destruct (fetch x f) eqn:h.
      + apply update_ok_none in e0.
        rewrite e0 in h;discriminate.
      + assumption.
    - discriminate.
    - discriminate.
  Qed.

  Lemma updateG_ok_same_orig: forall stk id v stk',
      updateG stk id v = Some stk'
      -> exists v', fetchG id stk = Some v'.
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros;try discriminate.
    - inversion H;simpl.
      destruct (update_ok_same_orig _ _ _ _ e0).
      rewrite H0.
      eauto.
    - inversion H;simpl.
      apply update_ok_none in e0.
      rewrite e0.
      eapply IHo.
      eauto.
  Qed.

  Lemma updateG_ok_same_resideG: forall stk id v stk',
      updateG stk id v = Some stk'
      -> resideG id stk' = true.
  Proof.
    intros.
    eapply fetchG_ok.
    eapply updateG_ok_same.
    eauto.
  Qed.



  Lemma updates_ok_others: forall sto id v sto',
      updates sto id v = Some sto' ->
      forall id', id<>id' -> fetches id' sto = fetches id' sto'.
  Proof.
    intros until v.
    functional induction (updates sto id v);intros;simpl in *;intros.
    - inversion H;simpl.
      rewrite -> Nat.eqb_eq in e0.
      subst.
      apply Nat.neq_sym in H0.
      rewrite <- Nat.eqb_neq in H0.
      rewrite H0 in *.
      reflexivity.
    - inversion H;simpl.
      destruct (Nat.eq_dec id' y).
      + subst.
        rewrite Nat.eqb_refl in *.
        reflexivity.
      + rewrite <- Nat.eqb_neq in n.
        rewrite n in *.
        eapply IHo;eauto.
    - discriminate.
    - discriminate.
  Qed.

  Lemma update_ok_others: forall frm id v frm',
      update frm id v = Some frm' ->
      forall id', id<>id' -> fetch id' frm = fetch id' frm'.
  Proof.
    intros until v.
    functional induction (ST.update frm id v);destruct frm;simpl in *;intros.
    - inversion H;simpl.
      eapply updates_ok_others in e;eauto.
    - discriminate.
  Qed.

  Lemma update_ok_others_reside: forall frm id v frm',
      update frm id v = Some frm' ->
      forall id', id<>id' -> reside id' frm = reside id' frm'.
  Proof.
    intros ? ? ? ? heq_update_frm_id ? hneq. 
    pose proof update_ok_others _ _ _ _ heq_update_frm_id _ hneq.
    destruct (fetch id' frm) eqn:heq_fetch.
    - apply fetch_ok in heq_fetch.
      rewrite heq_fetch.
      symmetry in H.
      apply fetch_ok in H.
      rewrite H.
      reflexivity.
    - apply fetch_ok_none in heq_fetch.
      rewrite heq_fetch.
      symmetry in H.
      apply fetch_ok_none in H.
      rewrite H.
      reflexivity.
  Qed.

  Lemma updateG_ok_others: forall stk id v stk',
      updateG stk id v = Some stk' ->
      forall id', id<>id' -> fetchG id' stk = fetchG id' stk'.
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros.
    - inversion H;simpl.
       (destruct (fetch id' f) eqn:h).
      + erewrite update_ok_others in h;eauto.
        rewrite h.
        reflexivity.
      + erewrite update_ok_others in h;eauto.
        rewrite h.
        reflexivity.
    - inversion H;simpl.
       (destruct (fetch id' f) eqn:h).
      + reflexivity.
      + eapply IHo;eauto.
    - discriminate.
    - discriminate.
  Qed.


  Lemma updateG_ok_others_resideG: forall frm id v frm',
      updateG frm id v = Some frm' ->
      forall id', id<>id' -> resideG id' frm = resideG id' frm'.
  Proof.
    intros ? ? ? ? heq_updateG_frm_id ? hneq.
    pose proof updateG_ok_others _ _ _ _ heq_updateG_frm_id _ hneq.
    destruct (fetchG id' frm) eqn:heq_fetchG.
    - apply fetchG_ok in heq_fetchG.
      rewrite heq_fetchG.
      symmetry in H.
      apply fetchG_ok in H.
      rewrite H.
      reflexivity.
    - apply fetchG_ok_none in heq_fetchG.
      rewrite heq_fetchG.
      symmetry in H.
      apply fetchG_ok_none in H.
      rewrite H.
      reflexivity.
  Qed.


  Lemma updateG_ok_same_frameG: forall stk id v lvl sto stk',
      updateG stk id v = Some stk'
      -> frameG id stk = Some (lvl,sto)
      -> exists sto', frameG id stk' = Some (lvl,sto').
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros;try discriminate.
    - inversion H;simpl.
      pose proof update_ok_same_reside _ _ _ _ e0.
      pose proof update_ok_same_reside_orig _ _ _ _ e0.
      rewrite H1.
      rewrite H3 in H0.
      inversion H0;subst.
      unfold update in e0.
      cbn in *.
      destruct (updates sto x v) eqn:heq.
      + eauto.
      + discriminate.
    - inversion H;simpl.
      rewrite update_ok_none in e0.
      apply fetch_ok_none in e0.
      rewrite e0.
      rewrite e0 in H0.
      eauto.
  Qed.

  Lemma updateG_ok_same_frameG_orig: forall stk id v lvl sto stk',
      updateG stk id v = Some stk'
      -> frameG id stk' = Some (lvl,sto)
      -> exists sto', frameG id stk = Some (lvl,sto').
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros;try discriminate.
    - inversion H;simpl;subst.
      pose proof update_ok_same_reside _ _ _ _ e0.
      pose proof update_ok_same_reside_orig _ _ _ _ e0.
      simpl in H0.
      rewrite H1 in H0.
      rewrite H2.
      inversion H0.
      unfold update in e0.
      cbn in *.
      destruct (updates (store_of f) x v) eqn:heq.
      + destruct f;simpl in *.
        subst;inversion e0.
        eauto.
      + discriminate.
    - inversion H;simpl;subst.
      simpl in H0.
      rewrite update_ok_none in e0.
      apply fetch_ok_none in e0.
      rewrite e0.
      rewrite e0 in H0.
      eapply IHo; eauto.
  Qed.


  Lemma resideG_false_fetchG_none: forall (id : idnum) (sto : state), resideG id sto = false -> fetchG id sto = None.
  Proof.
    intros id sto.
    functional induction (resideG id sto);try now intros; discriminate.
    - intros h_resideG. 
      cbn.
      apply reside_false_fetch_none in e0.
      rewrite e0.
      auto.
    - intros;cbn.
      reflexivity.
  Qed.

  Lemma fetchG_ok_none_iff: forall sto id, fetchG id sto = None <-> resideG id sto = false.
  Proof.
    intros id sto.
    split;intros.
    - apply fetchG_ok_none;assumption.
    - apply resideG_false_fetchG_none;assumption.
  Qed.

  Lemma frameG_resideG_1: forall l nme, (exists x, frameG nme l = Some x) -> resideG nme l = true.
  Proof.
    intros l nme. 
    functional induction frameG nme l.
    - intros [x heq ].
      inversion heq;subst. clear heq.
      cbn in *.
      rewrite e0;auto.
    - intros [x heq ].
      cbn in *.
      rewrite e0.
      apply IHo.
      eauto.
    - intros  [x heq ].
      discriminate.
  Qed.


  Lemma frameG_resideG_2: forall l nme, resideG nme l = true -> exists x, frameG nme l = Some x.
  Proof.
    intros l nme. 
    functional induction resideG nme l.
    - intros _.
      cbn.
      rewrite e0;eauto.
    - intros h_eq.
      cbn in *.
      rewrite e0.
      eapply IHb.
      eauto.
    - intros abs. 
      discriminate.
  Qed.

  Lemma frameG_resideG: forall l nme, resideG nme l = true <-> exists x, frameG nme l = Some x.
  Proof.
    intros l nme. 
    split;intro h.
    - apply frameG_resideG_2;auto.
    - apply frameG_resideG_1;auto.
  Qed.


  Lemma fetchG_ok_some: forall id sto,
      resideG id sto = true -> 
      exists v, fetchG id sto = Some v.
  Proof.
    intros id sto H. 
    destruct (fetchG id sto) eqn:heq.
    - eauto.
    - apply fetchG_ok_none_iff in heq.
      now rewrite H in heq.
  Qed.

  
  Lemma cuts_to_decomp: forall nme sto sto' sto'',
      cuts_to nme sto = (sto', sto'')
      -> sto = sto'++sto''.
  Proof.
    intros nme sto. 
    functional induction cuts_to nme sto ;simpl.

    - intros sto' sto'' heq.
      inversion heq.
      reflexivity.
    - intros sto' sto'' heq.
      inversion heq; clear heq.
      simpl. subst.
      erewrite IHp;eauto.
    - intros sto' sto'' heq. 
      inversion heq;auto.
  Qed.

  Lemma cuts_to_snd: forall nme sto sto' sto'',
      cuts_to nme sto = (sto', sto'')
      -> sto'' = nil \/ exists x sto''', sto'' = (nme,x)::sto'''.
  Proof.
    intros nme sto. 
    functional induction cuts_to nme sto;simpl.
    - intros sto' sto'' H.
      inversion H.
      right.
      exists v, s'.
      rewrite Nat.eqb_eq in e0.
      subst;auto.
    - intros sto' sto'' H.
      inversion H; clear H.
      subst.
      eapply IHp;eauto.
    - intros sto' sto'' heq.
      inversion heq;auto.
  Qed.

  Lemma cuts_to_fst: forall nme sto sto' sto'',
      cuts_to nme sto = (sto', sto'')
      -> resides nme sto' = false.
  Proof.
    intros nme sto. 
    functional induction cuts_to nme sto;simpl.
    - intros sto' sto'' heq.
      inversion heq.
      reflexivity.
    - intros sto' sto'' heq.
      inversion heq; clear heq.
      simpl.
      rewrite e0.
      eapply IHp;eauto.
    - intros sto' sto'' heq.
      inversion heq;subst;auto.
  Qed.

  Lemma cuts_to_snd_reside: forall nme sto sto' sto'',
      resides nme sto = true
      -> cuts_to nme sto = (sto', sto'')
      -> exists x sto''', sto'' = (nme,x)::sto'''.
  Proof.
    intros nme sto sto' sto'' heq heq0.
    pose proof @cuts_to_snd _ _ _ _ heq0 as h_or.
    destruct h_or.
    - subst.
      pose proof cuts_to_fst _ _ _ _ heq0 as heq_bool_false.
      pose proof cuts_to_decomp _ _ _ _ heq0.
      subst.
      rewrite app_nil_r in *.
      rewrite heq_bool_false in heq. 
      discriminate.
    - inversion heq;auto.
  Qed.

  Lemma frameG_resides: forall nme s lvl sto, frameG nme s = Some (lvl, sto) ->  resides nme sto = true.
  Proof.
    intros nme s.
    functional induction frameG nme s.
    - intros lvl sto H. 
      inversion H.
      subst.
      assumption.
    - intros lvl sto H. 
      eapply IHo;eauto.
    - intros lvl sto H. 
      inversion H.
  Qed.


  Lemma reside_true_fetch_Some: forall id sto,
      reside id sto = true -> 
      exists x, fetch id sto = Some x.
  Proof.
    destruct sto.
    induction s0;intros H.
    - cbn in H. discriminate.
    - unfold reside in H.
      simpl store_of in H.
      functional inversion H;subst.
      + exists v.
        cbn in H |- *.
        now rewrite H3 in *|-*.
      + destruct IHs0;auto.
        exists x.
        cbn.
        now rewrite H4.
  Qed.

  Lemma resideG_true_fetchG_Some: forall id sto,
      resideG id sto = true -> 
      exists x, fetchG id sto = Some x.
  Proof.
    intros until 0.
    induction sto.
    - simpl.
      intro abs; discriminate.
    - intro heq_resideG.
      functional inversion heq_resideG;subst.
      + apply reside_true_fetch_Some in H2.
        destruct H2.
        exists x.
        cbn in * |- *.
        now rewrite H in *|-*.
      + destruct IHsto;auto.
        exists x.
        cbn.
        apply reside_false_fetch_none in H3.
        now rewrite H3.
  Qed.

  Lemma fetchG_Some_frameG_Some: forall id s x,
      fetchG id s = Some x ->
      exists lvl fr, frameG id s = Some (lvl,fr).
  Proof.
    intros id s.
    functional induction fetchG id s;intros.
    - inversion H;subst.
      cbn.
      erewrite fetch_ok;eauto.
      destruct f;eauto.
    - specialize IHo with (1:=H).
      destruct IHo as [x0 H0 ].
      destruct H0 as [x1 H1 ].
      exists x0, x1.
      cbn.
      erewrite fetch_ok_none;eauto.
    - discriminate.
  Qed.


  Lemma exact_levelG_frameG_lt_lgth: forall s,
      exact_levelG s -> 
      forall nme lvl sto ,
        frameG nme s = Some (lvl, sto) ->
        (lvl < Datatypes.length s)%nat.
  Proof.
    induction 1.
    - intros nme lvl sto heq_frameG.
      cbn in heq_frameG.
      discriminate.
    - rename H into h_exct_lvl.
      intros nme lvl sto heq_frameG. 
      cbn.
      functional inversion heq_frameG;subst;auto with arith.
      assert (lvl < length stk).
      { eapply IHexact_levelG;eauto. }
      auto with arith.
  Qed.


  Lemma exact_lvl_lvl_of_top: forall l,
      exact_levelG l ->
      forall n, level_of_top l = Some n ->
                S n = Datatypes.length l.
  Proof.
    induction 1;simpl; intros n H0.
    - cbv in H0.
      discriminate.
    - unfold level_of_top in H0.
      simpl in H0.
      now inversion H0.
  Qed.

  Lemma exact_levelG_frameG_le_top:
    forall s lvl sto,
      exact_levelG ((lvl,sto)::s)
      -> forall nme lvl' sto',
        frameG nme ((lvl,sto)::s) = Some (lvl', sto')
        -> (lvl' <= lvl)%nat.
  Proof.
    intros s lvl sto h_exct_lvl nme lvl' sto' h_frameG.
    inversion h_exct_lvl;subst.
    rename H0 into h_exct_lvl_s.
    specialize exact_levelG_frameG_lt_lgth with (1:=h_exct_lvl) (2:=h_frameG);intro h.
    simpl in h.
    auto with arith.
  Qed.

  Lemma exact_levelG_sublist: forall x CE,
      exact_levelG (x::CE)
      -> exact_levelG CE.
  Proof.
    intros x CE H.
    inversion H;cbn in *;auto.
  Qed.

Lemma cut_until_exact_levelG:
  forall s pb_lvl s' s'' ,
    exact_levelG s ->
    (pb_lvl <= Datatypes.length s)%nat ->
    cut_until s pb_lvl s'  s'' ->
    pb_lvl = Datatypes.length s''.
Proof.
  intros s pb_lvl s' s'' h_exactlvlG.
  revert pb_lvl s' s''.
  induction h_exactlvlG;simpl;intros ? ? ? h_lt h_cut.
  - inversion h_cut;subst;simpl in *.
    omega.
  - inversion h_lt;subst.
    + clear h_lt.        
      inversion h_cut;subst.
      * reflexivity.
      * simpl in *.
        exfalso;omega.
    + simpl in *.
      inversion h_cut;subst;simpl in *.
      * exfalso;omega.
      * eapply IHh_exactlvlG;eauto.
Qed.

Lemma cut_until_exact_levelG_2:
  forall s pb_lvl s' s'' ,
    exact_levelG s ->
    (pb_lvl > Datatypes.length s)%nat ->
    cut_until s pb_lvl s'  s'' ->
    Datatypes.length s = Datatypes.length s''.
Proof.
  intros s pb_lvl s' s'' h_exactlvlG.
  destruct h_exactlvlG;simpl.
  - intros H h_cut. inversion h_cut.
    reflexivity.
  - intros H h_cut. inversion h_cut;simpl in *;subst.
    + reflexivity.
    + exfalso;omega.
Qed.

Lemma exact_lvl_level_of_top:
  forall l',
    exact_levelG  l' ->
    forall nme lvl_nme fr_nme,
      frameG nme l' = Some (lvl_nme, fr_nme) -> 
      exists top,
        level_of_top l' = Some top /\
        (lvl_nme <= top)%nat.
Proof.
  intros l' h_exct_lvl_l'.
  induction h_exct_lvl_l';intros;subst.
  - discriminate.
  - cbn in H.
    destruct (resides nme fr) eqn:heq.
    + inversion H.
      cbn.
      eauto with arith.
    + cbn.
      exists (Datatypes.length stk);split;auto.
      edestruct IHh_exct_lvl_l';eauto.
      destruct H0 as [h h'].
      destruct stk;cbn in h;try discriminate.
      destruct f.
      inversion h.
      cbn.
      inversion h_exct_lvl_l';subst.
      auto with arith.
Qed.

Lemma nodup_G_cons :
  forall a l nme ,
    exact_levelG (a::l) ->
    NoDup_G (a::l) -> resideG nme l = true -> reside nme a = false.
Proof.
  intros a l nme h__exact h_nodupG h_reside. 
  destruct (reside nme a) eqn:?;auto.
  specialize (h_nodupG nme (level_of a) (store_of a) (a::nil) l).
  cbn in h_nodupG.
  rewrite h_reside,Heqb in h_nodupG.
  assert (Some a = Some (level_of a, store_of a)).
  { destruct a;auto. }
  specialize (h_nodupG H).
  clear H.
  assert (cut_until (a :: l) (level_of a) (a::nil) l).
  { constructor 3.
    - omega.
    - destruct l.
      + constructor 1.
      + constructor 2.
        inversion h__exact.
        inversion H0.
        subst.
        cbn.
        omega.  }
  specialize (h_nodupG H).
  discriminate.
Qed.


Lemma nodup_G_cons_2 :
  forall a l nme ,
    exact_levelG (a::l) ->
    NoDup_G (a::l) -> reside nme a = true -> resideG nme l = false.
Proof.
  intros a l nme h__exact h_nodupG h_reside. 
  destruct (resideG nme l) eqn:?;try discriminate;auto.

  specialize (h_nodupG nme (level_of a) (store_of a) (a::nil) l).
  cbn in h_nodupG.
  rewrite h_reside,Heqb in h_nodupG.
  assert (Some a = Some (level_of a, store_of a)).
  { destruct a;auto. }
  specialize (h_nodupG H).
  clear H.
  assert (cut_until (a :: l) (level_of a) (a::nil) l).
  { constructor 3.
    - omega.
    - destruct l.
      + constructor 1.
      + constructor 2.
        inversion h__exact.
        inversion H0.
        subst.
        cbn.
        omega.  }
  specialize (h_nodupG H).
  discriminate.
Qed.

Lemma stack_CE_NoDup_cons: forall l',
    exact_levelG l' ->
    NoDup_G l' ->
    NoDup l' ->
    forall l a,
      l'= a::l ->
      NoDup l.
Proof.
  intros l' H H0 H1 l a H2. 
  red.
  intros.
  red in H1.
  apply (H1 nme lvl sto sto' sto'').
  - subst.
    simpl.
    red in H0.
    assert (reside nme a = false).
    { eapply nodup_G_cons;eauto.
      eapply  frameG_resideG;eauto. }
    rewrite H2.
    assumption.
  - assumption.
Qed.



Lemma stack_CE_NoDup_G_cons: forall l',
    exact_levelG l' ->
    forall l a,
      l'= a::l ->
      NoDup_G (a::l) -> NoDup_G l.
Proof.
  intros ? h_exct_lvl_l'.
  induction h_exct_lvl_l';subst; intros; unfold NoDup_G in *;intros.
  - inversion H.
  - inversion H;subst.
    remember (Datatypes.length l, fr) as a0.
    assert (exact_levelG (a0 :: l)).
    { subst a0.
      constructor;auto. }
    assert (reside nme a0 = false).
    { eapply nodup_G_cons;eauto.
      eapply  frameG_resideG;eauto. }

    assert (frameG nme (a0 :: l) = Some (lvl, sto)).
    { cbn.
      rewrite H4.
      auto. }

    eapply H0 with (s':= a0 :: s');eauto.
    constructor 3.
    + pose proof exact_lvl_level_of_top (a0::l) as h.
      specialize h with (1:=H3) (2:=H5).
      destruct h as [top [h1 h2]].
      enough (lvl <= level_of a0)%nat by omega.

      assert (top = level_of a0).
      { cbn in h1.
        destruct a0;cbn.
        inversion h1; reflexivity. }
      subst top;auto with arith.
    + assumption.
Qed.


Lemma stack_CE_NoDup_G_sublist: forall CE1 CE2,
    exact_levelG (CE1 ++ CE2) ->
    NoDup_G (CE1++CE2) ->
    NoDup_G CE2.
Proof.
  induction CE1.
  - intros CE2 H h_nodupG. simpl List.app in h_nodupG.
    assumption.
  - intros CE2 H h_nodupG. apply IHCE1.
    { eapply exact_levelG_sublist;eauto. }
    cbn in h_nodupG.
    eapply stack_CE_NoDup_G_cons;eauto;cbn;auto.
Qed.

Lemma stack_CE_NoDup_sublist: forall CE1 CE2,
    exact_levelG (CE1 ++ CE2) ->
    NoDup_G (CE1++CE2) ->
    NoDup (CE1++CE2) ->
    NoDup CE2.
Proof.
  induction CE1.
  - intros CE2 H H0 h_nodup.
    simpl List.app in h_nodup.
    assumption.
  - intros CE2 H H0 h_nodup.
    apply IHCE1.
    + eapply exact_levelG_sublist;eauto.
    + eapply stack_CE_NoDup_G_cons;eauto;reflexivity.
    + cbn in h_nodup.
      eapply stack_CE_NoDup_cons;eauto;cbn;auto.
Qed.

Lemma cut_until_exct_lvl:
  forall CE lvl x,
    exact_levelG ((lvl,x)::CE) ->
    cut_until CE lvl nil CE.
Proof.
  intros CE lvl x h_exct_lvl.
  destruct CE;cbn in *.
  - constructor 1.
  - constructor 2.
    inversion h_exct_lvl;subst.
    inversion H0.
    cbn.
    omega.
Qed.


Lemma nodupG_fetch_cons: forall fr CE id δ,
    exact_levelG (fr :: CE) ->
    NoDup_G (fr :: CE) ->
    fetchG id CE = Some δ ->
    fetch id fr = None.
Proof.
  intros fr CE id δ H H0 H1. 
  destruct (fetch id fr) eqn:heq;auto.
  assert (reside id fr=false) as heq_reside.
  { eapply nodup_G_cons;eauto.
    eapply fetchG_ok;eauto. }
  assert (reside id fr=true) as heq_reside'.
  { eapply fetch_ok;eauto. }
  rewrite heq_reside in heq_reside';discriminate.
Qed.

Lemma nodupG_fetchG_cons: forall fr CE id δ,
    exact_levelG (fr :: CE) ->
    NoDup_G (fr :: CE) ->
    fetchG id CE = Some δ ->
    fetchG id (fr :: CE) = Some δ.
Proof.
  intros fr CE id δ H H0 H1. 
  destruct fr.
  specialize nodupG_fetch_cons with (1:=H) (2:=H0) (3:=H1);intro h.
  cbn in *.
  rewrite h.
  assumption.
Qed.

Lemma updateG_ok_others_frameG: forall stk id v stk',
      updateG stk id v = Some stk' ->
      forall id' lvl sto,
        id<>id' ->
        frameG id' stk = Some (lvl,sto) -> 
        exists sto', frameG id' stk' = Some (lvl,sto').
Proof.
  intros until v.
  functional induction (updateG stk id v);simpl;intros;try discriminate.
  all: try match goal with
  | H:Some _ = Some _ |- _ => rename H into heq_Some
  end.
  all: try match goal with
  | H:_ <> _ |- _ => rename H into hneq
  end.
  - inversion heq_Some; clear heq_Some; subst.
    simpl.
    pose proof update_ok_others_reside _ _ _ _ e0 _ hneq as heq_reside.
    rewrite <- heq_reside.
    destruct (reside id' f) as [heq_Some' | ] eqn:h.
    + match goal with
      | H:Some _ = Some _ |- _ => inversion H;subst
      end.
      unfold update in e0.
      cbn in *.
      destruct (updates sto x v) eqn:heq.
      * inversion e0.
        eauto.
      * discriminate.
    + rewrite H1.
      eauto.
  - inversion heq_Some;subst;clear heq_Some.
    destruct (reside id' f) eqn:h.
    + inversion H1;subst.
      cbn in *.
      rewrite h.
      eauto.
    + cbn in *.
      rewrite h.
      eapply IHo;eauto.
Qed.

Lemma updateG_ok_frameG_others : forall stk id v stk' sto_id  lvl_id,
    updateG stk id v = Some stk' ->
    frameG id stk = Some (lvl_id,sto_id) ->
    forall id' lvl sto_id' sto'_id',
      frameG id' stk = Some (lvl,sto_id') -> 
      frameG id' stk' = Some (lvl,sto'_id') ->
      lvl <> lvl_id ->
      sto_id' = sto'_id'.
Proof.
  intros until v.
  functional induction (updateG stk id v);simpl;try (now (intros;try discriminate));rename x into id.
  - rename e0 into heq_update.
    intros stk' sto_id lvl_id heq_Some heq_Some0 id' lvl sto_id' sto'_id' heq_Some1 heq_frameG hneq. 
    inversion heq_Some;simpl.
    assert (reside id f = true) as heq_reside.
    { eapply update_ok_same_reside_orig; eauto. }
    rewrite heq_reside in heq_Some0.
    inversion heq_Some0;subst.
    assert (reside id' (lvl_id, sto_id) = false) as heq_reside0.
    { cbn in *.
      destruct (resides id' sto_id);auto.
      exfalso.
      inversion heq_Some1.
      now apply hneq. }
    rewrite heq_reside0 in heq_Some1.
    unfold update in heq_update.
    cbn in heq_update.
    functional inversion heq_frameG;subst.
    + exfalso.
      apply hneq.
      destruct (updates sto_id id v);try discriminate.
      now inversion heq_update.
    + rewrite X in heq_Some1.
      now inversion heq_Some1.
  -rename e0 into heq_update.
   intros stk' sto_id lvl_id heq_Some heq_Some0 id' lvl sto_id' sto'_id' heq_Some1 heq_frameG hneq. 
    assert (reside id f = false) as heq_reside.
    { apply reside_false_fetch_none.
      rewrite <- update_ok_none;eauto. }
    rewrite heq_reside in heq_Some0.
    inversion heq_Some;subst.
    destruct (reside id' f) eqn:heq.
   + inversion heq_Some1;subst.
      cbn in heq_frameG.
      cbn in heq.
      rewrite heq in heq_frameG.
      now inversion  heq_frameG.
    + eapply IHo ;eauto.
      cbn in heq_frameG.
      now rewrite heq in heq_frameG.
Qed.

Lemma exact_lvl_frameG_same_lvl : forall stk,
    exact_levelG stk ->
    forall id id' lvl sto_id sto_id',
      frameG id stk = Some (lvl,sto_id) ->
      frameG id' stk = Some (lvl,sto_id') ->
      sto_id = sto_id'.
Proof.
  intros stk h_exct_lvl_stk.
  induction h_exct_lvl_stk.
  - intros id id' lvl sto_id sto_id' heq_frameG heq_frameG0.
    functional inversion heq_frameG.
  - intros id id' lvl sto_id sto_id' heq_frameG heq_frameG0.
    functional inversion heq_frameG;functional inversion heq_frameG0;subst;auto.
    + exfalso.
      apply exact_levelG_frameG_lt_lgth in X.
      * omega.
      * assumption.
    + exfalso.
      apply  exact_levelG_frameG_lt_lgth in X.
      * omega.
      * assumption.
    + eapply IHh_exct_lvl_stk;eauto.
Qed.

Lemma updateG_spec_1 : forall stk id v stk',
    updateG stk id v = Some stk' ->
    exists stk1 sto sto' stk2 ,
      stk = stk1 ++ (sto::stk2)
      /\ stk' = stk1 ++ (sto'::stk2)
      /\ update sto id v = Some sto'
      /\ (forall sto1, List.In sto1 stk1 -> reside id sto1 = false)
      /\ frameG id stk = Some sto.
Proof.
  intros stk id v. 
  functional induction (updateG stk id v).
  - rename e0 into heq_update_f_x.
    intros stk' heq_Some. 
    inversion heq_Some;subst;clear heq_Some.
    exists nil, f, f' , s';repeat split;auto.
    + intros sto1 hIn. 
      inversion hIn.
    + cbn.
      erewrite update_ok_same_reside_orig;eauto.
  - rename e0 into heq_update_f_x.
    rename e1 into heq_updateG_s'_x.
    intros stk' heq_Some.
    inversion heq_Some;subst;clear heq_Some.
    specialize IHo with (1:=heq_updateG_s'_x).
    destruct IHo as [stk1 [sto [sto' [stk2 [heq_s' [heq_s'' [heq_update_x_v [h_forall heq_frameG]]]]]]]].
    subst.
    exists (f::stk1), sto, sto', stk2;repeat split;auto.
    + intros sto1 hIn. 
      cbn in hIn.
      destruct hIn.
      * subst.
        apply update_ok_none in heq_update_f_x.
        now apply fetch_ok_none.
      * now apply h_forall.
    + cbn.
      assert (reside x f = false) as heq_reside.
      { destruct (reside x f) eqn:heq;auto.
        apply fetch_ok_some in heq.
        destruct heq as [ x0 heq_fetch_x_f].
        rewrite update_ok_none in heq_update_f_x.
        rewrite heq_update_f_x in heq_fetch_x_f.
        discriminate. }
      now rewrite heq_reside.
  - discriminate.
  - discriminate.
Qed.


Lemma exact_levelG_sublist2:
  forall (CE1 CE2 : list frame), exact_levelG (CE1 ++ CE2) -> exact_levelG CE2.
Proof.
  induction CE1.
  - now intro.
  - intros CE2 H.
    specialize exact_levelG_sublist with (1:=H).
    intro.
    apply IHCE1.
    assumption.
Qed.

Lemma exact_levelG_frameG_unique_lvl: forall stk1 stk2 lvl sto_id1 id sto_id2,
      exact_levelG (stk1 ++ (lvl, sto_id1) :: stk2) ->
      frameG id (stk1 ++ (lvl, sto_id1) :: stk2) = Some (lvl, sto_id2) ->
      sto_id1 = sto_id2.
Proof.
  induction stk1.
  - intros stk2 lvl sto_id1 id sto_id2 h_exct_lvl heq_frameG. 
    cbn in *.
    destruct (resides id sto_id1) eqn:heq.
    + now inversion heq_frameG.
    + exfalso.
      assert (exact_levelG stk2) as h_exct_lvl_stk2.
      { now eapply exact_levelG_sublist;eauto. }
      specialize exact_lvl_level_of_top with (1:=h_exct_lvl_stk2)(2:=heq_frameG) as h_ex.
      destruct h_ex as [top [heq_level_of_top h_le]].
      specialize exact_lvl_lvl_of_top with (1:=h_exct_lvl_stk2)(2:=heq_level_of_top);intro.
      inversion h_exct_lvl;subst.
      omega.
  - intros stk2 lvl sto_id1 id sto_id2 h_exct_lvl heq_frameG.
    eapply IHstk1.
    + cbn in h_exct_lvl.
      now eapply exact_levelG_sublist;eauto. 
    + functional inversion heq_frameG;subst.
      * exfalso.
        assert (exact_levelG ((lvl, sto_id1) :: stk2)).
        { eapply exact_levelG_sublist2;eauto. }
        eapply exact_lvl_lvl_of_top in H.
        all:swap 1 2.
        cbn.
        reflexivity.
        eapply exact_lvl_lvl_of_top in h_exct_lvl.
        all:swap 1 2.
        cbn.
        reflexivity.
        simpl Datatypes.length in *.
        rewrite app_length in h_exct_lvl.
        simpl Datatypes.length in *.
        fold frame in *. (* omega fails to unify some terms otherwise *)
        omega.
      * eauto.
Qed.

Lemma updateG_ok_others_frameG_orig: forall stk id v stk',
      updateG stk id v = Some stk' ->
      forall id' lvl sto,
        id<>id' ->
        frameG id' stk' = Some (lvl,sto) -> 
        exists sto', frameG id' stk = Some (lvl,sto').
Proof.
  intros until v.
  functional induction (updateG stk id v);simpl;try now (intros;try discriminate).
  - rename e0 into heq_update_f_x.
    intros stk' heq_Some id' lvl sto hneq heq_frameG.
    inversion heq_Some;subst;simpl.
    pose proof update_ok_others_reside _ _ _ _ heq_update_f_x _ hneq as heq_reside.
    rewrite heq_reside.
    simpl in heq_frameG.
    destruct (reside id' f') eqn:h.
    + inversion heq_frameG;subst.
      unfold update in heq_update_f_x.
      cbn in *.
      destruct (updates (store_of f) x v) eqn:heq.
      * inversion heq_update_f_x.
        destruct f;simpl in *.
        eauto.
      * discriminate.
    + rewrite heq_frameG.
      eauto.
  - rename e0 into heq_update_f_x.
    rename e1 into heq_updateG_s'_x.
    intros stk' heq_Some id' lvl sto H0 heq_frameG.
    inversion heq_Some;subst;simpl.
    simpl in *. 
    destruct (reside id' f) eqn:h.
    + inversion heq_frameG.
      eauto.
    + eapply IHo;eauto.
Qed.

Lemma nodup_cons:
  forall (f : ST.frame) (s' : list ST.frame),
    NoDup s' -> NoDup (f::nil) -> NoDup (f :: s').
Proof.
  intros f s' h_nodup_s' h.
  red.
  intros nme lvl sto sto' sto'' h_frameG h_cut.
  functional inversion h_frameG;subst.
  - rename H3 into h_reside.
    eapply h;eauto.
    unfold frameG.
    rewrite h_reside.
    reflexivity.
  - eapply h_nodup_s';eauto.
Qed.

Lemma update_spec_1 : forall fr id v fr',
    updates fr id v = Some fr' -> 
    exists fr1 v0 fr2,
      fr = fr1 ++ (id, v0)::fr2
      /\ resides id fr1 = false.
Proof.
  intros fr id v.
  functional induction (updates fr id v).
  -  apply beq_nat_true in e0.
     subst.
     intros fr' heq_Some. 
     inversion heq_Some.
     subst.
     exists nil.
     cbn;eauto.
  - intros fr' heq_Some. 
    inversion heq_Some; subst;clear heq_Some.
    specialize IHo with (1:=e1).
    destruct IHo as [fr1 [v0 [fr2 [h1 h2]]]].
    subst.
    exists ((y, v') :: fr1), v0 , fr2;split;auto.
    cbn.
    now rewrite e0.
  - intros;discriminate.
  - intros;discriminate.
Qed.
    
(*
Lemma update_spec_1 : forall fr id v fr',
    updates fr id v = Some fr' -> 
    exists fr1 v0 fr2,
      fr = fr1 ++ (id, v0)::fr2.
Lemma update_nodup:
  forall nme (f : ST.frame),
    cuts_to nme f = (sto1, sto2) ->
    forall x v f', ST.update f x v = Some f' ->
                   exists sto1', cuts_to nme f = (sto1', sto2).
         
Lemma update_nodup:
  forall (x : idnum) (v : V) (f : ST.frame) (s' : list ST.frame) 
    (f' : ST.frame), ST.update f x v = Some f' -> NoDup (f::nil) -> NoDup (f'::nil).
Proof.
  intros x v f s' f' h_update h_nodup_fs'.
  red.
  intros nme lvl sto sto' sto'' h_frameG h_cut.
  red in h_nodup_fs'.
  destruct f.
  assert (exists f_prfx, cuts_to nme s0 = (f_prfx, sto'')).
  { admit. }
  destruct H as [f_prfx h_cut_s0].
  eapply h_nodup_fs' with  (lvl:=lvl) (2:=h_cut_s0).
  cbn.
  assert (resides nme s0 = true).
  { functional inversion h_update;subst.
    apply update_ok_same_reside_orig in h_update.
    
    eapply updates_ok_same_resides_orig;eauto.
    unfold update in h_update.
    

  eapply 
  functional inversion h_frameG;subst.
    all:swap 1 2.
    * functional inversion X.
    * 
  


Qed.

Lemma stack_NoDup_prefix: forall CE1 CE2 : list frame,
    exact_levelG (CE1 ++ CE2) -> NoDup_G (CE1 ++ CE2) -> NoDup (CE1 ++ CE2) -> NoDup CE1.
Proof.
Qed.
*)
End STORE_PROP.
