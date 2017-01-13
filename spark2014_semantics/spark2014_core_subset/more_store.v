Require Import environment.
Require Import Morphisms Relations.

(* Import STACK. *)

(* Functional Scheme update_ind := Induction for update Sort Prop. *)
(* Functional Scheme updates_ind := Induction for updates Sort Prop. *)
(* Functional Scheme fetch_ind := Induction for fetch Sort Prop. *)


Module STORE_PROP (V:ENTRY).
  Module ST := STORE(V).
  Include ST.
  Functional Scheme update_ind := Induction for ST.update Sort Prop.
(*   Functional Scheme updates_ind := Induction for ST.updates Sort Prop. *)
  Functional Scheme fetch_ind := Induction for fetch Sort Prop.

  (* The AST provided by gnat/sireum are supposed to have no two variables sharing
   the same name. This should imply that there are no duplication of name in stacks. *)
  (* intra-store *)
  Definition NoDup (s : stack) := 
    forall nme lvl sto (sto' sto'':store),
      frameG nme s = Some (lvl,sto) ->
      cuts_to nme sto = (sto',sto'') ->
      resides nme sto'' = false.

  (* extra-store *)
  Definition NoDup_G (s : stack) := 
    forall nme lvl sto s' s'',
      frameG nme s = Some (lvl,sto) ->
      cut_until s lvl s' s'' ->
      resideG nme s'' = false.


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
    | cut_until ?st ?s ?fr ?paramsprf ?args (Run_Time_Error ?er) => fresh "h_cut_until_RE"
    | cut_until ?st ?s ?fr ?paramsprf ?args (Normal ?fr') => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args ?fr' => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until_" fr
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until"
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

  Lemma reside_false_fetch_none: forall (id : idnum) (fr : frame), reside id fr = false <-> fetch id fr = None.
  Proof.
    intros id fr. 
    unfold reside, fetch in *.
    symmetry.
    apply fetches_ok_none.
  Qed.

  Lemma resideG_false_fetchG_none: forall (id : idnum) (sto : stack), resideG id sto = false -> fetchG id sto = None.
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



End STORE_PROP.
