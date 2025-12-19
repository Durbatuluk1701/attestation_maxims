From Equations Require Import Equations.
From Stdlib Require Import List.
Import ListNotations.
From AttestationMaxims Require Import Tactics.
From RocqCandy Require Import Tactics.
From Stdlib Require Import MSets.

Lemma not_InA_nil : forall T eq x, ~ @InA T eq x [].
Proof.
  setoid_rewrite InA_nil; ff.
Qed.

Lemma In_cons_refl : forall {A : Type} (l : list A) h t, 
  l = h :: t -> In h l.
Proof.
  ff.
Qed.

Lemma In_other : forall {A : Type} (l : list A) h t,
  l = h :: t ->
  forall x, In x t -> In x l.
Proof.
  intros.
  subst.
  right.
  exact H0.
Qed.

Fixpoint dep_fold_left {A Ac : Type} (l : list A) (f : forall (acc : Ac) (x : A) (Hin : In x l), Ac) (acc : Ac) : Ac :=
  match l as l' return l = l' -> _ with
  | nil => fun _ => acc
  | h :: t' => fun Hin => 
    (dep_fold_left 
      t' 
      (fun acc0 x Hinx => f acc0 x (In_other l h t' Hin _ Hinx)) 
      (f acc h (In_cons_refl _ _ _ Hin)))
  end eq_refl.

Fixpoint list_take_good {A : Type} (n : nat) (l : list A) (Hnl : n <= length l) 
    : {l' : list A | length l' = n /\ exists l'', l = l' ++ l''}.
Proof.
  ref (
    match n as n' return n = n' -> {l' : list A | length l' = n /\ exists l'', l = l' ++ l''} with
    | 0 => fun Hn => exist _ nil _
    | S n'' => fun Hn =>
      match l as l' return l = l' -> {l' : list A | length l' = n /\ exists l'', l = l' ++ l''} with
      | nil => fun Hl => _
      | h :: t' => fun Hl => _
      end eq_refl
    end eq_refl
  ).
  - split.
    * subst. reflexivity.
    * exists l. reflexivity.
  - subst.
    simpl in *.
    exfalso.
    eapply (Nat.nle_succ_0 _ Hnl).
  - assert (n'' <= length t'). {
      subst.
      simpl in *.
      lia.
    }
    destruct (list_take_good A n'' t' H) as [lret Hlret].
    ref (exist _ (h :: lret) _).
    split; ff.
Qed.

Fixpoint list_find_first {A : Type} `{DecEq A} (x : A) (l : list A) 
    : {exists lf le, l = lf ++ x :: le } + {~ In x l}.
Proof.
  ref (
    match l as l' return l = l' -> {exists lf le, l = lf ++ x :: le } + {~ In x l} with
    | nil => fun HL => _
    | h :: t' => fun HL => 
      match dec_eq x h with
      | left _ => _
      | right _ => 
        match list_find_first _ _ x t' with
        | left _ => (* hard *) _
        | right _ => _
        end
      end
    end eq_refl
  ); subst.
  - right.
    intros Hinx.
    eapply (in_nil Hinx).
  - left.
    exists nil, t'. reflexivity.
  - left.
    destruct e as [lf1 [lf2 HE]].
    exists (h :: lf1), lf2.
    rewrite HE.
    reflexivity.
  - right.
    intros HC.
    eapply n0.
    invc HC.
    * congruence.
    * eapply H0.
Qed.

Definition has_cycle {ty : Type} `{DecEq ty} 
    (h : ty) (t' : list ty) (HNDt : NoDup t') : 
  {exists p1 p2, h :: t' = h :: p1 ++ h :: p2} + {NoDup (h :: t')}.
Proof.
  ref (match t' as t'' return t' = t'' -> 
    {exists p1 p2, h :: t' = h :: p1 ++ h :: p2} + {NoDup (h :: t')} with
  | nil => fun _ => right _
  | off :: rst => fun HP => _
  end eq_refl).
  - subst; eapply NoDup_cons; ff.
  - pp (list_find_first h t').
    destruct H0.
    * left.
      ff.
    * right.
      econstructor; assumption.
Qed.

Definition is_cycle {t : Type} (p : list t) : Prop :=
  exists h p1 p2, p = h :: p1 ++ h :: p2.

Module Type ClosureS.
  Parameter t : Type.

  Inductive path (rel : list (t * t)) :=
  | Dead : forall (p : list t), is_cycle p -> path rel
  | Live : forall (p : list t), NoDup p -> path rel.
  Arguments Dead {rel} _ _.
  Arguments Live {rel} _ _.

  Parameter one_step_paths : forall (v : t) (rel : list (t * t)), path rel.
  Parameter multi_step_paths 
      : forall (v : t) (rel : list (t * t)) (visited : list t), list (path rel).
End ClosureS.

Module Closure (Ord : OrderedTypeWithLeibniz) <: ClosureS with Definition t := Ord.t.
  Definition t := Ord.t.

  Module CSet := MSetList.Make(Ord).
  Module Import CSetFacts := WFactsOn(Ord)(CSet).
  Module Import CSetPropsOn := WPropertiesOn(Ord)(CSet).
  Module Import CSetDecide := WDecideOn(Ord)(CSet).
  Ltac2 Notation "fsetdec" := ltac1:(fsetdec).

  Definition real_dec_eq (x y : t) : {x = y} + {x <> y}.
  Proof.
    destruct (Ord.eq_dec x y).
    - left; eapply Ord.eq_leibniz; eauto.
    - right.
      intros HC.
      subst.
      eapply n.
      erewrite MSetDecideAuxiliary.eq_refl_iff.
      apply I.
  Qed.

  Local Instance DecEq_t : DecEq t := { dec_eq := real_dec_eq }.

  Fixpoint all_in_rel (rela : list (t * t)) :=
    match rela with
    | nil => CSet.empty
    | (x, y) :: t' => CSet.add x (CSet.add y (all_in_rel t'))
    end.

  Inductive path (rel : list (t * t)) :=
  | Dead : forall (p : list t), 
    Forall (fun x => InA Ord.eq x (CSet.elements (all_in_rel rel))) p ->
    is_cycle p -> 
    path rel
  | Live : forall (p : list t), 
    Forall (fun x => InA Ord.eq x (CSet.elements (all_in_rel rel))) p ->
    NoDup p -> 
    path rel.
  Arguments Dead {rel} _ _.
  Arguments Live {rel} _ _.

  Definition path_length {rel} (pt : path rel) : nat :=
    match pt with
    | Dead p _ _ => length p
    | Live p _ _ => length p
    end.

  Definition AllDead (rel : list (t * t)) := 
    { l : list (path rel) | 
      Forall (fun pt => exists v hin hc, pt = Dead v hin hc) l 
    }.
  Definition AllDead_with_len (rel : list (t * t)) (n : nat) := 
    { l : list (path rel) | 
      Forall (fun pt => exists v hin hc, pt = Dead v hin hc) l /\
      Forall (fun pt => path_length pt = n) l
    }.
  Definition AllDeadNil (rel : list (t * t)) : AllDead rel := exist _ nil (Forall_nil _).
  Definition AllDeadNil_len (rel : list (t * t)) {n} : AllDead_with_len rel n := 
    exist _ nil (conj (Forall_nil _) (Forall_nil _)).

  Definition AllLive (rel : list (t * t)) := 
    { l : list (path rel) | 
      Forall (fun pt => exists v hin hc, pt = Live v hin hc) l 
    }.
  Definition AllLive_with_len (rel : list (t * t)) (n : nat) := 
    { l : list (path rel) | 
      Forall (fun pt => exists v hin hc, pt = Live v hin hc) l /\
      Forall (fun pt => path_length pt = n) l
    }.
  Definition AllLiveNil (rel : list (t * t)) : AllLive rel := exist _ nil (Forall_nil _).
  Definition AllLiveNil_len (rel : list (t * t)) {n} : AllLive_with_len rel n := 
    exist _ nil (conj (Forall_nil _) (Forall_nil _)).

  (* Definition one_step_paths_set a rel :=
    List.fold_left
      (fun acc '(x, y) => if Ord.eq_dec x a then CSet.add y acc else acc)
      rel
      CSet.empty. *)

  Definition one_step_paths a rela :=
    List.fold_left
      (fun acc '(x, y) => if Ord.eq_dec x a then CSet.add y acc else acc)
      rela
      CSet.empty.

  Lemma fold_left_add : forall (l : list (t * t)) a (v : t) rst,
    CSet.Equal
      (List.fold_left 
        (fun acc '(x, y) => 
          if Ord.eq_dec x a then CSet.add y acc else acc) l (CSet.add v rst))
      (CSet.add v (List.fold_left 
        (fun acc '(x, y) => if Ord.eq_dec x a then CSet.add y acc else acc) l rst)).
  Proof.
    induction l; ff; try (fsetdec).
    repeat (erewrite IHl).
    fsetdec.
  Qed.

  Lemma one_step_paths_subset : forall a rela,
    CSet.Subset (one_step_paths a rela) (all_in_rel rela).
  Proof.
    unfold one_step_paths.
    induction rela.
    - ff.
    - simpl in *.
      repeat (break_match; subst; simpl in *; eauto);
      try (fsetdec).
      setoid_rewrite fold_left_add.
      fsetdec.
  Qed.

  Definition extend_one_step (rela : list (t * t)) 
      {n : nat}
      (paths :  AllLive_with_len rela (S n))
      : (AllDead_with_len rela (S (S n)) * AllLive_with_len rela (S (S n))).
  Proof.
    destruct paths as [paths [HpathsLive HpathsLen]].
    ref (dep_fold_left paths _ (AllDeadNil_len rela, AllLiveNil_len rela)).
    clear deadNil liveNil.
    simpl in *.
    intros [dead live] path Hinpaths.
    unfold AllLive_with_len, AllDead_with_len in *.
    destruct path.
    - exfalso.
      erewrite Forall_forall in HpathsLive.
      pp (HpathsLive _ Hinpaths).
      repeat break_exists.
      congruence.
    - destruct p as [| h t'].
      * (* empty path!? - should not happen! *)
        erewrite Forall_forall in *.
        apply HpathsLen in Hinpaths.
        simpl in Hinpaths.
        congruence.
      * set (one_step := CSet.elements (one_step_paths h rela)).

        ref (dep_fold_left one_step _ (dead, live)).
        clear dead live.
        intros [dead live] next Hinnext.
        destruct (has_cycle next (h :: t') n0).
        + (* next is already in the path, so it forms a cycle *)
          destruct dead as [deadV [deadH1 deadH2]].
          split > [ | apply live].
          clear live.
          ref (exist _ ((Dead (next :: h :: t') _ _) :: deadV) _).
          split.
          ++ 
            erewrite Forall_forall.
            intros.
            simpl in *.
            destruct H.
            -- subst.
              repeat eexists; eauto.
              Unshelve.
              --- 
                erewrite Forall_forall.
                intros.
                pp (one_step_paths_subset).
                clear Hinpaths.
                erewrite Forall_forall in f.
                assert (x = next \/ In x (h :: t')). {
                  destruct H.
                  - left. subst. reflexivity.
                  - right. assumption.
                }
                destruct H1.
                ** subst.
                  setoid_rewrite <- elements_iff.
                  erewrite <- H0.
                  setoid_rewrite elements_iff.
                  eapply In_InA.
                  +++ eapply Ord.eq_equiv.
                  +++
                    subst one_step.
                    eapply Hinnext.
                ** eapply f.
                  eapply H1.
              ---
                unfold is_cycle.
                repeat break_exists.
                rewrite H.
                exists next, x, x0.
                reflexivity.
            -- erewrite Forall_forall in *.
              eapply deadH1.
              assumption.
          ++ erewrite Forall_forall in *.
            intros.
            simpl in H.
            destruct H.
            -- subst.
              simpl.
              pp (HpathsLen _ Hinpaths).
              simpl in *.
              rewrite H.
              reflexivity.
            -- eapply deadH2.
              assumption.
        + (* it is not a cycle, rather LIVE! *)
          destruct live as [liveV [liveH1 liveH2]].
          split > [ apply dead | ].
          clear dead.
          ref (exist _ ((Live (next :: h :: t') _ _) :: liveV) _).
          split.
          ++ 
            erewrite Forall_forall.
            intros.
            simpl in *.
            destruct H.
            -- subst.
              repeat eexists; eauto.
              Unshelve.
              --- 
                erewrite Forall_forall.
                intros.
                pp (one_step_paths_subset).
                clear Hinpaths.
                erewrite Forall_forall in f.
                assert (x = next \/ In x (h :: t')). {
                  destruct H.
                  - left. subst. reflexivity.
                  - right. assumption.
                }
                destruct H1.
                ** subst.
                  setoid_rewrite <- elements_iff.
                  erewrite <- H0.
                  setoid_rewrite elements_iff.
                  eapply In_InA.
                  +++ eapply Ord.eq_equiv.
                  +++
                    subst one_step.
                    eapply Hinnext.
                ** eapply f.
                  eapply H1.
              --- eauto.
            -- erewrite Forall_forall in *.
              eapply liveH1.
              assumption.
          ++ erewrite Forall_forall in *.
            intros.
            simpl in H.
            destruct H.
            -- subst.
              simpl.
              pp (HpathsLen _ Hinpaths).
              simpl in *.
              rewrite H.
              reflexivity.
            -- eapply liveH2.
              assumption.
  Qed.

  Lemma InA_In : forall x l,
      InA Ord.eq x l -> In x l.
  Proof.
    induction l; ff.
    - invc H.
    - invc H.
      * eapply Ord.eq_leibniz in H1; ff.
      * right; ff.
  Qed.

  Lemma all_in_rel_cardinal : forall rela n (paths : AllLive_with_len rela n),
    (exists p, In p (proj1_sig paths)) ->
    n <= CSet.cardinal (all_in_rel rela).
  Proof.
    intros.
    unfold AllLive_with_len in *.
    destruct paths as [paths [Hlive Hlen]].
    destruct H.
    simpl in H.
    erewrite Forall_forall in *.
    pp (Hlive _ H).
    pp (Hlen _ H).
    clear Hlive Hlen.
    destruct H0 as [v [hin [hn Hpath]]].
    subst.
    simpl in *.
    clear H.
    erewrite Forall_forall in *.
    erewrite CSet.cardinal_spec.
    set (L := CSet.elements (all_in_rel rela)) in *.
    clearbody L.
    eapply (@NoDup_incl_length _ v L hn).
    unfold incl.
    intros.
    eapply hin in H.
    eapply InA_In in H.
    eapply H.
  Qed.

  Equations? multi_step_paths_set (rela : list (t * t)) {n} 
      (paths : AllLive_with_len rela (S n))
      : list (path rela)
    by wf (S (CSet.cardinal (all_in_rel rela)) - (S n)) :=
    multi_step_paths_set rela paths :=
    match (proj1_sig paths) as paths' return paths' = proj1_sig paths -> list _ with
    | nil => fun _ => nil
    | _ =>
      fun HP =>
      let '(dead_paths, live_paths) := extend_one_step rela paths in
      (multi_step_paths_set rela live_paths) ++ 
        (proj1_sig dead_paths) ++ (proj1_sig live_paths)
    end eq_refl.
  Proof.
    (* clear multi_step_paths_set dead_paths live_paths.
    unfold AllLive_with_len in *.
    destruct paths as [liveV [HliveV HliveLen]].
    simpl in *.
    erewrite Forall_forall in *.
    subst. *)
    repeat (destruct n > [ lia | ]).
    pp (all_in_rel_cardinal rela (S n) paths).
    assert (exists p', In p' (proj1_sig paths)). {
      exists p.
      erewrite <- HP.
      ff.
    }
    eapply H in H0.
    lia.
  Qed.

  Definition multi_step_paths (a : t) (rela : list (t * t)) : list (path rela).
  destruct (InA_dec Ord.eq_dec a (CSet.elements (all_in_rel rela))).
  * 
    pp (@multi_step_paths_set rela 0).
    eapply X.
    eapply (exist _ [ Live [ a ] _ _ ] ).
    split;
    erewrite Forall_forall;
    intros;
    simpl in H;
    destruct H > [ | exfalso; assumption ];
    subst.
    - exists [a]; eexists; eexists.
      reflexivity.
    - simpl; reflexivity.
    Unshelve.
    erewrite Forall_forall.
    intros.
    simpl in H; destruct H > [ | exfalso; assumption ].
    subst.
    assumption.

    econstructor.
    ff.
    econstructor.
  * eapply nil.
  Qed.