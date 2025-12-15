From Equations Require Import Equations.
From RocqCandy Require Import All.
Import MapNotations.
From Stdlib Require Import List String.
From Stdlib Require Export ListSet.
From AttestationMaxims Require Import Tactics.
Local Open Scope map_scope.

Section Sets.

  Context (A : Type) `{DK : DecEq A}.

  Definition bin_rel := set (A * A).
  
  Lemma length_set_add : forall (s : set A) a,
    List.length (set_add dec_eq a s) =
      match in_dec dec_eq a s with
      | left _ => List.length s
      | right _ => S (List.length s)
      end.
  Proof.
    induction s; ff.
    - edestruct n; ff.
    - erewrite IHs; ff.
    - erewrite IHs; ff.
      edestruct n0; ff.
  Qed.

  Fixpoint all_in_rel (d : bin_rel) : set A :=
    match d with
    | [] => nil
    | (c1, c2) :: rest => 
      set_add dec_eq c1 (set_add dec_eq c2 (all_in_rel rest))
    end.

  Fixpoint get_all_one_step_reverse (d : bin_rel) (c : A) : set A :=
    match d with
    | [] => nil
    | (c1, c2) :: rest =>
        if dec_eq c2 c then set_add dec_eq c1 (get_all_one_step_reverse rest c)
        else get_all_one_step_reverse rest c
    end.
  
  Lemma in_get_all_one_step_reverse_impl_in_all_in_rel : forall (d : bin_rel) (c c' : A),
    In c' (get_all_one_step_reverse d c) ->
    In c' (all_in_rel d).
  Proof.
    induction d; ff.
    repeat (erewrite set_add_iff in *); ff.
    eapply IHd in H.
    repeat (erewrite set_add_iff in *); ff.
  Qed.

  Lemma not_In_set_add : forall {A} `{DecEq A} s (a : A),
    ~ In a s ->
    List.length (set_add dec_eq a s) = S (List.length s).
  Proof.
    induction s; ff.
    - edestruct H0; ff.
  Qed.

    
  Lemma in_acc_impl_in_set_fold_union : forall {A} `{HD : DecEq A} (f : A -> set A) (lst : list A) (x : A) (acc : set A),
    (In x acc) ->
    In x (fold_left (fun acc a => set_union dec_eq acc (f a)) lst acc).
  Proof.
    induction lst; ff.
    eapply IHlst; 
    erewrite set_union_iff; ff.
  Qed.

  Lemma set_in_fold_left_union : forall (f : A -> set A) (lst : list A) (x : A) (acc : set A),
    In x (set_fold_left (fun acc a => set_union dec_eq acc (f a)) lst acc) <->
    (* either in acc to start or in f a*)
    (In x acc) \/ (exists a, In a lst /\ In x (f a)).
  Proof.
    split.
    - generalizeEverythingElse lst.
      induction lst; ff.
      eapply IHlst in H; ff.
      erewrite set_union_iff in *; ff.
    - ff.
      destruct H.
      * generalizeEverythingElse lst.
        induction lst; ff.
        pp (IHlst _ f x (set_union dec_eq acc (f a))).
        eapply H0.
        erewrite set_union_iff; ff.
      * generalizeEverythingElse lst.
        induction lst; ff.
        destruct (in_dec dec_eq x0 lst).
        + pp (IHlst _ f x (set_union dec_eq acc (f x0))).
          eapply H.
          ff.
        + eapply in_acc_impl_in_set_fold_union; ff.
          erewrite set_union_iff; ff.
  Qed.

  Equations? get_multi_step_reverse' (c : A) (rel : set (A * A)) (seen : set A) : set A
      by wf (List.length (all_in_rel rel) - List.length seen) :=
  get_multi_step_reverse' c rel seen :=
    match (List.length (all_in_rel rel) - List.length seen) as n return (List.length (all_in_rel rel) - List.length seen = n -> _) with
    | 0 => fun Hm => nil
    | S _ =>
      fun Hm =>
      match (in_dec (DecEq.dec_eq) c seen) with
      | left _ => nil
      | right _ =>
        let parents := get_all_one_step_reverse rel c in
        set_fold_left 
          (fun (acc : set A) c' => set_union dec_eq acc (get_multi_step_reverse' c' rel (set_add dec_eq c seen)))
          parents
          parents
      end
    end eq_refl.
  Proof.
    erewrite not_In_set_add; ff l.
  Defined.

  Definition get_multi_step_reverse (c : A) (d : bin_rel) : set A :=
    get_multi_step_reverse' c d nil.

  Theorem seen_set_always_incl : forall n c rel seen,
    List.length (all_in_rel rel) - List.length seen <= n ->
    incl seen (all_in_rel rel) ->
    In c (all_in_rel rel) ->
    forall x,
    In x (get_multi_step_reverse' c rel seen) ->
    incl (x :: seen) (all_in_rel rel).
  Proof.
    unfold incl.
    induction n; ff.
    - ltac1:(simp get_multi_step_reverse' in *); ff l.
    - ltac1:(simp get_multi_step_reverse' in *); ff l.
      erewrite set_in_fold_left_union in *; ff l;
      elim_all_contras; ff l.
      * eapply in_get_all_one_step_reverse_impl_in_all_in_rel; ff.
      * destruct (in_dec dec_eq a seen); ff.
        eapply IHn in H3; ff l.
        + erewrite length_set_add; ff l.
        + erewrite set_add_iff in *; ff.
        + eapply in_get_all_one_step_reverse_impl_in_all_in_rel; ff.
  Qed.

  Lemma in_add_split : forall (c c' : A) s,
    In c (set_add dec_eq c' s) -> c = c' \/ In c s.
  Proof.
    induction s; ff.
    apply IHs in H0; ff.
  Qed.

  Lemma empty_set_length_iff : forall (T : Type) (s : list T),
    Datatypes.length s = 0 <-> s = [].
  Proof.
    induction s; ff.
  Qed.

  Lemma union_non_empty_len : forall (s s' : list A),
    Datatypes.length s <> 0 ->
    Datatypes.length (set_union dec_eq s s') <> 0.
  Proof.
    induction s; ff.
    apply empty_set_length_iff in H0.
    assert (In a (set_union dec_eq (a :: s) s')).
    apply set_union_intro; ff.
    rewrite H0 in H1. inversion H1.
  Qed.

  Lemma add_set_len : forall (s : list A) a,
    Datatypes.length s <= Datatypes.length (set_add dec_eq a s).
  Proof.
    induction s; ff.
    pp (IHs a0). lia.
  Qed.

  Lemma union_non_empty_len_more : forall (s s' : list A),
    Datatypes.length s <= Datatypes.length (set_union dec_eq s s').
  Proof.
    induction s'; ff.
    rewrite <- add_set_len. auto.
  Qed.

  Lemma union_non_empty_len_more_r : forall (s s' : list A),
    Datatypes.length s' <= Datatypes.length (set_union dec_eq s s').
  Proof.
  Admitted.

  Lemma union_non_empty : forall (s s' : list A),
    s <> [] ->
    set_union dec_eq s s' <> [].
  Proof.
    induction s; ff.
    assert (In a (set_union dec_eq (a :: s) s')).
    apply set_union_intro; ff.
    rewrite H0 in H1. inversion H1.
  Qed.

  Lemma get_one_get_multi : forall c c' E,
    In c' (get_all_one_step_reverse E c) ->
    In c' (get_multi_step_reverse c E).
  Proof.
    induction E.
    - ff.
    - intro. destruct a.
      unfold get_multi_step_reverse in *.
      ltac1:(simp get_multi_step_reverse' in *); ff; try (erewrite set_in_fold_left_union in *); ff.
      * erewrite Nat.sub_0_r in *; try (erewrite length_zero_iff_nil in *); ff.
      * repeat (erewrite length_set_add in *; ff).
      * repeat (erewrite length_set_add in *; ff).
  Qed.

  (* Lemma all_in_rel_empty : forall E,
    all_in_rel E = nil <-> E = nil.
  Proof.
    induction E; ff.
    apply union_non_empty in H; ff.
  Qed.

  Lemma all_in_rel_empty_len : forall E,
    Datatypes.length (all_in_rel E) = 0 <-> Datatypes.length E = 0.
  Proof.
    induction E; ff.
    apply union_non_empty_len in H; ff.
  Qed. *)

  Lemma in_dep_rel_one_step : forall c c' E,
    In (c, c') E <->
    In c (get_all_one_step_reverse E c').
  Proof.
    induction E; ff.
    apply set_add_intro; ff. right; apply IHE; apply H0.
    - apply IHE; ff.
    - apply set_add_elim in H; destruct H; ff.
      + right. apply IHE; ff.
    - right. apply IHE; ff.
  Qed.

  Lemma  expand_dep_rel_one_step : forall c c' E E',
    (forall x, In x E -> In x E') ->
    In c (get_all_one_step_reverse E c') ->
    In c (get_all_one_step_reverse E' c').
  Proof.
    induction E'; ff.
    - apply in_dep_rel_one_step in H0; ff.
    - apply in_dep_rel_one_step in H0; ff.
      destruct (dec_eq c a0); try (apply set_add_intro); ff.
      + right. apply H in H0. destruct H0; ff. apply in_dep_rel_one_step. ff.
    - apply in_dep_rel_one_step in H0; ff.
      apply in_dep_rel_one_step. apply H in H0; ff.
  Qed. 

  Lemma expand_dep_rel_test' : forall n E sn,
    List.length (all_in_rel E) - List.length sn <= n ->
    forall c c',
    In c (get_multi_step_reverse' c' E sn) ->
    forall a,
    In c (get_multi_step_reverse' c' (a :: E) sn).
  Proof.
    induction n; ff.
    - ltac1:(simp get_multi_step_reverse' in *); ff l.
    - ltac1:(simp get_multi_step_reverse' in *); ff l;
      erewrite set_in_fold_left_union in *; ff l.
      * assert (S n0 <= 0). {
          erewrite <- Heqn1, <- Heqn0.
          erewrite Nat.sub_le_mono_r; ff.
          repeat (erewrite add_set_len; ff).
        }
        lia.
      * elim_all_contras.
        + left; eapply set_add_intro; ff.
        + ff.
          eapply IHn in H1.
          --  
            right.
            exists v.
            split; ff.
            eapply set_add_intro; ff.
          -- erewrite length_set_add; ff.
            destruct (List.length (all_in_rel E)); ff l.
      * elim_all_contras.
        eapply IHn in H1; ff l.
        erewrite length_set_add; ff.
        destruct (List.length (all_in_rel E)); ff l.
  Qed.

  Lemma get_multi_dep_rel_cons_self : forall a a' E s,
    (forall x, In x s -> In x (all_in_rel E)) ->
    ~ (In a s) ->
    In a' (get_multi_step_reverse' a ((a', a) :: E) s).
  Proof.
    intros.
    ltac1:(simp get_multi_step_reverse' in *); ff l.
    - admit.
    - erewrite set_in_fold_left_union in *.
      left.
      erewrite set_add_iff; ff.
  Admitted.

  Lemma in_one_step_impl_in_targ : forall c c' E,
    In c' (get_all_one_step_reverse E c) ->
    In c (all_in_rel E) /\ In c' (all_in_rel E).
  Proof.
    induction E; ff.
    - repeat (erewrite set_add_iff in *); ff.
      split.
      * ff.
      * eapply IHE in H0; ff.
    - repeat (erewrite set_add_iff in *); ff.
      eapply IHE in H; ff.
      bool_logic.
  Qed.

  Lemma NoDup_all_in_rel : forall E,
    NoDup (all_in_rel E).
  Proof.
    induction E; ff.
    - econstructor.
    - eapply set_add_nodup.
      eapply set_add_nodup.
      ff.
  Qed.

  Lemma get_one_get_multi' : forall n c c' E s,
    NoDup s ->
    List.length (all_in_rel E) - List.length s <= n ->
    incl s (all_in_rel E) ->
    In c' (get_all_one_step_reverse E c) ->
    ~ In c s ->
    In c' (get_multi_step_reverse' c E s).
  Proof.
    unfold incl.
    induction n; ff.
    - ltac1:(simp get_multi_step_reverse' in *); ff l.
      eapply in_one_step_impl_in_targ in H2; ff.
      pp (NoDup_incl_length H H1).
      assert (List.length (all_in_rel E) <= List.length s) by lia.
      pp (@NoDup_length_incl A _ _ H H6 H1).
      unfold incl in *.
      ff.
    - ltac1:(simp get_multi_step_reverse' in *); ff l.
      * eapply in_one_step_impl_in_targ in H2; ff.
        pp (NoDup_incl_length H H1).
        assert (List.length (all_in_rel E) <= List.length s) by lia.
        pp (@NoDup_length_incl A _ _ H H6 H1).
        unfold incl in *.
        ff.
      * erewrite set_in_fold_left_union in *; ff l.
  Qed.
  Print Assumptions get_one_get_multi'.

  (* 
  Lemma expand_dep_rel_test : forall E,
    forall c c',
    In c (get_multi_step_reverse c' E) ->
    forall a,
    In c (get_multi_step_reverse c' (a :: E)).
  Proof.
    intros.
    eapply expand_dep_rel_test'; ff.
  Qed.

  Lemma get_one_step_one_step_trans : forall c c' E,
    In c' (get_all_one_step_reverse E c) -> c' <> c ->
    forall c'',
      c'' <> c -> c'' <> c' ->
      In c'' (get_all_one_step_reverse E c') ->
      In c'' (get_multi_step_reverse c E).
  Proof.
    induction E; ff.
  Admitted.

  Lemma get_one_step_multi_step_trans : forall c c' E,
    In c' (get_all_one_step_reverse E c) ->
    forall c'',
      In c'' (get_multi_step_reverse c' E) ->
      In c'' (get_multi_step_reverse c E).
  Proof.
    induction E; ff.
    unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; erewrite set_in_fold_left_union in *.
    - admit.
    - admit.
  Admitted.

  Lemma set_mem_cons : forall {A} `{DecEq A} (x : A) (s : set A),
    set_mem dec_eq x s = true ->
    forall e, set_mem dec_eq x (e :: s) = true.
  Proof.
    induction s; ff.
  Qed.

  Lemma get_multi_step_one_step_trans : forall c c' E,
    In c' (get_multi_step_reverse c E) ->
    forall c'',
      In c'' (get_all_one_step_reverse E c') ->
      In c'' (get_multi_step_reverse c E).
  Proof.
    induction E; ff.
    unfold get_multi_step_reverse.
    ltac1:(simp get_multi_step_reverse' in * ); ff.
    - rewrite Nat.sub_0_r in Heqn. apply union_non_empty_len in Heqn; ff.
    - erewrite set_in_fold_left_union in *; destruct (dec_eq c'' a0); ff.
    - erewrite set_in_fold_left_union in *.
      assert (In c' (get_multi_step_reverse c E)) by admit.
      destruct (dec_eq c'' a0).
      + admit.
  Admitted.

  Lemma get_multi_step_reverse_trans_test : forall c c' E,
    In c' (get_multi_step_reverse c E) ->
    forall c'',
      In c'' (get_multi_step_reverse c' E) ->
      In c'' (get_multi_step_reverse c E).
  Admitted.

  Lemma get_multi_step_self_nil : forall s c c' E,
    ~ (set_In c' (get_multi_step_reverse' c E (set_add dec_eq c s))).
  Proof.
    intros.
    ltac1:(simp get_multi_step_reverse' in * ); ff.
    eapply n0.
    erewrite set_add_iff; ff.
  Qed.

  Theorem get_multi_step_reverse_spec : forall n E s,
    List.length (all_in_rel E) - List.length s <= n ->
    forall c c',
    In c' (get_multi_step_reverse' c E s) <->
    (In c' (get_all_one_step_reverse E c) \/
     (exists c'', In c'' (get_all_one_step_reverse E c) /\
                  In c' (get_multi_step_reverse' c'' E (set_add dec_eq c s)))).
  Proof.
  Admitted.
  *)

  (*
  Lemma multi_seen_irrel : forall n E s c c1 c2 cf,
    NoDup s ->
    List.length (all_in_rel E) - List.length s <= n ->
    incl s (all_in_rel E) ->
    c <> c1 ->
    c <> c2 ->
    In cf (get_multi_step_reverse' c E (set_add dec_eq c1 s)) ->
    In cf (get_multi_step_reverse' c E (set_add dec_eq c2 s)).
  Proof.
    ltac1:(simp get_multi_step_reverse' in * ).

    unfold incl.
    induction n; ff.
    - ltac1:(simp get_multi_step_reverse' in * ); ff l.
      * admit.
      * erewrite set_add_iff in *; ff.
      * erewrite set_add_iff in *; ff; elim_all_contras; ff l.
        erewrite set_in_fold_left_union in *; ff l.
        destruct (in_dec dec_eq cf (get_all_one_step_reverse E c)); ff.
        right.
        exists x; split; ff.
    (* - ltac1:(simp get_multi_step_reverse' in * ); ff l.
      * 
      erewrite set_in_fold_left_union in *; ff l.
      Control.enter (fun () => elim_all_contras); ff l.
      * 
    - ltac1:(simp get_multi_step_reverse' in * ); ff l. *)
  Admitted.
  *)

  Lemma not_in_self : forall n c E s,
    NoDup s ->
    List.length (all_in_rel E) - List.length s <= n ->
    incl s (all_in_rel E) ->
    In c s ->
    forall c',
    ~ (In c' (get_multi_step_reverse' c E s)).
  Proof.
    unfold incl.
    induction n; ff l.
    - ltac1:(simp get_multi_step_reverse' in * ); ff l.
    - ltac1:(simp get_multi_step_reverse' in * ); ff l.
  Qed.

  Ltac2 Notation "incls" :=
    try (unfold incl in *); ff l;
    repeat (erewrite set_add_iff in *; ff);
    repeat (find_eapply_lem_hyp in_one_step_impl_in_targ; ff);
    repeat (erewrite set_add_iff in *; ff).

  Ltac2 Notation "nodups" := repeat (eapply set_add_nodup; ff l).

  Lemma get_multi_step_reverse_trans : forall n c c' E s,
    NoDup s ->
    List.length (all_in_rel E) - List.length s <= n ->
    incl s (all_in_rel E) ->
    In c' (get_multi_step_reverse' c E s) ->
    forall s' c'',
      In c'' (get_multi_step_reverse' c' E s') ->
      NoDup s' ->
      incl (set_add dec_eq c s) s' ->
      incl s' (all_in_rel E) ->
      In c'' (get_multi_step_reverse' c E s).
  Proof.
    unfold incl.
    induction n;
    intros c c' E s HNDs HL HssE H1 s' c'' H2 HNDs' Hss'E Hsss'; ff.
    - ltac1:(simp get_multi_step_reverse' in *); ff l.
    - 
      ltac1:(simp get_multi_step_reverse' in *); ff l.
      erewrite set_in_fold_left_union in *; ff l;
      elim_all_contras; ff l.
      * destruct (in_dec dec_eq c'' (get_all_one_step_reverse E c)); ff;
        right.
        exists c'; split; ff.
        eapply get_one_get_multi'; ff l.
        + nodups.
        + incls.
      * destruct (in_dec dec_eq c'' (get_all_one_step_reverse E c)); ff.
        right.
        exists c'.
        split.
        ff.
        eapply IHn; ff l.
        + nodups.
        + erewrite length_set_add; ff l.
        + eapply get_one_get_multi'.
          -- nodups.
          -- incls.
          -- incls.
          -- ff.
          -- ff.
        + nodups.
        + incls.
        + incls.
      * destruct (in_dec dec_eq c'' (get_all_one_step_reverse E c)); ff.
        right.
        assert (Hinvs : ~ In v s). {
          intros HC.
          eapply (not_in_self _ v E (set_add dec_eq c s)); ff l.
          + nodups.
          + incls.
          + incls.
        }
        destruct (dec_eq v c'); ff.
        ++ (* v = c' *)
          exists c'; split; ff.
          eapply get_one_get_multi'; ff l.
          + nodups.
          + incls.
        ++ (* v <> c' *)
        exists v.
        split; ff.
        eapply IHn.
        + nodups.
        + erewrite length_set_add; ff l.
        + incls.
        + ff.
        + eapply (get_one_get_multi' (S n0) c' c'' E (set_add dec_eq v (set_add dec_eq c s))); ff l.
          -- nodups.
          -- unfold incl; ff.
            repeat (erewrite length_set_add; ff l).
          -- incls.
          -- incls.
        + nodups.
        + incls.
        + incls.
      * destruct (in_dec dec_eq c'' (get_all_one_step_reverse E c)); ff.
        right.
        assert (Hinvs : ~ In v s). {
          intros HC.
          eapply (not_in_self _ _ E (set_add dec_eq c s)); ff l.
          + nodups.
          + incls.
          + incls.
        }
        assert (Hinv0s : ~ In v0 s'). {
          intros HC.
          eapply (not_in_self _ v0 E (set_add dec_eq c' s')); ff l.
          + nodups.
          + incls.
          + incls.
        }
        destruct (dec_eq v c'); ff.
        ++ (* v = c' *)
          exists c'; split; ff.
          eapply IHn.
          + nodups.
          + erewrite length_set_add; ff l.
          + incls.
          + eapply get_one_get_multi'; ff l.
            -- nodups.
            -- incls.
          + ff.
          + nodups.
          + incls.
          + incls.
        ++ (* v <> c' *)
        destruct (in_dec dec_eq v s').
        ---- 
        exists v.
        split; ff.
        eapply IHn.
        + nodups.
        + erewrite length_set_add; ff l.
        + incls.
        + ff.
        + 
          eapply (IHn c' v0 E (set_add dec_eq v (set_add dec_eq c s))); ff l.
          -- nodups.
          -- repeat (erewrite length_set_add; ff l).
          -- incls.
          -- eapply get_one_get_multi'.
            +++ nodups.
            +++ repeat (erewrite length_set_add; ff l).
            +++ incls.
            +++ incls.
            +++ incls.
          -- nodups.
          -- incls.
            (* repeat (erewrite set_add_iff in * ).
            destruct H3 as [? | [? | ?]].
            *** admit.
            *** ff.
            *** ff. *)
          -- incls.
        + nodups.
        + incls.
        + incls.
        ---- (* ~ In v s' *)
        setoid_rewrite set_add_iff in Hss'E.
        assert (In c s') by ff.

        (* destruct (in_dec dec_eq c' (get_all_one_step_reverse E c)).
        +++

        assert (In c' (get_multi_step_reverse' c E s)) by admit.
        assert (In c'' (get_multi_step_reverse' c' E (set_add dec_eq c s))) by admit.
        exists c'.
        split; ff.
        +++  *)

        exists v.
        split; ff.

        eapply IHn.
        + nodups.
        + erewrite length_set_add; ff l.
        + incls.
        + ff.
        + 
          eapply (IHn c' v0 E (set_add dec_eq c s)); ff l.
          -- nodups.
          -- repeat (erewrite length_set_add; ff l).
          -- incls.
          -- eapply get_one_get_multi'.
            ++++ nodups.
            ++++ repeat (erewrite length_set_add; ff l).
            ++++ incls.
            ++++ incls.
            ++++ incls.
          -- nodups.
          -- incls.
            (* repeat (erewrite set_add_iff in * ).
            destruct H3 as [? | [? | ?]].
            *** admit.
            *** ff.
            *** ff. *)
          -- incls.
        + nodups.
        + incls.
          admit.
        + incls.
  Admitted.

End Sets.

Arguments get_all_one_step_reverse {A} _ _.
Arguments get_multi_step_reverse {A} _ _.