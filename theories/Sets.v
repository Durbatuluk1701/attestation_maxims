From Equations Require Import Equations.
From RocqCandy Require Import All.
Import MapNotations.
From Stdlib Require Import List String.
From Stdlib Require Export ListSet.
Local Open Scope map_scope.

Section Sets.

  Context (A : Type) `{DK : DecEq A}.

  Definition union {A} `{DecEq A} := set_union dec_eq.
  Definition add {A} `{HDA : DecEq A} := set_add dec_eq.
  Definition mem {A} `{HDA : DecEq A} := set_mem dec_eq.

  Definition bin_rel := set (A * A).

  Fixpoint all_in_rel (d : bin_rel) : set A :=
    match d with
    | [] => nil
    | (c1, c2) :: rest => 
      union (c1 :: c2 :: nil) (all_in_rel rest)
    end.

  Fixpoint get_all_one_step_reverse (d : bin_rel) (c : A) : set A :=
    match d with
    | [] => nil
    | (c1, c2) :: rest =>
        if dec_eq c2 c then add c1 (get_all_one_step_reverse rest c)
        else get_all_one_step_reverse rest c
    end.

  Lemma not_set_In_add : forall {A} `{DecEq A} s (a : A),
    ~ set_In a s ->
    List.length (add a s) = S (List.length s).
  Proof.
    induction s; ff.
    - edestruct H0; ff.
  Qed.

  Equations? get_multi_step_reverse' (c : A) (rel : set (A * A)) (seen : set A) : set A
      by wf (List.length (all_in_rel rel) - List.length seen) :=
  get_multi_step_reverse' c rel seen :=
    match (List.length (all_in_rel rel) - List.length seen) as n return (List.length (all_in_rel rel) - List.length seen = n -> _) with
    | 0 => fun Hm => nil
    | S _ =>
      fun Hm =>
      match (set_In_dec (DecEq.dec_eq) c seen) with
      | left _ => nil
      | right _ =>
        let parents := get_all_one_step_reverse rel c in
        set_fold_left 
          (fun (acc : set A) c' => union acc (get_multi_step_reverse' c' rel (add c seen)))
          parents
          parents
      end
    end eq_refl.
  Proof.
    erewrite not_set_In_add; ff l.
  Defined.

  Definition get_multi_step_reverse (c : A) (d : bin_rel) : set A :=
    get_multi_step_reverse' c d nil.

  
  Lemma in_acc_impl_in_set_fold_union : forall {A} `{HD : DecEq A} (f : A -> set A) (lst : list A) (x : A) (acc : set A),
    (In x acc) ->
    In x (fold_left (fun acc a => set_union dec_eq acc (f a)) lst acc).
  Proof.
    induction lst; ff.
    eapply IHlst; 
    erewrite set_union_iff; ff.
  Qed.

  Lemma set_in_fold_left_union : forall (f : A -> set A) (lst : list A) (x : A) (acc : set A),
    In x (fold_left (fun acc a => set_union dec_eq acc (f a)) lst acc) <->
    (* either in acc to start or in f a*)
    (In x acc) \/ (exists a, In a lst /\ set_In x (f a)).
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

  Lemma set_In_add_split : forall (c c' : A) s,
    set_In c (add c' s) -> c = c' \/ set_In c s.
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
    unfold union. induction s; ff.
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
      ltac1:(simp get_multi_step_reverse' in *); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in *); ff.
        rewrite Nat.sub_0_r in Heqn. pp (union_non_empty_len [a; c] (all_in_rel E)); ff l.
        rewrite Nat.sub_0_r in Heqn. pp (union_non_empty_len [a; c] (all_in_rel E)); ff l.
        rewrite Nat.sub_0_r in Heqn. pp (union_non_empty_len [a; a0] (all_in_rel E)); ff l.
  Qed.

  Lemma all_in_rel_empty : forall E,
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
  Qed.

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

  Lemma expand_dep_rel_test : forall n E sn,
    List.length (all_in_rel E) - List.length sn <= n ->
    forall c c',
    In c (get_multi_step_reverse' c' E sn) ->
    forall a,
    In c (get_multi_step_reverse' c' (a :: E) sn).
  Proof.
    induction n; ff.
    - ltac1:(simp get_multi_step_reverse' in *); ff.
      * Search (set_union _ _ _ _).

  Lemma expand_dep_rel_test : forall E,
    forall c c',
    In c (get_multi_step_reverse c' E) ->
    forall a,
    In c (get_multi_step_reverse c' (a :: E)).
  Proof.

    intros; ff.
    try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff);
    try (rewrite Nat.sub_0_r in * ); try (find_eapply_lem_hyp union_non_empty_len; ff);
    try (find_eapply_lem_hyp all_in_rel_empty_len; ff);
    try (find_eapply_lem_hyp length_zero_iff_nil; ff).
    - admit.
    - admit.
  Admitted.

  (* maybe try writing a lemma for when only one component is in the seen set *)


  Lemma expand_dep_rel : forall E E',
    (forall x, In x E -> In x E') ->
    forall c c',
    In c (get_multi_step_reverse c' E) ->
    In c (get_multi_step_reverse c' E').
  Proof.
    induction E'; ff.
    try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff).
    destruct H0; ff.
    - apply in_dep_rel_one_step in H0. eapply H. apply H0.
    - apply in_dep_rel_one_step in H0. eapply H. apply H0.
    - destruct a. destruct (dec_eq c' a0).
      + inversion e; ff. destruct (dec_eq c a0); ff.
        * admit.
        * admit.
      + admit.
      (* try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff);
      try (rewrite Nat.sub_0_r in * ); try (find_eapply_lem_hyp union_non_empty_len; ff);
      try (find_eapply_lem_hyp all_components_empty_len; ff);
      try (find_eapply_lem_hyp length_zero_iff_nil; ff).

    induction E; ff. inversion H0.
      try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff);
      try (rewrite Nat.sub_0_r in * ); try (find_eapply_lem_hyp union_non_empty_len; ff);
      try (find_eapply_lem_hyp all_components_empty_len; ff);
      try (find_eapply_lem_hyp length_zero_iff_nil; ff).
      + apply IHE; ff.
        * apply IHE'; ff. admit.
        * 
    
    try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff);
      try (rewrite Nat.sub_0_r in * ); try (find_eapply_lem_hyp union_non_empty_len; ff);
      try (find_eapply_lem_hyp all_components_empty_len; ff);
      try (find_eapply_lem_hyp length_zero_iff_nil; ff).
      destruct H0; ff.
      + apply in_dep_rel_one_step in H0.
        pp (H _ H0). elim_contras H0; ff.
      + 
      destruct E. admit.


    *)
    (* induction E; ff.
    - unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff.
    - try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff);
      try (rewrite Nat.sub_0_r in * ); try (find_eapply_lem_hyp union_non_empty_len; ff);
      try (find_eapply_lem_hyp all_components_empty_len; ff);
      try (find_eapply_lem_hyp length_zero_iff_nil; ff).
      + elim_contras H0; ff. 
        * left.
          pp (H _ (or_introl eq_refl)).
          apply in_dep_rel_one_step; ff.
        * ltac1:(simp get_multi_step_reverse' in H1); ff. exfalso; ff.
      + elim_contras H0; ff.
        * apply set_add_elim in hc; unfold set_In in *; ff.
          pp (H _ (or_introl eq_refl)).
          destruct (dec_eq c c0); ff.
          -- left.
            apply in_dep_rel_one_step; ff.
          -- apply in_dep_rel_one_step in H0. right. exists c0; split; ff.
          left. admit.
        * admit.
      + elim_contras H0; ff.
        * left. admit.
        * pp (H _ (or_introl eq_refl)); ff. *)
  
  Admitted.


  Lemma get_one_step_one_step_trans : forall c c' E,
    In c' (get_all_one_step_reverse E c) -> c' <> c ->
    forall c'',
      c'' <> c -> c'' <> c' ->
      In c'' (get_all_one_step_reverse E c') ->
      In c'' (get_multi_step_reverse c E).
  Proof.
    induction E; ff.
  Admitted.
  (* 

    try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff; try (rewrite Nat.sub_0_r in * ); find_eapply_lem_hyp union_non_empty_len; ff).
    - pp (IHE H H0 c'' H1 H2).
      ff.
      try (unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff);
      try (rewrite Nat.sub_0_r in * ); try (find_eapply_lem_hyp union_non_empty_len; ff).
      + find_eapply_lem_hyp all_in_rel_empty_len; ff.
        find_eapply_lem_hyp length_zero_iff_nil; ff.
      + right. exists c'; split; ff.
        try (ltac1:(simp get_multi_step_reverse' in * ); ff; unfold set_fold_left in *; unfold union in *; try (erewrite set_in_fold_left_union in * ); ff).
        assert (Datatypes.length [c0; c'] = 2).
        * simpl. reflexivity.
        * assert (2 <= Datatypes.length (set_union dec_eq [c0; c'] (all_in_rel E))). rewrite <- H5. apply union_non_empty_len_more.
            lia.
    - destruct (dec_eq c' c0); ff.
      + admit.
      + assert (In c' (get_all_one_step_reverse E c)).
        apply set_add_elim in H. destruct H; ff.
        pp (IHE H4 H0 c'' H1 H2 H3). admit.
    - admit.
  Admitted.
  *)


  Lemma get_one_step_multi_step_trans : forall c c' E,
    In c' (get_all_one_step_reverse E c) ->
    forall c'',
      In c'' (get_multi_step_reverse c' E) ->
      In c'' (get_multi_step_reverse c E).
  Proof.
    induction E; ff.
    unfold get_multi_step_reverse in *; ltac1:(simp get_multi_step_reverse' in *); ff; unfold set_fold_left in *; unfold union in *; erewrite set_in_fold_left_union in *.
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
    ltac1:(simp get_multi_step_reverse' in *); ff.
    - rewrite Nat.sub_0_r in Heqn. apply union_non_empty_len in Heqn; ff.
    - unfold set_fold_left in *; unfold union in *; erewrite set_in_fold_left_union in *.
      destruct (dec_eq c'' a0); ff.
    - unfold set_fold_left in *; unfold union in *; erewrite set_in_fold_left_union in *.
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

  Lemma get_multi_step_reverse_trans : forall c c' E s,
    In c' (get_multi_step_reverse' c E s) ->
    forall c'',
      In c'' (get_multi_step_reverse' c' E s) ->
      In c'' (get_multi_step_reverse' c E s).
  Proof.
    induction E; ff.
    ltac1:(simp get_multi_step_reverse' in *); ff; unfold set_fold_left in *; unfold union in *; erewrite set_in_fold_left_union in *; ff.
    - destruct H; destruct H0.
      + right. exists c'. split; auto.
        ltac1:(simp get_multi_step_reverse' in *); ff; unfold set_fold_left in *; unfold union in *; ff.


  (*
          rewrite H1 in Heqn3. clear H1.

            --
            -- destruct (dec_eq c0 c).
              ++ subst. unfold union in *. simpl in *. admit.
              ++ admit.
            -- apply set_In_add_split in s0; destruct s0; ff.
            -- unfold set_fold_left in *. unfold union in *. erewrite set_in_fold_left_union in *. ff.
      + admit.
      + destruct H. right. exists x. split; auto; destruct H; auto.
        pp (IHE (add c s)).  admit.
      + admit.
    - unfold set_fold_left in *.
      unfold union in *.

      admit.
    - admit.
            *)
  Admitted.

End Sets.

Arguments get_all_one_step_reverse {A} _ _.
Arguments get_multi_step_reverse {A} _ _.