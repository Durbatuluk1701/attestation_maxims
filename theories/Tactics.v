From RocqCandy Require Export All.
Local Open Scope map_scope.

Ltac2 rec elim_contras (h : ident) :=
  cbn in $h;
  let hv := Control.hyp h in
  match! Constr.type hv with
  | False => exfalso; exact $hv
  | exists _, _ => 
    let v := fresh_hyp "v" in
    let hc := fresh_hyp "hc" in
    destruct $hv as [$v $hc] > [ elim_contras hc ]
  (* | forall _, _ =>
    printf "not handling foralls yet: %I: %t" h hv *)
  | _ \/ _ =>
    let hc1 := fresh_hyp "hc" in
    let hc2 := fresh_hyp "hc" in
    destruct $hv as [$hc1 | $hc2] 
    > [ elim_contras hc1 | elim_contras hc2 ]
  | _ /\ _ =>
    let hc1 := fresh_hyp "hc" in
    let hc2 := fresh_hyp "hc" in
    destruct $hv as [$hc1 $hc2]; 
    Control.enter (fun () => elim_contras hc1; elim_contras hc2)
  | _ => 
    (* default case, needs to be solvable *)
    try (simple congruence 1; 
    (* if not solved, go to the bigger guns *)
    congruence)
  end.

Ltac2 Notation "elim_contras" h(ident) := elim_contras h.

Ltac2 Notation "elim_all_contras" :=
  List.iter 
    (fun (h, _, _) => Control.enter (fun () => elim_contras $h)) 
    (Control.hyps ()).

Ltac2 rec get_forall_var_names (h : constr) : ident list :=
  match! h with
  | forall _ : _, _ =>
    match Constr.Unsafe.kind h with
    | Unsafe.Prod bnd rst => 
      let rest : ident list := get_forall_var_names rst in
      match Binder.name bnd with
      | Some i => i :: rest
      | None => 
        match Ident.of_string "H" with
        | Some id => id :: rest
        | None => Control.zero (Tactic_failure None)
        end
      end
    | _ => Control.zero (Tactic_failure None)
    end
  | _ => []
  end.

Ltac2 get_forall_var_name (h : constr) : ident :=
  match get_forall_var_names h with
  | [] => Control.zero (Tactic_failure None)
  | x :: _ => x
  end.

Ltac2 rec bool_logic tac :=
  match! goal with
  | [ |- ~ _ ] => 
    let hc := fresh_hyp "HC" in
    intro $hc; Control.enter 
      (fun () => elim_contras $hc; repeat find_injection)
  | [ |- forall _, _ ] => 
    let v := get_forall_var_name (Control.goal ()) in
    let x := fresh_hyp (Ident.to_string v) in
    intros $x; 
    (* try to contradict the hypothesis *)
    Control.enter (fun () => elim_contras $x; repeat find_injection);
    Control.enter (fun () => bool_logic tac)
  | [ |- exists _, _ ] => eexists; bool_logic tac
  | [ |- _ /\ _ ] => 
    (* we really only want to split if both sides get solved *)
    split; solve [ Control.enter (fun () => bool_logic tac) ]
  | [ |- _ \/ _ ] => 
    try (left; bool_logic tac; fail);
    try (right; bool_logic tac; fail)
  | [ |- match ?v with _ => _ end ] =>
    let h := fresh_hyp "Heq" in
    destruct $v eqn:$h; 
    (* Try to rewrite it everywhere *)
    Control.enter (fun () => 
      let hv := Control.hyp h in
      try (erewrite $hv in *)
    ); 
    (* Do all injections *)
    Control.enter (fun () => 
      try find_injection
    );
    (* Since we created goals, do contra elimination *)
    Control.enter (fun () => elim_all_contras);
    (* Continue *)
    Control.enter (fun () => bool_logic tac)
  | [ |- _ ] => (* default case, use tac *) 
    try (tac ());
    (* if not done, do a cbn and continue *)
    try (
      progress (fun () => cbn);
      (* only continue if cbn simplified *)
      bool_logic tac
    )
  end.

Ltac2 Notation "bool_logic" 
  tac(opt(seq("with", thunk(tactic)))) := 
  match tac with
  | Some t => (bool_logic t)
  | None => (* default to reflexivity *)
    (bool_logic (fun () => try (ltac1:(eassumption)); reflexivity))
  end.

Ltac2 dec_map_lookup () :=
  ff;
  repeat (match! goal with
    | [ h : context [ lookup ?_x (insert ?_x _ _) ] |- _ ] =>
      erewrite lookup_insert_eq in $h; ff
    | [ h : context [ lookup ?_x (insert ?_y _ _) ] |- _ ] =>
      erewrite lookup_insert_neq in $h; ff
    | [ h : context [lookup _ (map_Map _ _)] |- _ ] =>
      erewrite lookup_map_Map in $h; ff
    | [ |- context [ lookup ?_x (insert ?_x _ _) ]] =>
      erewrite lookup_insert_eq; ff
    | [ |- context [ lookup ?_x (insert ?_y _ _) ]] =>
      erewrite lookup_insert_neq; ff
    | [ |- context [lookup _ (map_Map _ _)] ] =>
      erewrite lookup_map_Map; ff
    end).

Ltac2 Notation "dec_map_lookup" := dec_map_lookup ().

Lemma length_insert : forall {A B} `{DecEq A} (m : Map A B) k v,
  List.length (insert k v m) = 
    match lookup k m with
    | Some _ => List.length m
    | None => S (List.length m)
    end.
Proof.
  induction m; ff; erewrite IHm; ff.
Qed.

Lemma length_map_Map : forall {A B C} (f : A -> B -> C) (m : Map A B),
  List.length (map_Map f m) = List.length m.
Proof.
  induction m; ff.
Qed.

Ltac2 Notation "map_len_simpl" :=
  repeat (
    match! goal with
    | [ h : context [ List.length (insert ?_x _ _) ] |- _ ] =>
      erewrite length_insert in $h; ff l
    | [ |- context [ List.length (insert ?_x _ _) ] ] =>
      erewrite length_insert; ff l
    | [ h : context [ List.length (map_Map _ _ )] |- _ ] =>
      erewrite length_map_Map in $h; ff l
    | [ |- context [ List.length (map_Map _ _ )] ] =>
      erewrite length_map_Map; ff l
    end
  ); ff l.



Ltac2 rec find_relevant_entry (comp : constr) (vl : constr) :=
  match! vl with
  | nil => Control.zero (Tactic_failure None)
  | ((?c, (?c_stat, ?c_typ, ?c_next_cor)) :: ?rest) =>
    (* check if the head matches *)
    if Constr.equal comp c
    then (c_stat, c_typ, c_next_cor)
    else find_relevant_entry comp rest
  end.

Ltac2 Notation "find_relevant_entry" comp(constr) map(constr) := 
  find_relevant_entry comp map.

Ltac2 Notation "fwd" :=
  match! goal with
  | [ h : ?h1 -> ?_h2 |- _ ] =>
    let ha := fresh_hyp "Ha" in
    assert ($h1) as $ha by bool_logic; 
    let hv := Control.hyp h in
    let hav := Control.hyp ha in
    pp ($hv $hav); clear $h $ha
  end.
