From Equations Require Import Equations.
From RocqCandy Require Import All.
Import MapNotations.
From Stdlib Require Import List String.
From AttestationMaxims Require Import Tactics Sets.
Local Open Scope map_scope.

Definition Component := string.
Global Instance DecEq_Component : DecEq Component.
unfold Component.
econstructor.
ref (string_dec).
Qed.

Definition Label := string.
Global Instance DecEq_Label : DecEq Label.
unfold Label.
econstructor.
ref (string_dec).
Qed.

Definition DependencyRel := bin_rel Component.

Inductive time := 
| LaunchTime
| Runtime.
Global Instance DecEq_time : DecEq time.  build_deq.  Qed.

Inductive event :=
| SysInit
| Start
| End
| Launch (c : Component)
| Meas (c : Component) (tm : time)
| Corrupt (c : Component) (l : Label) (tm : time)
| Repair (c : Component) (l : Label) (tm : time)
| Infect (c1 c2 : Component) (l : Label) (tm : time)
| SysDone (c : Component).

Global Instance DecEq_event : DecEq event.
econstructor.
unfold IDecEq in *; ff.
destruct v1, v2; ff a;
try (destruct (dec_eq c c0); ff);
try (destruct (dec_eq l l0); ff);
try (destruct (dec_eq c1 c0); ff);
try (destruct (dec_eq c2 c3); ff);
try (destruct (dec_eq tm tm0); ff).
Qed.

Definition trace := list event.

Fixpoint index_of (fn : event -> bool) (tr : trace) : option nat :=
  match tr with
  | [] => None
  | e' :: rest =>
      if fn e' then Some 0
      else
        match index_of fn rest with
        | None => None
        | Some n => Some (S n)
        end
  end.

Definition valid_trace (tr : trace) : Prop :=
  (* ordering makes sense *)
  (exists init_to_start start_to_end end_to_done sec_goal,
    tr = SysInit :: init_to_start ++ Start :: start_to_end ++ End :: end_to_done ++ [SysDone sec_goal]
  (* special events not in between - init_to_start *)
  /\ (~ In SysInit init_to_start)
  /\ (~ In Start init_to_start)
  /\ (~ In End init_to_start)
  /\ (~ exists c, In (SysDone c) init_to_start)
  (* special events not in between - start_to_end *)
  /\ (~ In SysInit start_to_end)
  /\ (~ In Start start_to_end)
  /\ (~ In End start_to_end)
  /\ (~ exists c, In (SysDone c) start_to_end)
  (* special events not in between - end_to_done *)
  /\ (~ In SysInit end_to_done)
  /\ (~ In Start end_to_done)
  /\ (~ In End end_to_done)
  /\ (~ exists c, In (SysDone c) end_to_done)
  ).

Global Instance DecEq_set {A} `{DecEq A} : DecEq (set A).
build_deq.
Qed.

Inductive state :=
| Cor (x : set Component)
| Safe.
Global Instance DecEq_state : DecEq state.
destruct (@DecEq_set Component DecEq_Component).
econstructor.
unfold IDecEq in *.
ff.
destruct v1, v2; ff a.
destruct (dec_eq x x0); ff.
Qed.

Definition state_union (s1 s2 : state) : state :=
  match s1, s2 with
  | Safe, Safe => Safe
  | Cor x1, Cor x2 => Cor (union x1 x2)
  | Cor x, Safe => Cor x
  | Safe, Cor x => Cor x
  end.

Inductive status :=
| Launched (cor_state : state)
| NotLaunched.
Global Instance DecEq_status : DecEq status. 
econstructor.
unfold IDecEq in *; ff.
destruct v1, v2; ff a.
destruct (dec_eq cor_state cor_state0); ff.
Qed.

Inductive protocol_state :=
| UnInit
| Running (meas_map : Map Component state)
| Concluded (p : bool).

Global Instance DecEq_protocol_state : DecEq protocol_state.
destruct (@DecEq_set (Component * state) _).
econstructor.
unfold IDecEq in *.
ff.
destruct v1, v2; ff a.
destruct (dec_eq meas_map meas_map0); ff.
destruct p, p0; try (destruct b, b0); ff.
Qed.

Inductive ty :=
| Secret
| Short
| Long.
Global Instance DecEq_ty : DecEq ty.  build_deq.  Qed.

Inductive vertex := 
| vert : 
  status (** Is it launched *)
  -> ty (** Is it Short or Long-lived *)
  -> state (** The corruption state: relevant to next launch *)
  -> vertex.

Global Instance DecEq_vertex : DecEq vertex.
econstructor.
unfold IDecEq in *; ff.
destruct v1, v2; ff a.
destruct (dec_eq s s1); ff.
ltac1:(destruct (dec_eq t t0)); ff.
destruct (dec_eq s0 s2); ff.
Qed.

Fixpoint valid_trace_with_filters V E 
    (filter_fns : list (Map Component vertex -> DependencyRel -> trace -> Prop)) (tr : trace) : Prop :=
  match filter_fns with
  | [] => valid_trace tr
  | fn :: rest => fn V E tr /\ valid_trace_with_filters V E rest tr
  end.


Definition forall_mentioned_components (tr : trace) (P : Component -> Prop) : Prop :=
  forall c,
    (
      In (Launch c) tr
      \/ (exists tm, In (Meas c tm) tr) 
      \/ (exists l tm, In (Corrupt c l tm) tr) 
      \/ (exists l tm, In (Repair c l tm) tr)
      \/ (exists l tm, exists c2, In (Infect c c2 l tm) tr)
      \/ (exists l tm, exists c2, In (Infect c2 c l tm) tr)
    )
    -> P c.

Create HintDb trace_pols.
Local Hint Unfold forall_mentioned_components : trace_pols.

Definition DecTrust (mmap : Map Component state) (dep_rel : DependencyRel) : bool :=
  (* TODO: Is this too simplistic!? *)
  List.fold_left (fun acc entry =>
    let '(c, st) := entry in
    (* We need to unwrap the acc *)
    match st with
    | Cor _ => false
    | Safe => acc
    end
  ) mmap true.

Inductive trust_state :=
| Trusted
| Untrusted.

Definition system_graph : Type := 
  (Map Component vertex) * protocol_state * trust_state.

Equations? trustworthy' (c : Component) (seen : set Component)
    (m : Map Component vertex) (dep_rel : DependencyRel) 
    : Prop
    by wf (List.length m - List.length seen) :=
trustworthy' c seen m dep_rel :=
  match (List.length m - List.length seen) as n return (List.length m - List.length seen = n -> _) with
  | 0 => fun Hm => True (* I guess, idk this should really never happen *)
  | S _ =>
  fun Hm =>
  match (set_In_dec (DecEq.dec_eq) c seen) with
  | left _ => True
  | right _ =>
    (match m ![ c ] with
    | None => False
    | Some (vert lstat _ next_cor) =>
      match lstat with
      | NotLaunched | Launched Safe => 
        (match get_all_one_step_reverse _ dep_rel c with
        | nil => False
        | parents =>
          set_fold_left 
            (fun acc c' => acc /\ trustworthy' c' (add c seen) m dep_rel) 
            parents
            True
        end)
      | Launched (Cor _) => False
      end
    end)
    end
  end eq_refl.
Proof.
  erewrite not_set_In_add; ff l.
  erewrite not_set_In_add; ff l.
Defined.

Definition trustworthy (c : Component) (m : Map Component vertex) (dep_rel : DependencyRel) : Prop :=
  trustworthy' c nil m dep_rel.

Theorem trustworthy_dec : forall c m dep_rel,
  { trustworthy c m dep_rel } + { ~ trustworthy c m dep_rel }.
Proof.
Admitted.


Definition measure (tm : time) (c : Component) 
    (V : Map Component vertex) : state :=
  match V ![ c ] with
  | None => Safe
  | Some (vert lstat ty next_cor) =>
    match ty with
    | Secret => Safe
    | Short | Long =>
      match tm with
      | LaunchTime => next_cor
        (* measurement at launch time, so look at launch cor state *)
      | Runtime =>
        match lstat with
        | Launched r_cor => r_cor
        | NotLaunched => Safe
        end
      end
    end
  end.

Reserved Notation "x -[ e ]-> y" (at level 50).

Section Transitions.
  Variable E : DependencyRel.

  Inductive transition : system_graph -> event -> system_graph -> Prop :=
  | run_sys_init : forall V V' tst,
    (* We always start with Safe and NotLaunched *)
    V' = map_Map (fun k '(vert stat ty next_cor) => (vert NotLaunched ty Safe)) V ->
    (V, UnInit, tst) -[ SysInit ]-> (V', UnInit, tst)

  | run_start : forall V tst,
    (V, UnInit, tst) -[ Start ]-> (V, Running (empty_set _), tst)

  | run_end : forall V mmap dec tst,
      DecTrust mmap E = dec ->
    (V, Running mmap, tst) -[ End ]-> (V, Concluded dec, tst)

  | run_launch : forall V PS c stat ty next_cor tst V',
      V ![ c ] = Some (vert stat ty next_cor) ->
      V' = V ![ c := (vert (Launched next_cor) ty next_cor) ] ->
    (V, PS, tst) -[ Launch c ]-> (V', PS, tst)

  | run_meas : forall V mmap c stat tm ty next_cor mmap' tst,
      V ![ c ] = Some (vert stat ty next_cor) ->
      mmap' = mmap ![ c := measure tm c V ] ->
    (V, Running mmap, tst) -[ Meas c tm ]-> (V, Running mmap', tst)

  | run_corrupt : forall V PS c l tm tst stat ty next_cor V',
      V ![ c ] = Some (vert stat ty next_cor) ->
      V' = V ![ c := 
      match tm with
      | LaunchTime => (vert stat ty (state_union (Cor [l]) next_cor))
      | Runtime => 
        match stat with
        | NotLaunched => (vert stat ty next_cor)
          (* can't corrupt unlaunched at runtime *)
        | Launched running_cors =>
            (vert (Launched (state_union (Cor [l]) running_cors)) ty next_cor)
        end
      end
    ] ->
    (V, PS, tst) -[ Corrupt c l tm ]-> (V', PS, tst)

  | run_repair : forall V PS c l tm stat ty next_cor V' tst,
      V ![ c ] = Some (vert stat ty next_cor) ->
      V' = V ![ c := (
        match tm with
        | LaunchTime => 
          match next_cor with
          | Safe => (vert stat ty Safe)
          | Cor lst => 
              (vert stat ty
                match filter (fun x => if dec_eq x l then false else true) lst with
                | nil => Safe
                | lst' => Cor lst'
                end)
          end
        | Runtime => 
          match stat with
          | NotLaunched => (vert stat ty next_cor) (* can't repair unlaunched *)
          | Launched run_cor =>
              match run_cor with
              | Safe => (vert stat ty Safe)
              | Cor lst =>
                  (vert (Launched (
                    match filter (fun x => if dec_eq x l then false else true) lst with
                    | nil => Safe
                    | lst' => Cor lst'
                    end))
                   ty
                   next_cor)
              end
          end
        end
      )] ->
    (V, PS, tst) -[ Repair c l tm ]-> (V' , PS, tst)

  | run_infect : forall V PS c1 c2 l tm stat1 ty1 stat2 ty2 next_cor1 next_cor2 V' tst,
      V ![ c1 ] = Some (vert stat1 ty1 next_cor1) ->
      (* c1 is corrupted with "l" *)
      match stat1 with
      | NotLaunched => False (* can't infect if not launched *)
      | Launched st1 => 
        match st1 with
        | Safe => False (* can't infect if not corrupted *)
        | Cor run_cors => mem l run_cors = true
        end
      end ->
      V ![ c2 ] = Some (vert stat2 ty2 next_cor2) ->
      set_In c1 (get_multi_step_reverse _ c2 E) ->
      V' = V ![ c2 := (
        match tm with
        | LaunchTime => (vert stat2 ty2 (state_union (Cor [l]) next_cor2))
        | Runtime =>
          match stat2 with
          | NotLaunched => (vert stat2 ty2 next_cor2) (* can't infect unlaunched *)
          | Launched run_cor2 =>
              (vert (Launched (state_union (Cor [l]) run_cor2)) ty2 next_cor2)
          end
        end
      )
      ] ->
    (V, PS, tst) -[ Infect c1 c2 l tm ]-> (V', PS, tst)
(* 
  | run_use : forall V PS V' c,
      (* I think it should ultimately be that launch < use? *)
      V' = V ![ c := 
        match V ![ c ] with
        | Some (s, st, ty) => (s, st, ty)
        | None => (Safe, NotLaunched, Short) (* default value if not present *)
        end ] ->
    (V, PS) -[ Use c ]-> (V', PS) 
*)

  | run_sys_done_trusted : forall V PS c tst,
      (* 
      if trustworthy c V 
      then Trusted
      else Untrusted
      *)
      trustworthy c V E ->
    (V, PS, tst) -[ SysDone c ]-> (V, PS, Trusted)

  | run_sys_done_untrusted : forall V PS c tst,
      (* 
      if trustworthy c V 
      then Trusted
      else Untrusted
      *)
      ~ (trustworthy c V E) ->
    (V, PS, tst) -[ SysDone c ]-> (V, PS, Untrusted)

  where "x -[ e ]-> y" := (transition x e y).

  Inductive runs : system_graph -> trace -> system_graph -> Prop :=
  | run_nil : forall sg, runs sg [] sg
  | run_cons : forall sg sg' sg'' e tr,
      sg -[ e ]-> sg' ->
      runs sg' tr sg'' ->
      runs sg (e :: tr) sg''.

End Transitions.

Lemma runs_app : forall E sg1 sg3 tr1 tr2,
  (exists sg2, runs E sg1 tr1 sg2 /\ runs E sg2 tr2 sg3)
  <-> runs E sg1 (tr1 ++ tr2) sg3.
Proof.
  intros.
  split; ff.
  - induction H; ff.
    econstructor; ff.
  - prep_induction H.
    induction H; ff.
    + destruct tr1; ff.
      exists sg; split; econstructor; ff.
    + destruct tr1; ff.
      * exists sg; split; econstructor; ff.
      * pp (IHruns _ _ eq_refl); ff.
        exists x; split; ff.
        econstructor; ff.
Qed.

Inductive valid_graph : Map Component vertex -> DependencyRel -> Prop :=
| vg_no_edges : forall x V, valid_graph (x :: V) nil
| vg_cons_edge : forall V E c1 c2,
    valid_graph V E ->
    In c1 (map fst V) ->
    In c2 (map fst V) ->
    valid_graph V ((c1, c2) :: E).
(* | vg_cons_vertex : forall V E x,
    valid_graph V E ->
    valid_graph (x :: V) E. *)

Lemma index_of_some : forall e tr n,
  index_of (fun v => if dec_eq e v then true else false) tr = Some n ->
  exists tr1 tr2,
    tr = tr1 ++ e :: tr2 /\
    n = List.length tr1.
Proof.
  induction tr; ff.
  - exists nil, tr; ff.
  - pp (IHtr _ eq_refl).
    clear IHtr.
    ff.
    exists (a :: x), x0; ff.
Qed.

Lemma transition_no_way_to_unconclude : forall E V ev V' PS' b tst tst',
  transition E (V, Concluded b, tst) ev (V', PS', tst') ->
  PS' = Concluded b.
Proof.
  induction ev; ff; try (invc H; ff; fail).
Qed.

Lemma runs_no_way_to_unconclude : forall tr E V V' PS' b tst tst',
  runs E (V, Concluded b, tst) tr (V', PS', tst') ->
  PS' = Concluded b.
Proof.
  induction tr; ff.
  - invc H; ff.
  - invc H; ff.
    destruct sg', p.
    eapply transition_no_way_to_unconclude in H3; ff.
Qed.

Theorem valid_trace_always_has_conclusion : forall tr,
  valid_trace tr ->
  forall V PS E V' PS' tst tst',
    runs E (V, PS, tst) tr (V', PS', tst') ->
    exists b, PS' = Concluded b.
Proof.
  intros.
  unfold valid_trace in H; ff.
  repeat (match! goal with
  | [ h : runs _ _ (_ :: _) _ |- _ ] => invc $h
  | [ h : runs _ _ (_ ++ _) _ |- _ ] => erewrite <- runs_app in $h; ff
  | [ h : transition _ _ _ _ |- _ ] => invc $h
  end).
  - invc H23; find_eapply_lem_hyp runs_no_way_to_unconclude; ff.
  - invc H23; find_eapply_lem_hyp runs_no_way_to_unconclude; ff.
Qed.

Definition corruption V E tst tr V' PS' tst' : Prop :=
  runs E (V, UnInit, tst) tr (V', PS', tst') /\ tst' = Untrusted.

Definition attested_good V E tst tr V' PS' tst' : Prop :=
  runs E (V, UnInit, tst) tr (V', PS', tst') /\ PS' = Concluded true.

(* An "attack" is a trace where corruption occur, but attestation says good *)
Definition attack V E tst tr V' PS' tst' : Prop :=
  corruption V E tst tr V' PS' tst' /\ attested_good V E tst tr V' PS' tst'.

(* Duel of "attack", caught means a trace corrupt **AND** attestation says bad *)
Definition caught V E tst tr V' PS' tst' : Prop :=
  corruption V E tst tr V' PS' tst' /\ (~ attested_good V E tst tr V' PS' tst').

Ltac2 Notation "inv_runs" :=
  repeat (
    match! goal with
    | [ h : runs _ _ (_ :: _) _ |- _ ] => invc $h
    | [ h : runs _ _ nil _ |- _ ] => invc $h
    | [ h : transition _ _ _ _ |- _ ] => invc $h
    end
  ).


Ltac2 Notation "dest_verts" :=
  repeat (
    match! goal with
    | [ h : (Component * vertex)%type |- _ ] => 
      let h := Control.hyp h in
      let c := fresh_hyp "c" in
      let stat := fresh_hyp "stat" in
      let typ := fresh_hyp "typ" in
      let next_cor := fresh_hyp "next_cor" in
      destruct $h as [$c [$stat $typ $next_cor]]
    | [ h : (vertex)%type |- _ ] => 
      let h := Control.hyp h in
      let stat := fresh_hyp "stat" in
      let typ := fresh_hyp "typ" in
      let next_cor := fresh_hyp "next_cor" in
      destruct $h as [$stat $typ $next_cor]
    end
  ).

Local Open Scope string_scope.

(* 
Lemma trustworthy_map_set : forall m k v,
  trustworthy (m ![ k := v ]) ->
  (match v with
    | (Launched (Cor _), _, _) => False
    | (_, _, _) => True
    end).
Proof.
  induction m; ff;
  find_eapply_lem_hyp IHm; ff.
Qed. *)
Ltac2 Notation "do_trustworthy" :=
  unfold trustworthy in *;
  ltac1:(simp trustworthy' in *); ff.

Ltac2 do_trans () := 
  match! goal with
  | [ |- transition ?e (?v, ?ps, ?tst) SysInit _ ] =>
    match! ps with
    | UnInit =>
      apply (run_sys_init $e $v 
        (map_Map (fun k '(vert stat ty next_cor) => (vert NotLaunched ty Safe)) $v) $tst
        eq_refl
      )
    | _ => printf "Found Protocol State: '%t' for SysInit, expected UnInit\n" ps; fail
    end

  | [ |- transition ?e (?v, ?ps, ?tst) Start _ ] =>
    match! ps with
    | UnInit => apply (run_start $e $v $tst)
    | _ => printf "Found Protocol State: '%t' for Start, expected UnInit\n" ps; fail
    end

  | [ |- transition _ (?v, Running ?mmap, _) (Meas ?_c _) _ ] =>
    eapply (run_meas _ $v $mmap); ff; solve [ dec_map_lookup | ff ]

  | [ |- transition _ (?_v, _, _) (Corrupt ?_c _ _) _ ] =>
    eapply run_corrupt > [ dec_map_lookup | ff ]; fail

  | [ |- transition _ (?_v, _, _) (Repair ?_c _ _) _ ] =>
    eapply run_repair; ff; solve [ dec_map_lookup | map_len_simpl ]

  | [ |- transition _ (?_v, _, _) (Infect ?_c1 ?_c2 _ _) _ ] =>
    eapply run_infect; ff; solve [ dec_map_lookup | map_len_simpl ]

  | [ |- transition _ (?_v, _, _) (Launch ?_c) _ ] =>
    eapply run_launch > [ dec_map_lookup | ff ]; fail

  | [ |- transition ?e (?v, Running ?mmap, ?tst) End _ ] =>
    eapply (run_end $e $v $mmap _ $tst); ff; fail

  | [ |- transition ?_e (?_v, ?_ps, ?_tst) (SysDone ?_c) _ ] =>
    (* need to try either method *)
    (* First, try untrustworthy *)
    orelse (fun () => 
      eapply run_sys_done_untrusted;
      do_trustworthy; solve [ map_len_simpl | dec_map_lookup ]
    )
    (fun _ => 
      eapply run_sys_done_trusted;
      do_trustworthy; solve [ map_len_simpl | dec_map_lookup ]
    )
  end.

Ltac2 Notation "do_trans" := do_trans ().

Ltac2 Notation "do_goal_run" :=
  try (unfold attack);
  try (unfold corruption);
  try (unfold attested_good);
  repeat eexists; ff;
  repeat (econstructor > [ do_trans | ]);
  try (unfold measure, DecTrust; ff; try (dec_map_lookup)); 
  econstructor.

Ltac2 rec list_split (f : constr -> bool) (lst : constr) :=
  match! lst with
  | nil => ('nil, 'nil)
  | ?hd :: ?tl =>
    if f hd
    then 'nil, '$tl
    else 
      let (h_rst, rst) := list_split f tl in
      '(cons $hd $h_rst), '$rst
  end.

Ltac2 Notation "do_trace" :=
  try (unfold valid_trace);
  match! goal with
  | [ |- exists i2s s2e e2d secgl, (?lst = SysInit :: _) /\ _ ] =>
    match! lst with
    | SysInit :: ?rest => 
      let (l, rst) := list_split (Constr.equal 'Start) rest in
      exists $l;
      let (l', rst') := list_split (Constr.equal 'End) rst in
      exists $l';
      let sec_goal := Ref.ref ('"a") in
      let (l'', _rst'') := list_split (fun x => 
        match! x with
        | SysDone ?sg => 
          Ref.set sec_goal '$sg;
          true
        | _ => false
        end) rst' in
      exists $l'';
      let sg_val := Ref.get sec_goal in
      exists $sg_val
    | _ => Control.zero (Tactic_failure None)
    end
  end;
  bool_logic.

Theorem corruptions_always_exist : forall V E tst,
  valid_graph V E ->
  exists tr, valid_trace tr /\ exists V' PS' tst', corruption V E tst tr V' PS' tst'.
Proof.
  intros.
  destruct V.
  ++ (* no components!? *)
    invc H; ff.
  ++ (* component "p" exists *)
  dest_verts.
  exists [SysInit; Start; Corrupt c "L" LaunchTime; Launch c; End; SysDone c].
  split; ff.
  - do_trace.
  - do_goal_run.
Qed.

Theorem attacks_always_exist : forall V E tst,
  valid_graph V E ->
  exists tr, valid_trace tr /\ exists V' PS' tst', attack V E tst tr V' PS' tst'.
Proof.
  intros.
  destruct V.
  ++ invc H; ff.
  ++ dest_verts.
    exists [SysInit; Start; Meas c LaunchTime; Corrupt c "L" LaunchTime; Launch c; End; SysDone c].
    split; ff.
    - do_trace.
    - do_goal_run.
Qed.

(* Maxim 1:  
"""
Constrain possible interactions so attested properties depend only on limited, predictable, measurable parts of the system.
"""

We encode this maxim into a trace policy "measure_before_done" which requires
that all components mentioned in the trace are measured before SysDone.
*)

(* 
This filters traces by whether or not they satisfy the 
default measurement policy of measuring all components before use.
*)
Definition measure_before_done (V : Map Component vertex) (E : DependencyRel) (tr : trace) : Prop :=
  (* implicitly, we should know that all meas < SysDone :
  since we know SysDone is always last. 

  So this really boils down to measuring all mentioned components.
  *)
  forall_mentioned_components tr (fun c =>
    (* We know the components are mentioned, so measures need to happen, and must come before use's *)
    exists tm, In (Meas c tm) tr
  ).

Local Hint Unfold measure_before_done : trace_pols.

Definition prevents_some_attacks 
    (Filt : Map Component vertex -> DependencyRel -> trust_state -> Prop)
    (pol1 pol2 : list (Map Component vertex -> DependencyRel -> trace -> Prop)) : Prop :=
  forall V E tst,
    Filt V E tst ->
    exists tr,
    (* There exists some trace "tr" s.t. pol2 invalidates it, but pol1 allows it, and it is an attack *)
      (~ (valid_trace_with_filters V E pol2 tr) 
      /\ valid_trace_with_filters V E pol1 tr 
      /\ exists V' PS' tst', attack V E tst tr V' PS' tst').

Definition default_Filt
    (V : Map Component vertex) (E : DependencyRel) (tst : trust_state) : Prop :=
  List.length V > 0.

Ltac2 Notation "do_trace_pol" :=
  ltac1:(autounfold with trace_pols in *); try (bool_logic);
  repeat (match! goal with
  | [ h : context[forall (_ : Component), _ ] |- _ ] =>
    apply_to_all_of_type 'Component (fun idnt =>
      Control.enter (fun () =>
        let hv := Control.hyp h in
        let idntv := Control.hyp idnt in
        pp ($hv $idntv)
      )
    ); clear $h
  end);
  repeat (
    match! goal with
    | [ h : ?h1 -> ?_h2 |- _ ] =>
      let ha := fresh_hyp "Ha" in
      assert ($h1) as $ha by bool_logic; 
      let hv := Control.hyp h in
      let hav := Control.hyp ha in
      pp ($hv $hav); clear $h $ha
    end; try (bool_logic); ff l
  ).

Lemma measurement_prevents_some_attacks : 
  prevents_some_attacks default_Filt [] [measure_before_done]. 
Proof.
  unfold default_Filt, prevents_some_attacks; ff.
  destruct V; ff l.
  dest_verts.
  exists 
    [SysInit; Start; Corrupt c "L" LaunchTime; Launch c; End; SysDone c].
    repeat (split; ff).
  - do_trace_pol.
  - do_trace.
  - do_goal_run.
Qed.


(* TODO: This line of reasoning needs to be restored! 

Theorem prevents_attacks_strengthens : forall h t,
  ~ (exists FV FE FT, prevents_some_attacks FV FE FT (h :: t) t).
Proof.
  intros.
  intros HC.
  unfold prevents_some_attacks in HC.
  ff.
  ff.
Qed.

Lemma measure_better_than_not : 
  ~ (prevents_some_attacks [measure_before_done] []).
Proof.
  eapply prevents_attacks_strengthens.
Qed.

*)

(** Maxim 2:
"""
Short-lived, single-input processes avoid the need for process runtime remeasurement that long-lived services require if they handle untrusted inputs. 
"""

We encode this maxim into a trace policy "no_runtime_corruption_on_short" which forbids
corruptions at runtime on short-lived components.

In particular, any short-lived component must be Launched after its measurement
*)

Definition no_runtime_corruption_on_short (V : Map Component vertex) 
    (E : DependencyRel) (tr : trace) : Prop :=
  forall_mentioned_components tr (fun c =>
    match V ![ c ] with
    | Some (vert stat ty next_cor) =>
      match ty with
      | Secret => True
      | Short =>
        (* If c is mentioned *)
        exists tm, 
          match index_of (fun ev => if dec_eq ev (Meas c tm) then true else false) tr with
          | Some meas_idx =>
            match index_of (fun ev => if dec_eq ev (Launch c) then true else false) tr with
            | Some launch_idx =>
              (* then the measurement happens before launch *)
              meas_idx < launch_idx
            | None => True (* if not launched, no problem *)
            end
          | None => False (* if not measured, problem *)
          end 
      | Long => True
      end
    | None => False (* how the heck is a mentioned component not present?! *)
    end
  ).

Local Hint Unfold no_runtime_corruption_on_short : trace_pols.

Theorem maxim_2_works : 
  prevents_some_attacks 
    (fun V E tst => default_Filt V E tst /\ exists c st nc, V ![ c] = Some (vert st Short nc))
    [] [no_runtime_corruption_on_short].
Proof.
  unfold default_Filt, prevents_some_attacks; ff.
  exists [SysInit; Start; Corrupt x "L" LaunchTime; Launch x; End; SysDone x].
  repeat (split; ff).
  - do_trace_pol.
  - do_trace.
  - do_goal_run.
Qed.

Theorem maxim_12_better_than_1 : 
  prevents_some_attacks 
    (fun V E tst => default_Filt V E tst /\ exists c st nc, V ![ c] = Some (vert st Short nc))
    [measure_before_done] [measure_before_done; no_runtime_corruption_on_short].
Proof.
  unfold default_Filt, prevents_some_attacks; ff.
  exists [SysInit; Start; Launch x; Meas x LaunchTime; Corrupt x "L" Runtime; End; SysDone x].
  repeat (split; ff).
  - do_trace_pol.
  - do_trace_pol.
  - do_trace.
  - do_goal_run.
Qed.

(** Maxim 3:
"""
Attestation should be independent of secrets that could be disclosed by transient corruptions, lest transient corruptions cause permanent attestation failure.
"""

We codify this maxim by saying any "component" that is of type "Secret" is always trustworthy (i.e. cannot be corrupted).
*)

Definition secrets_always_trustworthy (V : Map Component vertex) (E : DependencyRel) (tr : trace) : Prop :=
  forall_mentioned_components tr (fun c =>
    match V ![ c ] with
    | Some (vert stat ty next_cor) =>
      match ty with
      | Secret => 
        (* Secrets cannot be corrupted *)
        (~ exists l tm, In (Corrupt c l tm) tr) 
        /\ (~ exists l tm c', In (Infect c' c l tm) tr)
      | Short | Long => True
      end
    | None => True
    end
  ).

Local Hint Unfold secrets_always_trustworthy : trace_pols.

Theorem maxim_3_works : 
  prevents_some_attacks 
    (fun V E tst => default_Filt V E tst /\ exists c nst nnc, V ![ c ] = Some (vert nst Secret nnc))
    [] [secrets_always_trustworthy].
Proof.
  unfold default_Filt, prevents_some_attacks; ff.
  exists 
    [SysInit; Start; Corrupt x "L" LaunchTime; Launch x; End; SysDone x].
  repeat (split; ff).
  - do_trace_pol.
  - do_trace.
  - do_goal_run.
Qed.

Theorem maxim_123_better_than_12 : 
  prevents_some_attacks 
    (fun V E tst => default_Filt V E tst 
      /\ exists c nst nnc, V ![ c ] = Some (vert nst Secret nnc))
    [measure_before_done; no_runtime_corruption_on_short]
    [measure_before_done; no_runtime_corruption_on_short; secrets_always_trustworthy].
Proof.
  unfold default_Filt, prevents_some_attacks; ff.
  exists 
    [SysInit; Start; Corrupt x "L" LaunchTime; 
      (* This meas won't detect corr since its a secret *)
      Meas x LaunchTime; Launch x; End; SysDone x].
  repeat (split; ff).
  - do_trace_pol.
  - do_trace_pol.
  - do_trace_pol.
  - do_trace.
  - do_goal_run.
Qed.

(** Maxim 4:
"""
Each attestation must display characteristics showing that it originated from our uncorrupted attestation software, running under a trustworthy system boot. 
"""

This one is tough... skipping for now
*)

(** Maxim 5:
"""
An acyclic dependency relation enables us to measure lower layers before components depending on them. Only very recent corruptions of underlying components can then undermine attestations, meaning corruptions during the course of attestation. 
"""
*)

Definition no_cycles_in_dep_rel (V : Map Component vertex) (E : DependencyRel) (tr : trace) : Prop :=
  forall_mentioned_components tr (fun c =>
    ~ (set_In c (get_multi_step_reverse _ c E))).

Local Hint Unfold no_cycles_in_dep_rel : trace_pols.

Theorem maxim_5_works : 
  prevents_some_attacks (fun V E tst =>
    default_Filt V E tst /\ 
    (* Need two components for the cycle *)
    List.length V > 1 /\
    (exists c1 nst1 nt1 nnc1 c2 nst2 nt2 nnc2, 
      c1 <> c2 
      /\ V ![ c1 ] = Some (vert nst1 nt1 nnc1) 
      /\ V ![ c2 ] = Some (vert nst2 nt2 nnc2)
      /\ set_In c1 (get_multi_step_reverse _ c2 E)
      /\ set_In c2 (get_multi_step_reverse _ c1 E))
  ) [] [no_cycles_in_dep_rel].
Proof.
  unfold default_Filt, prevents_some_attacks; ff.
  exists 
    [SysInit; Start; Corrupt x "L" LaunchTime; Launch x; Infect x x3 "L" LaunchTime; Launch x3; End; SysDone x3].
  repeat (split; ff).
  - do_trace_pol.
    find_eapply_lem_hyp get_multi_step_reverse_trans; ff.
  - do_trace.
  - do_goal_run.
Qed.

Theorem maxim_1235_better_than_123 : 
  prevents_some_attacks (fun V E tst =>
    default_Filt V E tst /\ 
    (* Need two components for the cycle *)
    List.length V > 1 /\
    (exists c1 nst1 nt1 nnc1 c2 nst2 nt2 nnc2, 
      (* As long as two components exist that are cyclically dependent and not Secret (we need this since secret corruption makes picking a trace very hard) *)
      c1 <> c2 
      /\ nt1 <> Secret
      /\ V ![ c1 ] = Some (vert nst1 nt1 nnc1) 
      /\ nt2 <> Secret
      /\ V ![ c2 ] = Some (vert nst2 nt2 nnc2)
      /\ set_In c1 (get_multi_step_reverse _ c2 E)
      /\ set_In c2 (get_multi_step_reverse _ c1 E))
  )
  [measure_before_done; no_runtime_corruption_on_short; secrets_always_trustworthy]
  [measure_before_done; no_runtime_corruption_on_short; secrets_always_trustworthy; no_cycles_in_dep_rel].
Proof.
  unfold default_Filt, prevents_some_attacks; ff.
  exists 
    [SysInit; Start; Meas x LaunchTime; Corrupt x "L" LaunchTime; Launch x; Meas x3 LaunchTime; Infect x x3 "L" LaunchTime; Launch x3; End; SysDone x3].
  repeat (split; ff).
  - 
    ltac1:(autounfold with trace_pols in *); bool_logic.
    repeat (match! goal with
    | [ h : context[forall (_ : Component), _ ] |- _ ] =>
      apply_to_all_of_type 'Component (fun idnt =>
        Control.enter (fun () =>
          let hv := Control.hyp h in
          let idntv := Control.hyp idnt in
          pp ($hv $idntv)
        )
      ); clear $h
    end).
    repeat (fwd).
    printf "ugh".
    repeat (find_rewrite).
    elim_contras H6; repeat (find_injection).
    elim_contras H15; repeat (find_injection).
    elim_all_contras.
    printf "ugh 2".
    find_eapply_lem_hyp get_multi_step_reverse_trans; ff.
  - do_trace_pol.
  - do_trace_pol; subst_max; ff l.
  - do_trace_pol; subst_max; ff l.
  - do_trace.
  - do_goal_run.
Qed.

(** 
If we codify timely attacks and say they are not possible, then no attacks remain.
*)
Definition no_timely_attacks (V : Map Component vertex) (E : DependencyRel) (tr : trace) : Prop :=
  forall_mentioned_components tr (fun c =>
    (* A timely attack is one that occurs after the measurement *)
    ~ (exists mtm clab ctm,
      match 
        index_of (fun ev => if dec_eq ev (Meas c mtm) then true else false) tr,
        index_of (fun ev => if dec_eq ev (Corrupt c clab ctm) then true else false) tr 
      with
      | Some meas_idx, Some cor_idx =>
        meas_idx < cor_idx
      | Some _, None => (* measured, but never corrupted: Okay *) False
      | None, Some _ => (* corrupted but never measured: Bad *) True
      | None, None =>  (* neither measured nor corrupted: Bad *) True
      end
    )
  ).
Local Hint Unfold no_timely_attacks : trace_pols.

Lemma trustworthy'_builder : forall c V E sn,
  trustworthy' c sn V E ->
  forall f,
    (forall c v, 
      V ![ c ] = Some v ->
      (f c v = v \/ exists l1 l2, f c v = (vert l1 l2 Safe))) ->
    trustworthy' c sn (map_Map f V) E.
Proof.
  intros.
  ltac1:(simp trustworthy' in *); ff.
  try (erewrite length_map_Map in *; ff l).
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma map_Map_not_in : forall {A B} `{HD : DecEq A} (m : Map A B) c,
  ~ In c (map fst m) ->
  forall v',
  m = map_Map (fun k v => if dec_eq k c then v' else v) m.
Proof.
  induction m; ff.
  - pp (H (or_introl eq_refl)); ff.
  - erewrite <- IHm; ff.
Qed.

Lemma insert_to_map_Map : forall {A B} `{HD : DecEq A} (m : Map A B) k v v',
  NoDup (map fst m) ->
  m ![ k ] = Some v ->
  m ![ k := v' ] = map_Map (fun k' v'' => if dec_eq k' k then v' else v'') m.
Proof.
  induction m; ff.
  * invc H; ff.
    eapply map_Map_not_in in H2.
    erewrite <- H2.
    reflexivity.
  * erewrite <- IHm; ff.
    invc H; ff.
Qed.

Theorem trustworthy_change_transitions : forall ev V E PS tst V' PS' tst' c,
  NoDup (map fst V) ->
  trustworthy c V E ->
  ~ (trustworthy c V' E) ->
  transition E (V, PS, tst) ev (V', PS', tst') ->
  ((exists c' l tm, ev = Corrupt c' l tm /\ set_In c' (get_multi_step_reverse _ c E))
  \/ (exists (c' : Component), ev = Launch c /\ exists stat typ s, V ![ c ] = Some (vert stat typ (Cor s)))).
Proof.
  intros.
(*
  invc H2; Control.enter (fun () => bool_logic).
  * edestruct H1; clear H1. 
    unfold trustworthy in *.
    ltac1:(simp trustworthy' in * ); ff;
    try (erewrite length_map_Map in *; ff l);
    try (erewrite lookup_map_Map in *; ff).
    + admit.
    + admit.

  * right; ff.
  * split > [ reflexivity | ].
    admit.
  * edestruct H1; clear H1.
    erewrite insert_to_map_Map > [ | ff | ff ].
    eapply trustworthy'_builder.
    + ff.
    + ff.
      -- admit.
      -- admit.
      -- admit.
  * edestruct H1; clear H1.
    erewrite insert_to_map_Map > [ | ff | ff ].
    eapply trustworthy'_builder.
    + ff.
    + ff.
      admit.
  * 
    admit.
    ff.
    ff.
    admit.
    admit.

  admit.

    edestruct H0; clear H0; eapply trustworthy'_builder; ff.
  * 
    unfold trustworthy in *;
    ltac1:(simp trustworthy in * ); ff.
  * admit.
  * admit.
  * admit.
  * admit.
*)
Admitted.

Theorem trustworthy_change_runs : forall tr V E PS tst V' PS' tst' c,
  trustworthy c V E ->
  ~ (trustworthy c V' E) ->
  runs E (V, PS, tst) tr (V', PS', tst') ->
  ((exists l tm, In (Corrupt c l tm) tr) 
  \/ (exists l c' tm, In (Infect c' c l tm) tr)).
Proof.
  induction tr; ff.
  - invc H1; ff.
  - invc H1; ff.
    destruct sg' as [[V'' PS''] tst''].
    destruct (trustworthy_dec c V'' E) as [tv'' | tv''].
    * pp (IHtr _ _ _ _ _ _ _ _ tv'' H0 H7).
      elim_contras H1; Control.enter (fun () => bool_logic).
    * 
Admitted.

Theorem only_timely_attacks_remain : forall V E tst,
  default_Filt V E tst ->
  ~ (exists tr,
  (* There are no traces "tr" s.t. pol2 invalidates it, but pol1 allows it, and it is an attack *)
    (valid_trace_with_filters V E 
      [
        (* Maxims 1-5 (missing 4 currently) *)
        measure_before_done; 
        no_runtime_corruption_on_short; 
        secrets_always_trustworthy;
        no_cycles_in_dep_rel;
        no_timely_attacks
      ] tr) 
    /\ exists V' PS' tst', attack V E tst tr V' PS' tst').
Proof.
  intros.
  intros HC.
  ff.
  invc H1.
  invc H7.
  invc H8.
  clear H7.
  unfold valid_trace in *; repeat (break_exists; break_and).
  ff.
  repeat (inv_runs; try (erewrite <- runs_app in *); ff).
  inv_runs.

  pp (runs_no_way_to_unconclude _ _ _ _ _ _ _ _ H19); ff.
  rewrite <- H20 in *.
  clear H20.
  destruct (trustworthy_dec x4 V0 E);
  destruct (trustworthy_dec x4 V1 E);
  destruct (trustworthy_dec x4 x0 E); ff.

Admitted.

Module Example.

  Local Open Scope string_scope.

  Definition example_dep_rel : DependencyRel :=
    [("c1", "c2"); ("c2", "c3")].

  Definition ex_transitions := transition example_dep_rel.
  Definition ex_runs := runs example_dep_rel.

  Definition init_state : system_graph :=
    ([("c1", (vert NotLaunched Short Safe));
      ("c2", (vert NotLaunched Long Safe));
      ("c3", (vert NotLaunched Short Safe))], 
      UnInit,
      Untrusted).

  Example example_run_no_meas : exists v,
    ex_runs init_state [Start; Corrupt "c1" "L" LaunchTime; End] (v, Concluded true, Untrusted).
  Proof.
    simpl.
    unfold init_state.
    do_goal_run.
  Qed.

  Example example_run_catches : exists v,
    ex_runs init_state [Start; Corrupt "c1" "L" LaunchTime; Meas "c1" LaunchTime; End] (v, Concluded false, Untrusted).
  Proof.
    simpl.
    unfold init_state.
    do_goal_run.
  Qed.

End Example.
