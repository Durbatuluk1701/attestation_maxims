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

Fixpoint list_find_first {A : Type} (x : A) (l : list A) 
    : {n : nat | exists lf le, l = lf ++ x :: le } 
    + {~ In x l}.
Admitted.

Definition has_cycle {ty : Type} (h : ty) (t' : list ty) (HNDt : NoDup t') : 
  {exists p1 p2, h :: t' = h :: p1 ++ h :: p2} + {NoDup (h :: t')}.
  ref (match t' as t'' return t' = t'' -> 
    {exists p1 p2, h :: t' = h :: p1 ++ h :: p2} + {NoDup (h :: t')} with
  | nil => fun _ => right _
  | off :: rst => fun HP => _
  end eq_refl).
  - subst; eapply NoDup_cons; ff.
  - pp (list_find_first h t').
    destruct H.
    * destruct s.
      left.
      ff.
    * right.
      econstructor; assumption.
Qed.

Definition is_cycle {t : Type} (p : list t) : Prop :=
  exists h p1 p2, p = h :: p1 ++ h :: p2.

Inductive path (t : Type) :=
| Dead : forall (p : list t), is_cycle p -> path t
| Live : forall (p : list t), NoDup p -> path t.
Arguments Dead {t} _ _.
Arguments Live {t} _ _.

Definition AllDead (t : Type) := 
  { l : list (path t) | Forall (fun pt => exists v h, pt = Dead v h) l }.
Definition AllDeadNil (t : Type) : AllDead t := exist _ nil (Forall_nil _).
Definition AllLive (t : Type) := 
  { l : list (path t) | Forall (fun pt => exists v h, pt = Live v h) l }.
Definition AllLiveNil (t : Type) : AllLive t := exist _ nil (Forall_nil _).

Module Type ClosureS.
  Parameter t : Type.

  Parameter one_step_paths : t -> list (t * t) -> path t.
  Parameter multi_step_paths : t -> list (t * t) -> list t -> list (path t).
End ClosureS.

Module Closure (Ord : OrderedType) <: ClosureS with Definition t := Ord.t.
  Definition t := Ord.t.

  Module CSet := MSetList.Make(Ord).

  Definition one_step_paths_set a rel :=
    List.fold_left
      (fun acc '(x, y) => if Ord.eq_dec x a then CSet.add y acc else acc)
      rel
      CSet.empty.

  Definition one_step_paths a rela := 
    CSet.elements (one_step_paths_set a rela).

  Definition extend_one_step (rela : list (t * t)) (paths : AllLive t)
      : AllDead t * AllLive t.
    destruct paths as [paths Hpaths].
    ref (dep_fold_left paths _ (AllDeadNil t, AllLiveNil t)).
    intros [dead live] path Hinpaths.
    unfold AllLive, AllDead in *.
    destruct path.
    - exfalso.
      erewrite Forall_forall in *.
      pp (Hpaths _ Hinpaths).
      ff.
    - destruct p as [| h t'].
      * (* empty path!? - should not happen! *)
        apply (dead, live).
      * set (one_step := one_step_paths h rela).

        ref (dep_fold_left one_step _ (dead, live)).
        clear dead live.
        intros [dead live] next Hinnext.
        destruct (has_cycle next (h :: t') n).
        + (* next is already in the path, so it forms a cycle *)
          destruct dead as [deadV deadH].
          split > [ | apply live].
          ref (exist _ ((Dead (next :: h :: t') _) :: deadV) _).
          erewrite Forall_forall.
          intros.
          simpl in H.
          destruct H.
          -- subst.
            repeat eexists; eauto.
            Unshelve.
            unfold is_cycle.
            ff.
          -- erewrite Forall_forall in *.
            ff.
        + destruct live as [liveV liveH].
          split > [ apply dead | ].
          ref (exist _ ((Live (next :: h :: t') _) :: liveV) _).
          ff.
          Unshelve.
          ff.
  Qed.
          (* erewrite 

      ff.
      Search (Forall).
      unfold Forall in *.
      edestruct Hpaths.
    set (f := 
      (fun _ '(dead, live) path Hinpaths =>
        let path :=
          match path with
          | Live p Hlive => p
          | Dead p Hdead => p
          end
        in
        match path with
        | nil => (* empty path!? *) (dead, live)
        | h :: t =>
          let one_step := one_step_paths h rela in
          List.fold_left
            (fun '(dead, live) next =>
              match InA_dec Ord.eq_dec next path with
              | left Hdead => ((Dead (next :: path) :: dead), live)
              | right Hndead => (dead, (Live (next :: path) :: live))
              end
            )
            one_step
            (dead, live)
        end)).
    dep_fold_left
      paths
      (nil, nil)). *)

  Fixpoint all_in_rel rela :=
    match rela with
    | nil => CSet.empty
    | (x, y) :: t => CSet.add x (CSet.add y (all_in_rel t))
    end.

  Equations multi_step_paths_set (rela : list (t * t)) (paths : AllLive t)
    : list (path t)
    by wf (CSet.cardinal (all_in_rel rela) - length (proj1_sig paths)) :=
    multi_step_paths_set rela paths :=
    match (proj1_sig paths) with
    | nil => nil
    | _ =>
      let '(dead_paths, live_paths) := extend_one_step rela paths in
      (multi_step_paths_set rela live_paths) ++ 
        (proj1_sig dead_paths) ++ (proj1_sig live_paths)
    end.
  Next Obligation.
    admit.
  Admitted.

  Definition multi_step_paths a rela :=
    multi_step_paths_set rela [ Live [ a ] ].
