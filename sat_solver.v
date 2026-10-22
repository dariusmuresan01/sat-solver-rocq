(*
Authors:

Darius Muresan - 202502066
Rui Xavier - 202502046
*)

Require Import project_lib.
Require Import List.
Import ListNotations.

(* Exercise 2.1 *)

Inductive form :=
| var : id -> form
| FTrue : form
| FFalse : form
| FNeg : form -> form
| FConj : form -> form -> form
| FDisj : form -> form -> form
| FImpl : form -> form -> form.

(* Exercise 2.2 *)

Definition x : id := Id 0.
Definition y : id := Id 1.

Definition ex1 : form :=
  FConj 
    (FDisj (var x) (FNeg (var y)))
    (FDisj (FNeg (var x)) (var y)).

Definition ex2 : form :=
    FImpl
        (FNeg (var y))
        (FDisj (var x) (var y)).

Definition ex3 : form :=
    FConj
        (FConj (var x) (FNeg (var x)))
        FTrue.

Definition valuation := id -> bool.

Definition empty_valuation : valuation := fun x => false.

Definition override (V : valuation) (x : id) (b : bool) : valuation :=
  fun y => if beq_id x y then b else V y.

(* Exercise 2.3 *)

Fixpoint interp (V : valuation) (p : form) : bool :=
  match p with
  | var x     => V x
  | FTrue     => true
  | FFalse    => false
  | FNeg q    => negb (interp V q)
  | FConj a b => (interp V a) && (interp V b)
  | FDisj a b => (interp V a) || (interp V b)
  | FImpl a b => (negb (interp V a)) || (interp V b)
  end.

(* Satisfiability *)
  Definition satisfiable (p : form ) : Prop :=
exists V : valuation , interp V p = true .

(* Exercise 2.4 *)
Lemma ex1_satisfiable : satisfiable ex1.
Proof.
    exists (override (override empty_valuation x true) y true).
    auto.
Qed.

Lemma ex2_satisfiable : satisfiable ex2.
Proof.
    exists (override empty_valuation y true).
    auto.
Qed.

Lemma satisfiability : forall p V,
  interp V p = true -> satisfiable p.
Proof.
    intros p V H.
    unfold satisfiable.
    exists V.
    apply H.
Qed.

(* Exercise 2.5 *)

Fixpoint vars (p : form) : list id :=
  match p with
  | var x      => [x]
  | FTrue       => []
  | FFalse      => []
  | FNeg q      => vars q
  | FConj p q   => vars p ++ vars q
  | FDisj p q   => vars p ++ vars q
  | FImpl p q   => vars p ++ vars q
  end.

Fixpoint mem_id (x : id) (l : list id) : bool :=
  match l with
  | [] => false
  | y :: ys => if beq_id x y then true else mem_id x ys
  end.

Fixpoint remove_dups (l : list id) : list id :=
  match l with
  | [] => []
  | x :: xs =>
      if mem_id x xs then remove_dups xs
      else x :: remove_dups xs
  end.

Fixpoint all_valuations (vars : list id) : list valuation :=
    match vars with
    | [] => [empty_valuation]
    | x :: xs =>
        let rest := all_valuations xs in
        (map (fun V => override V x true) rest) ++
        (map (fun V => override V x false) rest)
    end.

Fixpoint find_sat (p : form) (vals : list valuation) : option valuation :=
    match vals with
    | [] => None
    | V :: vs =>
        if interp V p
        then Some V
        else find_sat p vs
    end.

Definition find_valuation (p : form) : option valuation :=
    find_sat p (all_valuations (remove_dups (vars p))).

Definition solver (p : form) : bool :=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.

(* Tests *)

Example test_find_valuation1 :
  find_valuation ex1 = 
    Some (override (override empty_valuation y true) x true).
Proof. reflexivity. Qed.

Example test_find_valuation2 :
  find_valuation ex2 = 
    Some (override (override empty_valuation y true) x true).
Proof. reflexivity. Qed.

(* Exercise 2.6 *)

(*

SATISFIABLE
The term satisfiable is defined in Coq as a type of Prop (Logical Proposition).
It represents the mathematical specification of the problem.
Its definition asserts that there exists a valuation V such that the interpretation of the formula p evaluates to true.
Because it involves the existential quantifier (exists), this definition cannot be executed or run as code.
Instead, it is used exclusively in proofs to describe the property of a formula having a solution.
It represents the "What" of the project.

SOLVER
The term solver is defined as a computable function that returns a bool (computational Boolean).
It represents the algorithmic implementation.
This function works by calling the helper function find_valuation to search through a generated list of all possible valuations.
If it finds a valid valuation, it returns true; otherwise, it returns false.
Unlike satisfiable, this function can be executed (using commands like Compute) to calculate an 
actual result for a specific formula. It represents the "How" of the project.

THE RELATIONSHIP
The critical link between the implementation and the specification is 
established through the Soundness Lemma (solver_sound).
This proof demonstrates that the computational algorithm is correct with respect to the logical specification.
Specifically, it proves that if the solver function returns the boolean true, 
then the formula is mathematically satisfiable according to the proposition.

*)

(* Exercise 2.7 *)

(* Solver tests *)

Example test_solver1 :
  solver ex1 = true.
Proof. reflexivity. Qed.

Example test_solver2 :
  solver ex2 = true.
Proof. reflexivity. Qed.

Example test_solver3 :
  solver ex3 = false.
Proof. reflexivity. Qed.

Example test_solver4 :
  solver (FConj (var x) (FNeg (var x))) = false.
Proof. reflexivity. Qed.

(* Exercise 2.8 *)

Lemma find_sat_sound : forall p vals V,
  find_sat p vals = Some V -> interp V p = true.
Proof.
  induction vals as [| W ws IH]; intros V H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (interp W p) eqn:E.
    + inversion H; subst; clear H. assumption.
    + apply IH. assumption.
Qed.

Lemma solver_sound : forall p,
  solver p = true -> satisfiable p.
Proof.
  intros p H.
  unfold solver in H.
  unfold find_valuation in H.
  unfold satisfiable.
  destruct (find_sat p (all_valuations (remove_dups (vars p)))) as [V|] eqn:E.
  - simpl in H. inversion H; clear H.
    exists V.
    apply (find_sat_sound p (all_valuations (remove_dups (vars p))) V).
    exact E.
  - simpl in H. discriminate.
Qed.

(* Exercise 2.9 *)

(* Moderate (1) *)

Inductive tri : Type :=
| TTrue : tri
| TFalse : tri
| TUnknown : tri.

Definition neg_tri (t : tri) : tri :=
  match t with
  | TTrue => TFalse
  | TFalse => TTrue
  | TUnknown => TUnknown
  end.

Definition and_tri (t1 t2 : tri) : tri :=
  match t1, t2 with
  | TFalse, _ => TFalse
  | _, TFalse => TFalse
  | TTrue, TTrue => TTrue
  | _, _ => TUnknown
  end.

Definition or_tri (t1 t2 : tri) : tri :=
  match t1, t2 with
  | TTrue, _ => TTrue
  | _, TTrue => TTrue
  | TFalse, TFalse => TFalse
  | _, _ => TUnknown
  end.

Definition impl_tri (t1 t2 : tri) : tri :=
  or_tri (neg_tri t1) t2.

Definition valuation3 := id -> tri.

Fixpoint interp3 (V : valuation3) (p : form) : tri :=
  match p with
  | var x => V x
  | FTrue => TTrue
  | FFalse => TFalse
  | FNeg q => neg_tri (interp3 V q)
  | FConj q1 q2 => and_tri (interp3 V q1) (interp3 V q2)
  | FDisj q1 q2 => or_tri (interp3 V q1) (interp3 V q2)
  | FImpl q1 q2 => impl_tri (interp3 V q1) (interp3 V q2)
  end.

Definition satisfiable3 (p : form) : Prop :=
  exists V : valuation3, interp3 V p = TTrue.

Definition bool_to_tri (b : bool) : tri :=
  if b then TTrue else TFalse.

Definition val_2_to_3 (V : valuation) : valuation3 :=
  fun x => bool_to_tri (V x).

Lemma three_valued_consistency : forall V p,
  bool_to_tri (interp V p) = interp3 (val_2_to_3 V) p.
Proof.
  intros V p.
  induction p; simpl; auto;
  try rewrite <- IHp; try rewrite <- IHp1; try rewrite <- IHp2;
  try destruct (interp V p); 
  try destruct (interp V p1); try destruct (interp V p2); 
  simpl; reflexivity.
Qed.

(* Moderate (2) *)

Fixpoint optimize (p : form) : form :=
  match p with
  | var x => var x
  | FTrue => FTrue
  | FFalse => FFalse
  | FNeg p' => 
      match optimize p' with
      | FTrue => FFalse
      | FFalse => FTrue
      | opt_p => FNeg opt_p
      end
  | FConj p1 p2 =>
      match optimize p1, optimize p2 with
      | FTrue, opt_p2 => opt_p2
      | FFalse, _ => FFalse
      | opt_p1, FTrue => opt_p1
      | _, FFalse => FFalse
      | opt_p1, opt_p2 => FConj opt_p1 opt_p2
      end
  | FDisj p1 p2 =>
      match optimize p1, optimize p2 with
      | FTrue, _ => FTrue
      | FFalse, opt_p2 => opt_p2
      | _, FTrue => FTrue
      | opt_p1, FFalse => opt_p1
      | opt_p1, opt_p2 => FDisj opt_p1 opt_p2
      end
  | FImpl p1 p2 => 
      match optimize p1, optimize p2 with
      | FFalse, _ => FTrue
      | FTrue, opt_p2 => opt_p2
      | _, FTrue => FTrue
      | opt_p1, opt_p2 => FImpl opt_p1 opt_p2
      end
  end.

Lemma optimize_correct : forall p V,
  interp V (optimize p) = interp V p.
Proof.
  intros p V.
  induction p; simpl; auto;
  try rewrite <- IHp; try rewrite <- IHp1; try rewrite <- IHp2;
  try destruct (optimize p); 
  try destruct (optimize p1); try destruct (optimize p2);
  simpl; auto;
  repeat rewrite Bool.andb_true_r; repeat rewrite Bool.andb_false_r;
  repeat rewrite Bool.orb_true_r;  repeat rewrite Bool.orb_false_r;
  reflexivity.
Qed.

Definition solver_opt (p : form) : bool :=
  solver (optimize p).

Lemma solver_opt_sound : forall p, solver_opt p = true -> satisfiable p.
Proof.
  intros p H. unfold solver_opt in H.
  apply solver_sound in H.
  unfold satisfiable in *. destruct H as [V H].
  exists V. rewrite <- optimize_correct. assumption.
Qed.

(* Difficult *)

Fixpoint to_nnf (p : form) : form :=
  match p with
  | var x => var x
  | FTrue => FTrue
  | FFalse => FFalse
  | FNeg p' => neg_nnf p'
  | FConj p1 p2 => FConj (to_nnf p1) (to_nnf p2)
  | FDisj p1 p2 => FDisj (to_nnf p1) (to_nnf p2)
  | FImpl p1 p2 => FDisj (neg_nnf p1) (to_nnf p2)
  end
with neg_nnf (p : form) : form :=
  match p with
  | var x => FNeg (var x)
  | FTrue => FFalse
  | FFalse => FTrue
  | FNeg p' => to_nnf p'
  | FConj p1 p2 => FDisj (neg_nnf p1) (neg_nnf p2)
  | FDisj p1 p2 => FConj (neg_nnf p1) (neg_nnf p2)
  | FImpl p1 p2 => FConj (to_nnf p1) (neg_nnf p2)
  end.

Lemma nnf_equiv_mutual : forall p,
  (forall V, interp V (to_nnf p) = interp V p) /\
  (forall V, interp V (neg_nnf p) = negb (interp V p)).
Proof.
  induction p; simpl; split; intros V; auto;
  try destruct IHp as [IH_pos IH_neg]; 
  try destruct IHp1 as [IH1_pos IH1_neg]; 
  try destruct IHp2 as [IH2_pos IH2_neg];
  try rewrite IH_pos; try rewrite IH_neg;
  try rewrite IH1_pos; try rewrite IH1_neg;
  try rewrite IH2_pos; try rewrite IH2_neg;
  try rewrite Bool.negb_involutive;
  try rewrite Bool.negb_andb;
  try rewrite Bool.negb_orb;
  try rewrite Bool.negb_involutive;
  reflexivity.
Qed.

Lemma nnf_correct : forall p V,
  interp V (to_nnf p) = interp V p.
Proof.
  intros p V.
  destruct (nnf_equiv_mutual p) as [H _].
  apply H.
Qed.

Definition solver_nnf (p : form) : bool :=
  solver (to_nnf p).

Lemma solver_nnf_sound : forall p,
  solver_nnf p = true -> satisfiable p.
Proof.
  intros p H.
  unfold solver_nnf in H.
  apply solver_sound in H.
  unfold satisfiable in *.
  destruct H as [V H_sat].
  exists V.
  rewrite <- nnf_correct.
  assumption.
Qed.

(* Very Difficult (1) *)

Fixpoint distribute (p1 p2 : form) : form :=
  match p1 with
  | FConj a b => FConj (distribute a p2) (distribute b p2)
  | _ => 
      (fix dist_helper (p2_inner : form) : form :=
         match p2_inner with
         | FConj c d => FConj (dist_helper c) (dist_helper d)
         | _ => FDisj p1 p2_inner
         end) p2
  end.

Fixpoint to_cnf_from_nnf (p : form) : form :=
  match p with
  | FConj a b => FConj (to_cnf_from_nnf a) (to_cnf_from_nnf b)
  | FDisj a b => distribute (to_cnf_from_nnf a) (to_cnf_from_nnf b)
  | other => other
  end.

Definition to_cnf (p : form) : form :=
  to_cnf_from_nnf (to_nnf p).

Lemma distribute_correct : forall p1 p2 V,
  interp V (distribute p1 p2) = interp V (FDisj p1 p2).
Proof.
  induction p1; intros p2 V; simpl.
  5: {
    rewrite IHp1_1. rewrite IHp1_2.
    symmetry. apply Bool.orb_andb_distrib_l.
  }
  all: induction p2; simpl; auto;
       try rewrite IHp2_1; try rewrite IHp2_2;
       try (symmetry; apply Bool.orb_andb_distrib_r);
       try destruct (V i); 
       try destruct (interp V p1);
       try reflexivity.
Qed.

Lemma cnf_from_nnf_correct : forall p V,
  interp V (to_cnf_from_nnf p) = interp V p.
Proof.
  induction p; simpl; auto; intros V;
  try rewrite distribute_correct; simpl;
  try rewrite IHp1; try rewrite IHp2;
  reflexivity.
Qed.

Lemma cnf_correct : forall p V,
  interp V (to_cnf p) = interp V p.
Proof.
  intros p V.
  unfold to_cnf.
  rewrite cnf_from_nnf_correct.
  rewrite nnf_correct.
  reflexivity.
Qed.

Definition solver_cnf (p : form) : bool :=
  solver (to_cnf p).

Lemma solver_cnf_sound : forall p,
  solver_cnf p = true -> satisfiable p.
Proof.
  intros p H.
  unfold solver_cnf in H.
  apply solver_sound in H.
  unfold satisfiable in *.
  destruct H as [V H_sat].
  exists V.
  rewrite <- cnf_correct.
  assumption.
Qed.

(* Very Difficult (2) *)

Lemma interp_agreement : forall p V1 V2,
  (forall x, In x (vars p) -> V1 x = V2 x) ->
  interp V1 p = interp V2 p.
Proof.
  induction p; intros; simpl; auto.
  - apply H. simpl. left. reflexivity.
  - apply f_equal. eauto.
  - try apply f_equal2; try apply IHp1; try apply IHp2; intros x IH;
  apply H; simpl; apply in_or_app; eauto.
  - apply f_equal2. apply IHp1. intros x IH1. apply H. simpl. apply in_or_app. eauto. 
  apply IHp2. intros x IH2. apply H. simpl. apply in_or_app. eauto.
  - apply f_equal2; try apply f_equal; try apply IHp1; try apply IHp2; intros x IH;
  apply H; simpl; apply in_or_app; auto.
Qed.

Lemma beq_id_true_iff : forall x y, beq_id x y = true <-> x = y.
Proof.
  intros. split.
  - intros. apply beq_id_eq. eauto.
  - intros. subst. symmetry. apply beq_id_refl.
Qed.

Lemma mem_id_iff : forall x l, mem_id x l = true <-> In x l.
Proof.
  intros x l.
  induction l.
  - simpl. split; intros.
    + discriminate.
    + contradiction.
  - simpl.
    destruct (beq_id x a) eqn:Heq.
    + split; intros.
      * apply beq_id_true_iff in Heq.
        subst.
        left. reflexivity.
      * reflexivity.
    + split; intros.
      * right. apply IHl. assumption.
      * destruct H.
        -- subst.
           rewrite <- beq_id_refl in Heq.
           discriminate.
        -- apply IHl.
           assumption.
Qed.

Lemma in_remove_dups : forall x l, In x l <-> In x (remove_dups l).
Proof.
  induction l; simpl.
  - split; auto.
  - destruct (mem_id a l) eqn:Hmem.
    + split; intros.
      * destruct H. subst. apply IHl. apply mem_id_iff. assumption.
        apply IHl. assumption.
      * right. apply IHl in H. assumption.
    + split; intros.
      * destruct H. subst. left. reflexivity.
        right. apply IHl. assumption.
      * destruct H. subst. left. reflexivity.
        right. apply IHl in H. assumption.
Qed.

Lemma in_map_iff_override : forall V x b l,
  In V l -> In (override V x b) (map (fun V' => override V' x b) l).
Proof.
  intros V x b l H. apply in_map with (f := fun V' => override V' x b). assumption.
Qed.

Lemma all_valuations_covers : forall l V,
  exists V', In V' (all_valuations l) /\
  (forall x, In x l -> V' x = V x).
Proof.
  induction l; simpl; intros.
  - exists empty_valuation; split; [left; reflexivity | contradiction].
  - destruct (IHl V) as [V_sub [H_in H_agree]].
    exists (override V_sub a (V a)); split.
    + apply in_or_app; destruct (V a); [left|right];
      apply in_map_iff_override; assumption.
    + intros x [H_head | H_tail]; unfold override.
      * subst; rewrite <- beq_id_refl; reflexivity.
      * destruct (beq_id a x) eqn:Heq.
        -- apply beq_id_true_iff in Heq; subst; reflexivity.
        -- apply H_agree; assumption.
Qed.

Lemma find_sat_exists : forall vals p V,
  In V vals ->
  interp V p = true ->
  exists V_found, find_sat p vals = Some V_found.
Proof.
  induction vals; intros.
  - inversion H.
  - simpl. destruct H.
    + subst. rewrite H0. exists V. reflexivity.
    + destruct (interp a p).
      * exists a. reflexivity.
      * apply IHvals with (V := V).
        -- assumption.
        -- assumption.
Qed.

Lemma solver_complete : forall p,
  satisfiable p -> solver p = true.
Proof.
  intros p H.
  destruct H as [V H_sat].
  unfold solver, find_valuation.
  assert (H_cover := all_valuations_covers (remove_dups (vars p)) V).
  destruct H_cover as [V' [H_in H_agree]].
  assert (H_sat_V' : interp V' p = true).
  {
    rewrite <- H_sat.
    apply interp_agreement.
    intros x H_in_vars.
    apply H_agree.
    apply in_remove_dups in H_in_vars.
    assumption.
  }
  apply find_sat_exists with (vals := all_valuations (remove_dups (vars p))) (V := V') in H_sat_V'.
  - destruct H_sat_V' as [V_found H_found].
    rewrite H_found.
    reflexivity.
  - assumption.
Qed.