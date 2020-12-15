From mathcomp Require Import all_ssreflect ssrbool finmap matrix.
Require Import String Ascii.
Require Import Nat.
Require Import Coq.Program.Wf.

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import classical_sets topology finset.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


Section FinTypeSubsets.

  Variable T : finType.
  Implicit Type X : T -> Type.
  Implicit Type A : {set T}.

  Definition subsetFinType A : finType := sig_finType (mem A).
  Lemma subsetFinType_super_type A (T' : subsetFinType A) : T.
  Admitted.
  Definition subsetDepType X A (t : subsetFinType A) : Type := X (subsetFinType_super_type t).

End FinTypeSubsets.




Section MeasureDefs.

  Variable X : finType.
  Variable Y : realFieldType.

  (*
  Variable Z : Type.
  Set Printing All.
  Check fun s : set X => s == s.
  Print set.
  About set.
  *)

  Implicit Type x : X.
  Implicit Type d : X -> Y.
  Implicit Type mu : {set X} -> Y.
  Implicit Type A B : {set X}.
  
  Definition is_capacity mu :=
    mu set0 = 0
    /\
    mu setT = 1
    /\
    forall A B, A \subset B -> mu A <= mu B.

  Definition is_bel mu : Prop.
  Admitted.   
  Definition is_pl mu : Prop.
  Admitted.
  Definition is_proba mu : Prop.
  Admitted.

  Definition is_dist d :=
    \sum_(x : X) d x = 1
    /\
    forall x : X, 0 <= d x <= 1.

  Lemma proba_capa mu :
    is_proba mu -> is_capacity mu.
  Admitted.

  Lemma proba_bel mu :
    is_proba mu -> is_bel mu.
  Admitted.

  Lemma proba_pl mu :
    is_proba mu -> is_pl mu.
  Admitted.

  Lemma bel_capa mu :
    is_bel mu -> is_capacity mu.
  Admitted.

  Lemma pl_capa mu :
    is_pl mu -> is_capacity mu.
  Admitted.


  Definition mk_dist mu x := mu (set1 x).

  Definition mk_proba d A : Y :=
      match boolP (#|A| == 1)%N with
      | AltTrue h => d (projT1 (mem_card1 (eqP h)))
      | AltFalse _ => 0
      end.

  Lemma proba_dist mu A :
    mu A = \sum_(x : X | x \in A) mk_dist mu x.
  Admitted.

  Lemma proba_cancel :
    cancel mk_dist mk_proba.
  Admitted.
  Lemma dist_cancel :
    cancel mk_proba mk_dist.
  Admitted.
  
  Definition mobius_inverse mu : {set X} -> Y.
  Admitted.

  Lemma mobius_inverse_correct mu A :
    mu A = \sum_(B : {set X} | B \subset A) mobius_inverse mu B.
  Admitted.

  (*
  Lemma mobius_inverse_pmf (X : finType) (Y : realFieldType) (mu : {set X} -> Y) :
    is_bel mu -> is_dist (mobius_inverse mu).
   *)

  


  Section ConditionDefs.

    Implicit Type mu_c : {set X} -> option Y.

    Definition proba_cond mu A : {set X} -> option Y.
    Admitted.

    Definition cond_correct mu mu_c : Prop.
    Admitted.

    Definition cond_total mu_c A :=
      match mu_c A with
      | None => 0
      | Some v => v
      end.
    


    Section DecisionDefs.

      Variable (u : X -> Y)
               (v : {set X} -> Y)
               (uv_correct : forall x : X, u x = v (set1 x)).

      Definition expected_utility d (p : is_dist d) : Y :=
        \sum_(x : X) d x * u x.

      Definition expected_utility_p mu (p : is_proba mu) : Y :=
        \sum_(x : X) mu (set1 x) * v (set1 x).

      Definition mobius_expected_utility mu : Y :=
        \sum_(A : {set X}) mobius_inverse mu A.

      Lemma mobius_expected_utility_correct mu (p : is_proba mu) :
        expected_utility_p p = mobius_expected_utility mu.
      Admitted.

    End DecisionDefs.

  End ConditionDefs.
  
End MeasureDefs.





Section GameDefs.



  Search _ "addr0".

  Notation " '( i , t ) " := (existT _ i t).
  Notation " '( it ).1 " := (projT1 it).
  Notation " '( it ).2 " := (projT2 it).
  
  Section Profiles.


    Implicit Type (N : finType).
    (*    
      Implicit Type (X : N -> Type).
      Implicit Type (T : N -> finType). *)

    Definition profile N X := {dffun forall i : N, X i}.

    Definition iprofile N X := profile (fun i : N => X).

    Definition bprofile N (T : N -> finType) X :=
      profile (fun it : {i : N & T i} => X '(it).1).

    Definition biprofile N T X := bprofile T (fun i : N => X).

    (* {ffun forall it : {i : N & T i}, X (projT1 it)}. *)
    
    Definition subprofile N X (N' : {set N}) :=
      profile (subsetDepType X (A:=N')).
    
    Definition subiprofile N X (N' : {set N}) :=
      profile (subsetDepType (fun i : N => X) (A:=N')).
    
    Definition projprofile N X (p : profile X) (N' : {set N}) : subprofile X N' :=
      [ffun i => p (subsetFinType_super_type i)].

    Definition projbprofile N (T : N -> finType) X (bprof : bprofile T X) (theta : forall i, T i) :
      profile X :=
      [ffun i => bprof '(i,theta i)].

    Definition upd_profile N X (p : profile X) (i : N) (xi : X i) : profile X :=
      [ffun j =>
      match boolP (i == j) with
      | AltTrue h => eq_rect _ _ xi j (eqP h)
      | AltFalse _ => p j
      end].
    

  End Profiles.




    
  Variables (U : Type)
            (V : Type)
            (U0 : U)
            (oplus : Monoid.com_law U0)
            (otimes : V -> U -> U)
            (geqU : rel U).



  Section NormalFormGame.

    Variables (N : finType)
              (A : N -> finType).

    Definition NFGame := profile A -> iprofile N U.

  End NormalFormGame.


  Section BayesianGame.

    Variables (N : finType)
              (A : N -> finType)
              (T : N -> finType)
              (d : profile T -> {i : N & T i} -> V).

    Implicit Type it : {i : N & T i}.

    Definition BGame := profile A * profile T -> iprofile N U.

    Definition BGame_expected_utility G (a : bprofile T A): biprofile T U :=
      [ffun it =>
       \big[oplus/U0]_(p : profile T | p '(it).1 == '(it).2)
        otimes (d p it) (G (projprofile) p)].

    Definition Nash_equilibrium G (a : bprofile T A) :=
      forall it,
      forall ait : A '(it).1,
      geqU (BGame_expected_utility G a it) (BGame_expected_utility G (upd_profile a ait) it).

  End BayesianGame.


  Section HyperGraphicalGame.

    Variables (N : finType)
              (A : N -> finType).

    Definition HGGame := forall E : {set N}, option (subprofile A E -> subiprofile U E).

    Definition is_polymatrix (G : HGGame) : Prop :=
      forall E, match G E with
                | None => True
                | Some _ => #|E| = 2
                end.

    Definition HGGame_global_utility G (a : profile A) : iprofile N U :=
      [ffun i : N =>
       \big[oplus/U0]_(E : {set N})
        match G E with
        | None => U0
        | Some f => f (projprofile a E)
        end].

  End HyperGraphicalGame.



  Section HR.

    Variables (N : finType)
              (A : N -> finType)
              (T : N -> finType)
              (G : BGame A T).

    Implicit Type it : {i : N & T i}.

    Definition A' := fun it => A '(it).1.

    Definition E' : {set {set {i : N & T i}}} :=
      [set [set '(i,theta i) | i : N] | theta : profile T].

    Definition is_e_theta (e : {set {i : N & T i}}) :=
      exists theta : profile T,
      forall it,
      (it \in e) = (theta '(it).1 == '(it).2).

    Lemma E'_correct : forall e, is_e_theta e <-> e \in E'.
    Admitted.

    Definition theta_of (e : {set {i : N & T i}}) : profile T.
    Admitted.

    Definition G' : HGGame A' :=
      fun E_theta : {set {i : N & T i}} =>
      if E_theta \in E'
      then let theta := theta_of E_theta in
           Some (fun a => G (projbprofile a theta,theta))
      else None.
    Admitted.

    Definition theta_of (e : {set {i : N & T i}}) : profile T.
    Admitted.

    Definition G' : HGGame A' :=
      fun E_theta : {set {i : N & T i}} =>
      if E_theta \in E'
      then let theta := theta_of E_theta in
           Some (fun a => G (projbprofile a theta,theta))
      else None.


    (* To be continued *)
