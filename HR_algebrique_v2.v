From mathcomp Require Import all_ssreflect ssrbool finmap.
From mathcomp Require Import all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*

Section EvaluationStructure.

  (* Evaluation structure *)
  Variables (U W V : Type)
            (preceq_U : rel U) (preceq_W : rel W) (preceq_V : rel V)
            (V0 : V)
            (oplus : Monoid.com_law V0)
            (otimes : W -> U -> V).

End EvaluationStructure.

*)

Section EvalStruct.

  Record eval_struct : Type :=
    { U : finType ;
      W : eqType ;
      V : eqType ;
      V0 : V ;
      preceq_U : rel U ;
      preceq_W : rel W ;
      preceq_V : rel V ;
      oplus : Monoid.com_law V0 ;
      otimes : W -> U -> V ;
    }.

End EvalStruct.



Section Games.

  

  Variable rty : numDomainType.

  Section Profiles.
    Variables (N : finType)
              (T : N -> finType)
              (X : N -> Type).

    Definition profile := {ffun forall i, X i}.
    Definition fprofile := {dffun forall i, T i}.
    Definition bprofile := {ffun forall it : {i : N & T i}, X (projT1 it)}.

    Definition proj_profile (bp : bprofile) (theta : fprofile) : profile :=
      [ffun i => bp (existT _ i (theta i))].

  End Profiles.

  Section IIGames.
    
    (* Situation de jeu *)
    Variables (N : finType)
              (Omega : finType)
              (Theta : N -> finType)
              (tau : forall (i : N), Omega -> Theta i)
              (A : forall (i : N), finType).
    (* Spécification des agents *)
    Variables (E : forall (i : N) (t : Theta i), eval_struct)
              (d : forall (i : N) (t : Theta i), Omega -> W (E t))
              (u : forall (i : N) (t : Theta i), profile A -> Omega -> U (E t)).

    Definition mk_tprofile (omg : Omega) : fprofile Theta :=
      [ffun i => tau i omg].

    Definition IIutility i t  (bp : bprofile Theta A) : V (E t) :=
      \big[oplus (E t)/V0 (E t)]_(omg in [pred omg | tau i omg == t])
       otimes (d t omg) (u t (proj_profile bp (mk_tprofile omg)) omg).
       
    
  End IIGames.

  Section HGGames.
    
    (* Situation de jeu *)
    Variables (N : finType)
              (E : {set {set N}})
              (A : forall (i : N), finType).

    (* Spécification des agents *)
    Variables (V : forall (i : N), Type)
              (V0 : forall (i : N), V i)
              (oplus : forall (i : N), Monoid.com_law (V0 i) )
              (u : forall e i, e \in E -> i \in e -> profile A -> V i).

    Definition u_total e i p :=
      match boolP (e \in E) with
      | AltTrue h1 =>
        match boolP (i \in e) with
        | AltTrue h2 => u h1 h2 p
        | AltFalse _ => V0 i
        end
      | AltFalse _ => V0 i
      end.
    
    Definition HGutility (i : N) (p : profile A) : V i :=
      \big[oplus i/V0 i]_(e in [pred e | e \in E]) u_total e i p.

  End HGGames.

  Section HR.
    
    (* Situation de jeu *)
    Variables (N : finType)
              (Omega : finType)
              (Theta : N -> finType)
              (tau : forall (i : N), Omega -> Theta i)
              (A : forall (i : N), finType).
    (* Spécification des agents *)
    Variables (E : forall (i : N) (t : Theta i), eval_struct)
              (d : forall (i : N) (t : Theta i), Omega -> W (E t))
              (u : forall (i : N) (t : Theta i), profile A -> Omega -> U (E t)).


    Definition e_theta (theta : fprofile Theta) := [set existT Theta i (theta i) | i in N].
    Definition omgs_of_theta (theta : fprofile Theta) : {set Omega} := [set omg : Omega | [forall i : N, (tau i omg) == (theta i)]].
    


    Definition bar_N := [finType of {i : N & Theta i}].
    Definition bar_oplus := fun it : bar_N => oplus (E (projT2 it)).
    Definition bar_A := fun (it : bar_N) => A (projT1 it).
    Definition bar_E := [set e_theta theta | theta in fprofile Theta].

    Definition theta_of_e (e : {set {i : N & Theta i}}) : fprofile Theta. Admitted.
    
    Definition bar_u_total (e : {set bar_N}) (it : bar_N) bp :=
      let i := projT1 it in
      let t := projT2 it in
      let theta := theta_of_e e in
      match boolP (e \in bar_E) with
      | AltTrue he =>
        match boolP (it \in e) with
        | AltTrue hit => \big[oplus (E t)/V0 (E t)]_(omg in omgs_of_theta theta)
                          otimes (d t omg) (u t (proj_profile bp theta) omg)
        | _ => V0 (E t)
        end
      | _ => V0 (E t)
      end.

    (* TODO utiliser les preuves que e \in bar_E et i \in e ? *)
    Definition bar_u (e : {set bar_N}) (it : bar_N) (_ : e \in bar_E) (_ : it \in e) bp :=
      let i := projT1 it in
      let t := projT2 it in
      let theta := theta_of_e e in
      \big[oplus (E t)/V0 (E t)]_(omg in omgs_of_theta theta)
                          otimes (d t omg) (u t (proj_profile bp theta) omg).
                          
    Lemma eq_oplus (i : N) (t : Theta i) :
      oplus (E t) = bar_oplus (existT _ i t).
    Proof. by auto. Qed.

    

    Check IIutility _ _ _ _ _.
    Check HGutility _ _ _ _.
    Lemma HR :
      forall i t bp, IIutility tau d u t bp = HGutility bar_oplus bar_u (existT _ i t) bp.
    Proof.
    rewrite /IIutility /HGutility.
    move => i t bp.
    rewrite -eq_oplus => //=.
    (* To be continued... A table ! *)
    Admitted.
    
  End HR.

    
End Games.



(*

Section DecisionProblem.

  Record decision_situation : Type :=
    { Omega : finType ;
      C : finType ;
      (* acts : ({ffun Omega -> C})%type ; *)
    }.
  
  Definition act situation : Type := {ffun Omega situation -> C situation}.
  
  Record decision_problem : Type := 
    { situation : decision_situation ;
      E : eval_struct ;
      u : C situation -> U E ;
      Pl : {set (Omega situation)} -> W E ;
    }.

  Definition ua (D : decision_problem) (a : act (situation D)) : Omega _ -> U _ := fun sow => u (a sow).

  Check ua _.

  Definition ua_inv (D : decision_problem) (a : act (situation D))  : U _ -> {set Omega _} :=
    fun util => [set sow | (ua a sow) == util].

  Definition range_ua D (a : act (situation D)) : {set U (E D)} :=
    [set ua a sow | sow in Omega _].

  Definition GEU (D : decision_problem) (a : act (situation D)) : V (E D) :=
    \big[oplus (E D)/V0 (E D)]_(x in range_ua a) otimes (Pl (ua_inv a x)) x.

  Definition is_dist (X : finType) (Y : Type) X0 (mu : {set X} -> Y) (d : X -> Y) (oplus : Monoid.com_law X0) :=
    forall A : {set X}, mu A = \big[oplus/X0]_(x in A) d x.

  Check is_dist _ _.

End DecisionProblem.



Module Game.

  Variable rty : numDomainType.

  Section Profiles.
    Variables (N : finType)
              (T : N -> finType)
              (X : N -> Type).

    Definition profile := {ffun forall i, X i}.
    Definition fprofile := {dffun forall i, T i}.
    Definition bprofile := {ffun forall it : {i : N & T i}, X (projT1 it)}.

    Definition proj_profile (bp : bprofile) (theta : fprofile) : profile :=
      [ffun i => bp (existT _ i (theta i))].

  End Profiles.


  Module SNF.
    Record game : Type :=
      { N : finType ;
        A : forall i : N, finType ;
        u : forall i : N, profile A -> rty ;
      }.
  End SNF.

  Module BGame.
    Record game : Type :=
      { N : finType ;
        A : forall i : N, finType ;
        Theta : forall i : N, finType ;
        P_cond : profile Theta -> {i : N & Theta i} -> rty ;
        u : forall i : N, bprofile Theta A -> profile Theta -> rty ;
      }.

    Definition UE G (i : N G) (t : Theta i) (bp : bprofile (Theta (g:=G)) (A (g:=G))) : rty :=
      \sum_(theta in [pred p : fprofile (Theta (g:=G)) | p i == t]) P_cond theta (existT _ i (theta i)) * u i bp theta.

  End BGame.

  Module HGGame.
    Record game : Type :=
      { N : finType ;
        E : {set {set N}} ;
        A : forall i : N, finType ;
        u : forall e i, e \in E -> i \in e -> profile A -> rty ; 
      }.

    Search _ (is_true (_ && _)).
    
    Definition u_total G e i :=
      match boolP (e \in E G) with
      | AltTrue h1 =>
        match boolP (i \in e) with
        | AltTrue h2 => u h1 h2
        | AltFalse _ => fun _ => 0%R
        end
      | AltFalse _ => fun _ => 0%R
      end.
    
    Definition UG G i p : rty :=
      \sum_(e in E G) u_total e i p.

  End HGGame.

  Definition SNFGame_2_HGGame (G : SNF.game) : HGGame.game :=
    {| HGGame.N := SNF.N G ;
       HGGame.E := set1 setT ;
       HGGame.A := SNF.A (g:=G) ;
       HGGame.u := fun _ i _  _ => SNF.u i
    |}.

  Definition HGGame_2_SNFGame (G : HGGame.game) : SNF.game :=
    {| SNF.N := HGGame.N G ;
       SNF.A := HGGame.A (g:=G) ;
       SNF.u := HGGame.UG  (G:=G) ;
    |}.
      
  Definition SNFGame_2_BGame (G : SNF.game) : BGame.game :=
    {| BGame.N := SNF.N G ;
       BGame.A := SNF.A (g:=G) ;
       BGame.Theta := fun _ => unit_finType ;
       BGame.P_cond := fun _ _ => 1%R ;
       BGame.u := fun i bp _ => SNF.u i (proj_profile bp [ffun _ => tt]) ;
    |}.

  Search _ "imset".
  Check (_ : bprofile _ _) _.
  Definition BGame_2_HGGame (G : BGame.game) : HGGame.game. Admitted.
                                               (*:= 
    {| HGGame.N := [finType of {i : BGame.N G & BGame.Theta i}] ;
       HGGame.E := [set [set (existT _ i (theta i)) | i in BGame.N G] | theta in bprofile BGame.Theta _ _] ;
    |}. *)


  Check BGame.UE _.
  Check HGGame.UG _.
  Lemma lemma1 :
    forall (G : BGame.game) (i : BGame.N G) (t : BGame.Theta i) (bp : bprofile _ _),
    BGame.UE t bp = HGGame.UG (existT _ i t) bp.
  
End Game.

Module GamesM.
  Definition X := 1.
End GamesM.  

Check GamesM.SNF.u _ _.

Definition evaluation_structure.
Definition decision_problem.
Definition GEU.
Definition dist.
Definition SNF_game.
Definition profile.
Definition HG_game.
Definition global_utility.
Definition BGame.
Definition PiGame.
Definition bprofile.
Definition UE.
Definition eqNash.
Definition eqBay.
Definition UUGame.
Lemma is_decision_problem.
Lemma is_SNFGame
Lemma is_BGame.
Lemma is_PiGame.

Definition UUGame2HGGame.
Lemma HowsonRonsenthal.
Definition HGGame2SNFGame.
Definition UUGame2SNFGame.
 *)
