From mathcomp Require Import all_ssreflect ssrbool finmap finset.
From mathcomp Require Import all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.







Section EvalStruct.

  (* Structure d'évaluation. Contient les opérateurs, les domaines et leurs ordres *)

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


  
  Section Profiles.
    (* Profils (de stratégies, de signaux, etc.) *)

    (* Domaines *)
    Variables (N : finType)
              (T : N -> finType)
              (X : N -> Type).


    (* Profil classique : une action par joueur *)
    Definition profile := {ffun forall i, X i}.

    (* Profil à co-domaine fini *)
    Definition fprofile := {dffun forall i, T i}.

    (* Profil "bayésien" : une action par joueur et par signal *)
    Definition bprofile := {ffun forall it : {i : N & T i}, X (projT1 it)}.

    (* Projection d'un profil "étant donné les signaux" *)
    Definition proj_profile (bp : bprofile) (theta : fprofile) : profile :=
      [ffun i => bp (existT _ i (theta i))].

    Definition move (p : profile) (i : N) (xi : X i) : profile :=
      [ffun j => match boolP (i == j) with
                 | AltTrue h => eq_rect _ _ xi _ (eqP h)
                 | AltFalse _ => p j
                 end].

    Definition bmove (bp : bprofile) (i : N) (t : T i) (xi : X i) : bprofile :=
      [ffun jt => match boolP (i == (projT1 jt)) with
                  | AltTrue h => eq_rect _ _ xi _ (eqP h)
                  | AltFalse _ => bp jt
                  end].

  End Profiles.


  Check bmove.
  Lemma move_bmove (N : finType) (T : N -> finType) (X : N -> Type) :
    forall (p : profile (fun it : tag_finType _ => _)) (i : N) (t : T i) (xi : X i),
    @move (tag_finType T) _ p (existT _ i t) xi = @bmove N T X p _ t xi.
  Proof.
  move => p i t xi.
  apply eq_dffun => //= it.
  Admitted.

  
End Games.






Module NormalForm.

  Record game (player : finType) : Type :=
    { outcome : player -> Type ;
      preceq : forall i, rel (outcome i) ; 
      action : player -> finType ;
      utility : forall i, profile action -> outcome i ;
    }.

  Definition NashEqb player (g : game player) : pred (profile (action g)) :=
    fun p =>
    [forall i : player,
      [forall ai : action g i,
        (ai == p i) || ~~ preceq (utility i p) (utility i (move p ai)) ]].

  Definition NashEq player (g : game player) (p : profile (action g)) : Prop :=
    forall (i : player) (ai : action g i),
    ai = p i \/ (~ preceq (utility i p) (utility i (move p ai))).

  Lemma NashEqP player (g : game player) (p : profile (action g)) : reflect (NashEq p) (NashEqb p).
  Proof.
  case (boolP (NashEqb p)) ; constructor ; move: i.
  - move /forallP => H i ; move: (H i).
    move /forallP => H2 ai ; move: (H2 ai).
    move /orP ; case => H0.
    + exact : or_introl (eqP H0).
    + exact : or_intror (negP H0).
  - move /forallPn => H ; destruct H ; move : H.
    move /forallPn => H ; destruct H ; move : H.
    move /norP ; case.
    move /eqP => H /negPn H2 Hne.
    destruct (Hne x x0) ; by contradiction.
  Qed.


End NormalForm.

Module HGGame.

  (* Hyper-graphical games with player dependant oplus operator *)

  Definition set2finType (T : finType) (s : {set T}) := seq_sub_finType (enum (s)).

  Record hggame (player : finType) : Type :=
    { local_game : finType ;
      plays : local_game -> pred player ;
      outcome : player -> Type ;
      outcome0 : forall i, outcome i ;
      oplus : forall i, Monoid.com_law (outcome0 i) ;
      preceq : forall i, rel (outcome i) ;
      action : player -> finType ;
      local_utility : local_game -> forall i, profile action -> outcome i ; }.

  Check oplus _ _.
  Check outcome0 _ _.

  Definition global_utility player (g : hggame player) (i : player) (p : profile (action g)) :=
    \big[oplus g i/outcome0 g i]_(lg : local_game g | plays lg i) local_utility lg i p.

  Definition to_normal_form player (g : hggame player) : NormalForm.game player :=
    {| NormalForm.outcome := outcome g ;
       NormalForm.preceq := @preceq _ g ;
       NormalForm.action := action g ;
       NormalForm.utility := @global_utility _ g ; |}.

  Definition NashEqb player (g : hggame player) := @NormalForm.NashEqb _ (to_normal_form g).
  Definition NashEq player (g : hggame player) := @NormalForm.NashEq _ (to_normal_form g).

  Lemma NashEqP player (g : hggame player) (p : profile (action g)) : reflect (NashEq p) (NashEqb p).
  Proof.
  exact: NormalForm.NashEqP.
  Qed.

  Lemma NashEq_HG_NFb player (g : hggame player) p :
    NashEqb p = @NormalForm.NashEqb _ (to_normal_form g) p.
  Proof.
      by compute.
  Qed.

  Lemma nashEq_HG_NF player (g : hggame player) p :
    NashEq p <-> @NormalForm.NashEq _ (to_normal_form g) p.
  Proof.
      by compute.
  Qed.

End HGGame.

(*
Search _ "proj".
Require Extraction.
Extraction proj1_sig.
Extraction projT1.
*)


Module BGame.

  Record bgame (player : finType) : Type :=
    { evalst : player -> eval_struct ;
      signal : player -> finType ;
      action : player -> finType ;
      utility : forall i : player, profile action -> profile signal -> U (evalst i) ;
      belief : forall i : player, profile signal -> W (evalst i) ; }.

  Definition GEutility player (g : bgame player) (i : player) (t : signal g i) (p : bprofile (signal g) (action g)) :=
    \big[oplus (evalst g i)/V0 (evalst g i)]_(theta : fprofile (signal g) | (theta i) == t)
     otimes (belief i theta) (utility i (proj_profile p theta) theta).

  Definition to_hggame player (g : bgame player) : HGGame.hggame _ :=
    {| HGGame.local_game := [finType of fprofile (signal g)] ;
       HGGame.plays := fun theta it => theta (projT1 it) == projT2 it ;
       HGGame.outcome := fun it => V _ ;
       HGGame.outcome0 := fun it => V0 _ ;
       HGGame.oplus := fun it => oplus _ ;
       HGGame.preceq := fun it => @preceq_V _ ;
       HGGame.action := fun it => action g _ ;
       HGGame.local_utility := fun theta it p => otimes (belief (projT1 it) theta) (utility (projT1 it) (proj_profile p theta) theta) ; |}.

  Definition to_normal_form player (g : bgame player) : NormalForm.game _ :=
    HGGame.to_normal_form (to_hggame g).

  Definition NashEqb player (g : bgame player) : pred (bprofile (signal g) (action g)) :=
    fun bp =>
    [forall i : player,
      [forall t : signal g i,
        [forall ai : action g i,
          (ai == bp (existT _ i t)) || ~~ preceq_V (GEutility t bp) (GEutility t (bmove bp t ai)) ]]].

  Definition NashEq player (g : bgame player) (p : bprofile (signal g) (action g)) : Prop :=
    forall i : player,
    forall t : signal g i,
    forall ai : action g i,
    (ai = p (existT _ i t)) \/ ~ preceq_V (GEutility t p) (GEutility t (bmove p t ai)).


  Lemma NashEqP player (g : bgame player) (p : bprofile (signal g) (action g)) :
    reflect (NashEq p) (NashEqb p).
  Proof.
  case (boolP (NashEqb p)) ; constructor ; move: i.
  - move /forallP => H i ; move: (H i).
    move /forallP => H2 t ; move: (H2 t).
    move /forallP => H3 ai ; move: (H3 ai).
    move /orP ; case => H0.
    + exact : or_introl (eqP H0).
    + exact : or_intror (negP H0).
  - move /forallPn => H ; destruct H ; move : H.
    move /forallPn => H ; destruct H ; move : H.
    move /forallPn => H ; destruct H ; move : H.
    move /norP ; case.
    move /eqP => H /negPn H2 Hne.
    have Hcontra := Hne x x0 x1.
    destruct Hcontra ; by contradiction.
  Qed.

End BGame.

Section HR.

  Lemma HowsonRosenthal :
    forall player (g : BGame.bgame player) i t p,
    @BGame.GEutility player g i t p = @HGGame.global_utility _ (BGame.to_hggame g) (existT _ i t) p.
  Proof.
  auto. (* Direct from the definitions *)
  Qed.




  Lemma HR2 :
    forall player (g : BGame.bgame player),
    let g' := BGame.to_hggame g in
    forall  (p : bprofile (BGame.signal g) (BGame.action g)),
    @HGGame.NashEqb _ g' p = BGame.NashEqb p.
  Proof.
  move => player g g' p.
  Set Printing All.
  rewrite /g'.
  Unset Printing All.
  apply /NormalForm.NashEqP => /=.
  case (boolP (BGame.NashEqb p)).
  - move /BGame.NashEqP => H it ai //=.
    move : (H _ (projT2 it) ai) => H2 ; destruct H2.
    + apply or_introl ; move : H0 => ->.
        by rewrite (sigT_eta it).
    + apply or_intror.
      move : H0 ; rewrite !HowsonRosenthal -move_bmove.
      Check (sigT_eta it). (* dep type error *)-
        by admit.
  - by admit.
  Admitted.


End HR.

