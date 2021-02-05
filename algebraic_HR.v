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

  Definition NashEq player (g : game player) : pred (profile (action g)) :=
    fun p =>
    [forall i : player,
      [forall ai : action g i,
        (ai == p i) || ~~ preceq (utility i p) (utility i (move p ai)) ]].

  Definition NashEq2 player (g : game player) (p : profile (action g)) : Prop :=
    forall i : player,
    forall ai : action g i,
    ai = p i \/ (~ preceq (utility i p) (utility i (move p ai))).

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

  Definition NashEq player (g : hggame player) := @NormalForm.NashEq _ (to_normal_form g).
  Definition NashEq2 player (g : hggame player) := @NormalForm.NashEq2 _ (to_normal_form g).

  (*  
  Record hyper_game (T I : finType) : Type :=
    { player : I -> {set T} ;
      local_game : forall i : I, NormalForm.game (set2finType (player i)) ; 
      action_axiom :
        forall t : T,
        exists At : finType,
        forall i : I,
        t \in NormalForm.player (local_game i) -> NormalForm.action (local_game i) = At ; }.
   *)

End HGGame.

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

  Definition NashEq player (g : bgame player) : pred (bprofile (signal g) (action g)) :=
    fun bp =>
    [forall i : player,
      [forall t : signal g i,
        [forall ai : action g i,
          (ai == bp (existT _ i t)) || ~~ preceq_V (GEutility t bp) (GEutility t (bmove bp t ai)) ]]].

  Definition NashEq2 player (g : bgame player) (p : bprofile (signal g) (action g)) : Prop :=
    forall i : player,
    forall t : signal g i,
    forall ai : action g i,
    (ai = p (existT _ i t)) \/ ~ preceq_V (GEutility t p) (GEutility t (bmove p t ai)).
  
End BGame.

Section HR.

  Lemma HR :
    forall player (g : BGame.bgame player) i t p,
    @BGame.GEutility player g i t p = @HGGame.global_utility _ (BGame.to_hggame g) (existT _ i t) p.
  Proof.
  auto. (* Direct from the definitions *)
  Qed.




  Lemma azerty player g i t p a :
    @bmove player (@BGame.signal player g) (fun x : Finite.sort player => Finite.sort (@BGame.action player g x)) p i t a
    =
    (@move
     (@tag_finType player (@BGame.signal player g))
     (fun x : @sigT (Finite.sort player) (fun i : Finite.sort player => Finite.sort (@BGame.signal player g i)) =>
      Finite.sort (@BGame.action player g (@projT1 (Finite.sort player) (fun i : Finite.sort player => Finite.sort (@BGame.signal player g i)) x))) p
     (@existT (Finite.sort player) (fun i : Finite.sort player => Finite.sort (@BGame.signal player g i)) i t) a).
  Proof.
  apply eq_dffun => it.
  case (boolP
        (@eq_op (Finite.eqType (@tag_finType player (@BGame.signal player g)))
                (@existT (Finite.sort player) (fun i0 : Finite.sort player => Finite.sort (@BGame.signal player g i0)) i t) it)) ;
    case ( boolP (@eq_op (Finite.eqType player) i (@projT1 (Finite.sort player) (fun i0 : Finite.sort player => Finite.sort (@BGame.signal player g i0)) it))) => //= Hi Hit.
  - by admit.
  - have Hit' := Hit.
    have Hi' := Hi.
    move/eqP in Hit'.
    rewrite -Hit' in Hi'.
    move: Hi' => //=.
      by rewrite eqxx.
  - have Hi' := Hi.
    move/eqP in Hi'.
      by admit.
  Admitted.


      
  Lemma HR2 :
    forall player (g : BGame.bgame player) p,
    @NormalForm.NashEq2 _ (BGame.to_normal_form g) p -> BGame.NashEq2 p.
  Proof.
  rewrite /BGame.NashEq2  /NormalForm.NashEq2.  
  move => player g p HNF i t a.
  move: (HNF (existT _ i t) a).
  rewrite !HR.
  (* Check move_bmove _.  <<-- What TODO? *)
  rewrite azerty => //=.
  Qed.

End HR.

