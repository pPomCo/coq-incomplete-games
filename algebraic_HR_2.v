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

    Implicit Type (N : finType).

    Definition profile N (X : N -> Type) := forall i, X i.

    Definition fprofile N (X : N -> finType) := {dffun forall i, X i}.

    Definition fprofile_of_profile N (X : N -> finType) (p : profile X) : fprofile X :=
      [ffun i => p i].


    Definition move N X (p : profile X) (i : N) (pi : X i) : profile X :=
      fun j => match boolP (i == j) with
               | AltTrue h => eq_rect _ _ pi _ (eqP h)
               | AltFalse _ =>  p j
               end.



    Definition iprofile N (T : N -> finType) (X : N -> Type) :=
      forall (i : N) (t : T i), X i.

    Definition iprofile_flatten N T X (p : iprofile T X) : profile (fun it : {i : N & T i} => X (projT1 it)) :=
      fun it => p (projT1 it) (projT2 it).

    Definition proj_flatprofile N (T : N -> finType) X (p : profile (fun it : {i : N & T i} => X (projT1 it))) (theta : profile T) : profile X :=
      fun i => p (existT _ i (theta i)).

    Definition proj_iprofile N (T : N -> finType) X (p : iprofile T X) (theta : profile T) : profile X :=
      fun i => p i (theta i).


    Lemma proj_iprof_flatprof N (T : N -> finType) X (p : iprofile T X) theta :
      forall j, (proj_iprofile p theta) j = (proj_flatprofile (iprofile_flatten p) theta) j.
    Proof.
        by [].
    Qed.
    
    
    Check eq_rect _ _ _ _ _.
    
    Definition bmove' N T X (p : iprofile T X) (i : N) (ti : T i) (xi : X i) : iprofile T X.
    move => j tj.
    case (boolP (i == j)) => Hi.
    Check eq_sym _ _.
    have Hj := Hi ; rewrite eq_sym in Hj.
    - have ti' := eq_rect _ T ti _ (eqP Hi).
      case (boolP (ti' == tj)) => Htj.
      + exact : eq_rect _ X xi _ (eqP Hi).
      + exact : p j tj.
    - exact : p j tj.
    Defined.
    Print bmove'.

    Definition bmove N T X (p : iprofile T X) (i : N) (ti : T i) (xi : X i) : iprofile T X :=
      fun j tj => match boolP (i == j) with
                  | AltTrue h =>
                    let ti' := eq_rect _ T ti _ (eqP h) in
                    if ti' == tj then eq_rect i X xi j (eqP h) else p j tj
                  | AltFalse _ => p j tj
                  end.


    Lemma move_bmove N T X (p : iprofile T X) (i : N) (ti : T i) xi :
      (@move _ _ (iprofile_flatten p) (existT _ i ti) xi) = (iprofile_flatten (bmove p ti xi)).
    Admitted.

    
  End Profiles.


  (*
  Section Profiles.
    (* Profils (de stratégies, de signaux, etc.) *)

    (* Domaines *)
    Variables (N : finType)
              (T : N -> finType)
              (X : N -> Type).


    (* Profil classique : une action par joueur *)
    Definition profile := {ffun forall i, X i}.
    Definition profile' := forall i, X i.

    (* Définir les profils comme des fonctions et à l'occasion les caster en finType *)

    Definition profile'_profile (p : profile') : profile.
    exact : [ffun i => p i].
    Qed.

    (* Profil à co-domaine fini *)
    Definition fprofile := {dffun forall i, T i}.
    Definition fprofile' := forall i, T i.

    Definition fprofile'_fprofile (p : fprofile') : fprofile.
    exact : [ffun i => p i].
    Qed.

    Definition profile_finType
    

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

    (* ecast == eq_rect 
    Search _ "cast".
    Check fun m n (e : m = n) (x : 'I_m) => ecast i ('I_ i) e x. 
     *)
    
  End Profiles.
  Check @bprofile .
  (*
  Definition bprofile2 :=
    fun (N : finType) (T : N -> finType) X (p : @bprofile N T X) => _ : @profile {i : N & T i}X.
   *)
  
  Lemma move_bmove (N : finType) (T : N -> finType) (X : N -> Type) :
    forall (p : profile (fun it : tag_finType _ => _)) (i : N) (t : T i) (xi : X i),
    @move (tag_finType T) _ p (existT _ i t) xi = @bmove N T X p _ t xi.
  Proof.
  move => p i t xi.
  apply eq_dffun => //= it.
  destruct boolP.
  destruct boolP.
  simpl.
  Check f_equal_dep.
  Search _ eq_rect.
  f_equal.
  case (boolP (existT (fun i0 : N => T i0) i t == it)).
  Admitted.
  )
*)  
End Games.







Module NFGame.

  Record game (player : finType) : Type :=
    { outcome : player -> Type ;
      action : player -> finType ;
      utility : forall i, profile action -> outcome i ;
      preceq : forall i, rel (outcome i) ; 
    }.

  (* Ordre : irreflexif ? *)
  
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


End NFGame.

Module HGGame.

  (* Hyper-graphical games with player dependant oplus operator *)

  (* Definition set2finType (T : finType) (s : {set T}) := seq_sub_finType (enum (s)). *)

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

  Definition to_normal_form player (g : hggame player) : NFGame.game player :=
    {| NFGame.outcome := outcome g ;
       NFGame.preceq := @preceq _ g ;
       NFGame.action := action g ;
       NFGame.utility := @global_utility _ g ; |}.

  Definition NashEqb player (g : hggame player) := @NFGame.NashEqb _ (to_normal_form g).
  Definition NashEq player (g : hggame player) := @NFGame.NashEq _ (to_normal_form g).

  Lemma NashEqP player (g : hggame player) (p : profile (action g)) : reflect (NashEq p) (NashEqb p).
  Proof.
  exact: NFGame.NashEqP.
  Qed.

  Lemma NashEq_HG_NFb player (g : hggame player) p :
    NashEqb p = @NFGame.NashEqb _ (to_normal_form g) p.
  Proof.
      by compute.
  Qed.

  Lemma nashEq_HG_NF player (g : hggame player) p :
    NashEq p <-> @NFGame.NashEq _ (to_normal_form g) p.
  Proof.
      by compute.
  Qed.


  (* NFGame 2 HGGame *)

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

  Definition GEutility player (g : bgame player) (i : player) (t : signal g i) (p : iprofile (signal g) (action g)) :=
    \big[oplus (evalst g i)/V0 (evalst g i)]_(theta : fprofile (signal g) | (theta i) == t)
     otimes (belief i theta) (utility i (proj_iprofile p theta) theta).

  Definition to_hggame player (g : bgame player) : HGGame.hggame _ :=
    {| HGGame.local_game := [finType of fprofile (signal g)] ;
       HGGame.plays := fun theta it => theta (projT1 it) == projT2 it ;
       HGGame.outcome := fun it => V _ ;
       HGGame.outcome0 := fun it => V0 _ ;
       HGGame.oplus := fun it => oplus _ ;
       HGGame.preceq := fun it => @preceq_V _ ;
       HGGame.action := fun it => action g _ ;
       HGGame.local_utility := fun theta it p => otimes (belief (projT1 it) theta) (utility (projT1 it) (proj_flatprofile p theta) theta) ; |}.

  Definition to_normal_form player (g : bgame player) : NFGame.game _ :=
    HGGame.to_normal_form (to_hggame g).

  Definition NashEqb player (g : bgame player) : pred (iprofile (signal g) (action g)) :=
    fun bp =>
    [forall i : player,
      [forall t : signal g i,
        [forall ai : action g i,
          (ai == bp i t) || ~~ preceq_V (GEutility t bp) (GEutility t (bmove bp t ai)) ]]].

  Definition NashEq player (g : bgame player) (p : iprofile (signal g) (action g)) : Prop :=
    forall i : player,
    forall t : signal g i,
    forall ai : action g i,
    (ai = p i t) \/ ~ preceq_V (GEutility t p) (GEutility t (bmove p t ai)).


  Lemma NashEqP player (g : bgame player) (p : iprofile (signal g) (action g)) :
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













Section Examples.

  Definition coordination_game : NFGame.game [finType of 'I_2] :=
    {| NFGame.outcome := fun _ => nat ;
       NFGame.preceq := fun _ => ltn ;
       NFGame.action := fun _ => bool_finType ;
       NFGame.utility := fun _ p => if [forall i, p i] then 1 else 0
    |}.

  Eval compute in  NFGame.action coordination_game (inord 0).

  Lemma coord_NashEq1 :
    @NFGame.NashEq _ coordination_game [ffun _ => true].
  Proof.
  Admitted.

  Lemma coord_NashEq2 :
    @NFGame.NashEq _ coordination_game [ffun _ => false].
  Admitted.

End Examples.






Section HR.

  Lemma HowsonRosenthal :
    forall player (g : BGame.bgame player) i t p,
    @BGame.GEutility player g i t p = @HGGame.global_utility _ (BGame.to_hggame g) (existT _ i t) (iprofile_flatten p).
  Proof.
      by []. (* Direct from the definitions *)
  Qed.




  Lemma HR2 :
    forall player (g : BGame.bgame player),
    forall  (p : iprofile (BGame.signal g) (BGame.action g)),
    @HGGame.NashEqb _ (BGame.to_hggame g) (iprofile_flatten p) = BGame.NashEqb p.
  Proof.
  move => player g p.
  apply /NFGame.NashEqP /BGame.NashEqP => /=.
  - rewrite /NFGame.NashEq /BGame.NashEq => /= H i t ai.
    move : (H (existT _ i t) ai).
    Check move_bmove.
      by rewrite {1}/iprofile_flatten !HowsonRosenthal -move_bmove => //=.
  - rewrite /NFGame.NashEq /BGame.NashEq => /= H it ai.
    move : (H (projT1 it) (projT2 it) ai).
    rewrite {1}/iprofile_flatten !HowsonRosenthal -move_bmove => H2 //=.
    case H2 => H3.
    + exact : (or_introl H3).
    + apply or_intror => Hcontra.
      apply : H3.
      move : (sigT_eta it) ; move /eqP ; rewrite eq_sym ; move/eqP => Hsig.
      (* rewrite Hsig ; exact : Hcontra *) (* dependent type error *)
  Admitted.      


End HR.
