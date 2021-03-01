From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Section GeneralLemmae.

  Lemma eqType_dec (T : eqType) :
    forall t1 t2 : T, t1 = t2 \/ t1 <> t2.
  Proof.
  move => t1 t2.
  case (boolP (t1 == t2)) => /eqP H.
  - by apply or_introl.
  - by apply or_intror.
  Qed.

End GeneralLemmae.




Section EvalStruct.

  (* Evaluation structure: domains, orders and operators for GEU *)

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

  (* The asymetric part of preceq *)
  Definition prec T (preceq : rel T) : rel T :=
    fun t1 t2 => (preceq t1 t2) && ~~ (preceq t2 t1).

End EvalStruct.







Section Games.

  Section Profiles.

    Implicit Type (N : finType).

    (* Profile for classical games *)
    Definition profile (N : finType) (X : N -> eqType) := {dffun forall i, X i}.

    (* Finite profile *)
    Definition fprofile N (X : N -> finType) := {dffun forall i, X i}.

    (* Change the strategy of a given player in a given profile *)
    Definition move N X (p : profile X) (i : N) (pi : X i) : profile X :=
      [ffun j => match boolP (i == j) with
                 | AltTrue h => eq_rect _ X pi _ (eqP h)
                 | AltFalse _ =>  p j
                 end].



    (* Profile for incomplete games *)
    Definition iprofile N (T : N -> finType) (X : N -> eqType) :=
      {dffun forall i, T i -> X i}.

    Definition iprofile_flatten N (T : N -> finType) X (p : iprofile T X)
      : profile (fun it => X (projT1 it)) :=
      [ffun it => p (projT1 it) (projT2 it)].

    Definition proj_iprofile N (T : N -> finType) X (p : iprofile T X)
      : profile T -> profile X :=
      fun theta => [ffun i => p i (theta i)].

    Definition proj_flatprofile N (T : N -> finType) X
               (p : profile (fun it => X (projT1 it)))
      : profile T -> profile X :=
      fun theta => [ffun i => p (existT _ i (theta i))].

    Lemma proj_iprof_flatprof N (T : N -> finType) X (p : iprofile T X) theta :
      (proj_iprofile p theta) = (proj_flatprofile (iprofile_flatten p) theta).
    Proof.
    by apply eq_dffun => i ; rewrite ffunE.
    Qed.

    
    Definition bmove N T X (p : iprofile T X) (i : N) ti xi
      : iprofile T X :=
      [ffun j => fun tj => match boolP (i == j) with
                           | AltTrue h =>
                             let ti' := eq_rect _ T ti _ (eqP h) in
                               if ti' == tj
                               then eq_rect i X xi j (eqP h)
                               else p j tj
                           | AltFalse _ => p j tj
                           end].



    Lemma move_bmove N T X (p : iprofile T X) (it : {i : N & T i})
          (xi : X (projT1 it)) :
      (@move _ _ (iprofile_flatten p) it xi)
      = (iprofile_flatten (bmove p (projT2 it) xi)).
    Proof.
    apply eq_dffun => it' //=.
    rewrite !ffunE.
    case (boolP (@eq_op (Finite.eqType (tag_finType T)) it it')) => H1 ;
    case (boolP (projT1 it == projT1 it')) => H2 //=.
    - case (boolP ((eq_rect _ _ (projT2 it) (projT1 it')  (@elimT
            (@eq (Finite.sort N) _ _) _ eqP H2)) == (projT2 it'))) => H3.
      + rewrite (rew_map X _ (eqP H1) xi).
          by rewrite (Eqdep_dec.eq_proofs_unicity
                (@eqType_dec N) (f_equal _ (eqP H1))(eqP H2)).
      + move/eqP in H3.
        have Hcontra := projT2_eq (eqP H1).
        rewrite (Eqdep_dec.eq_proofs_unicity (@eqType_dec N)
                  (projT1_eq (eqP H1)) (eqP H2)) in Hcontra.
          by contradiction.
    - move /eqP in H2.
      rewrite (eqP H1) in H2.
        by contradiction.
    - case (boolP ((eq_rect _ _ (projT2 it) (projT1 it')  (@elimT
            (@eq (Finite.sort N) _ _) _ eqP H2)) == (projT2 it'))) => H3 //.
      have Hcontra := eq_sigT it it' (eqP H2) (eqP H3).
      move /eqP in H1.
        by contradiction.
    Qed.


  End Profiles.

End Games.








Module NFGame.

  (* Classical SNF games *)

  Record game (player : finType) : Type :=
    { outcome : player -> Type ;
      action : player -> finType ;
      utility : forall i, profile action -> outcome i ;
      preceq : forall i, rel (outcome i) ; 
    }.

  Definition NashEqb player (g : game player)
    : pred (profile (action g)) :=
    fun p =>
    [forall i : player,
     forall ai : action g i,
        ~~ prec (@preceq _ _ _) (utility i p) (utility i (move p ai))].

  Definition NashEq player (g : game player) (p : profile (action g))
    : Prop :=
    forall (i : player) (ai : action g i),
    ~ prec (@preceq _ _ _) (utility i p) (utility i (move p ai)).

  Lemma NashEqP player (g : game player) (p : profile (action g)) :
    reflect (NashEq p) (NashEqb p).
  Proof.
  case (boolP (NashEqb p)) ; constructor ; move: i.
  - move /forallP => H i ; move: (H i).
    move /forallP => H2 ai ; move: (H2 ai) => H0.
      exact : (negP H0).
  - move /forallPn => H ; destruct H ; move : H.
    move /forallPn => H ; destruct H ; move : H.
    move /negPn => H Hne.
      by destruct (Hne x x0).
  Qed.


End NFGame.

Module HGGame.

  (* Hyper-graphical games with player-dependant-oplus-operator *)

  Record game (player : finType) : Type :=
    { local_game : finType ;
      plays : local_game -> pred player ;
      outcome : player -> Type ;
      outcome0 : forall i, outcome i ;
      oplus : forall i, Monoid.com_law (outcome0 i) ;
      preceq : forall i, rel (outcome i) ;
      action : player -> finType ;
      local_utility : local_game ->
                      forall i, profile action -> outcome i ;
    }.

  Definition global_utility player (g : game player) (i : player)
             (p : profile (action g)) :=
    \big[oplus g i/outcome0 g i]_(lg : local_game g | plays lg i)
     local_utility lg i p.

  Definition to_normal_form player (g : game player)
    : NFGame.game player :=
    {| NFGame.outcome := outcome g ;
       NFGame.preceq := @preceq _ g ;
       NFGame.action := action g ;
       NFGame.utility := @global_utility _ g ;
    |}.

  Definition NashEqb player (g : game player) :=
    @NFGame.NashEqb _ (to_normal_form g).

  Definition NashEq player (g : game player) :=
    @NFGame.NashEq _ (to_normal_form g).

  Lemma NashEqP player (g : game player) (p : profile (action g))
    : reflect (NashEq p) (NashEqb p).
  Proof. exact: NFGame.NashEqP. Qed.

  Lemma NashEq_HG_NFb player (g : game player) p :
    NashEqb p = @NFGame.NashEqb _ (to_normal_form g) p.
  Proof. by []. Qed.

  Lemma nashEq_HG_NF player (g : game player) p :
    NashEq p <-> @NFGame.NashEq _ (to_normal_form g) p.
  Proof. by []. Qed.

End HGGame.




Module IGame.

  (* Incomplete games such as bayesian games and possibilistic games *)

  Record game (player : finType) : Type :=
    { evalst : player -> eval_struct ;
      signal : player -> finType ;
      action : player -> finType ;
      utility : forall i : player,
        profile action -> profile signal -> U (evalst i) ;
      belief : forall i : player, profile signal -> W (evalst i) ;
    }.

  Definition GEutility player (g : game player) (i : player) t p :=
    \big[oplus (evalst g i)/V0 (evalst g i)]_(
     theta : fprofile (signal g) | (theta i) == t)
     otimes (belief i theta) (utility i (proj_iprofile p theta) theta).

  Definition to_hggame player (g : game player) : HGGame.game _ :=
    {| HGGame.local_game := [finType of fprofile (signal g)] ;
       HGGame.plays := fun theta it => theta (projT1 it) == projT2 it ;
       HGGame.outcome := fun it => V _ ;
       HGGame.outcome0 := fun it => V0 _ ;
       HGGame.oplus := fun it => oplus _ ;
       HGGame.preceq := fun it => @preceq_V _ ;
       HGGame.action := fun it => action g _ ;
       HGGame.local_utility := fun theta it p =>
           otimes (belief (projT1 it) theta)
              (utility (projT1 it) (proj_flatprofile p theta) theta) ;
    |}.

  Definition to_normal_form player (g : game player)
    : NFGame.game _ :=
    HGGame.to_normal_form (to_hggame g).

  Definition NashEqb player (g : game player)
    : pred (iprofile (signal g) (action g)) :=
    fun bp =>
    [forall i : player,
     forall t : signal g i,
     forall ai : action g i,
          ~~ prec (@preceq_V _) (GEutility t bp)
             (GEutility t (bmove bp t ai)) ].

  Definition NashEq player (g : game player) p : Prop :=
    forall i : player,
    forall t : signal g i,
    forall ai : action g i,
    ~ prec (@preceq_V _) (GEutility t p) (GEutility t (bmove p t ai)).


  Lemma NashEqP player (g : game player)
        (p : iprofile (signal g) (action g)) :
    reflect (NashEq p) (NashEqb p).
  Proof.
  case (boolP (NashEqb p)) ; constructor ; move: i.
  - move /forallP => H i ; move: (H i).
    move /forallP => H2 t ; move: (H2 t).
    move /forallP => H3 ai ; move: (H3 ai) => H0.
      exact : negP H0.
  - move /forallPn => H ; destruct H ; move : H.
    move /forallPn => H ; destruct H ; move : H.
    move /forallPn => H ; destruct H ; move : H.
    move /negPn => H2 Hne.
    have Hcontra := Hne x x0 x1.
      by contradiction.
  Qed.

End IGame.








Section HR.

  Lemma HowsonRosenthal :
    forall player (g : IGame.game player) i t p,
    @IGame.GEutility player g i t p
    = @HGGame.global_utility _ (IGame.to_hggame g) (existT _ i t)
                             (iprofile_flatten p).
  Proof.
  rewrite /IGame.GEutility /HGGame.global_utility
          /IGame.to_hggame => player g i t p //=.
  apply eq_bigr => theta Htheta.
    by rewrite -proj_iprof_flatprof.
  Qed.

  Lemma HowsonRosenthal_NashEqb :
    forall player (g : IGame.game player),
    forall  (p : iprofile (IGame.signal g) (IGame.action g)),
    @HGGame.NashEqb _ (IGame.to_hggame g) (iprofile_flatten p)
    = IGame.NashEqb p.
  Proof.
  move => player g p.
  apply /NFGame.NashEqP /IGame.NashEqP => /=.
  - rewrite /NFGame.NashEq /IGame.NashEq => /= H i t ai.
    move : (H (existT _ i t) ai).
      by rewrite {1}/iprofile_flatten !HowsonRosenthal move_bmove.
  - rewrite /NFGame.NashEq /IGame.NashEq => /= H it ai.
    have H' := (H (projT1 it) (projT2 it) ai).
      by rewrite {1 2 3 4}(sigT_eta it) move_bmove -!HowsonRosenthal.
  Qed.

  Lemma HowsonRosenthal_NashEq :
    forall player (g : IGame.game player),
    forall  (p : iprofile (IGame.signal g) (IGame.action g)),
    @HGGame.NashEq _ (IGame.to_hggame g) (iprofile_flatten p)
    <-> IGame.NashEq p.
  Proof.
  split => H.
  - apply/IGame.NashEqP ; move/HGGame.NashEqP in H.
      by rewrite -(HowsonRosenthal_NashEqb p).
  - apply/HGGame.NashEqP ; move/IGame.NashEqP in H.
      by rewrite (HowsonRosenthal_NashEqb p).
  Qed.

End HR.








