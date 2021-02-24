From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Section GeneralLemmae.
  Lemma finType_decidable (T : finType) :
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
    rewrite /move /bmove /iprofile_flatten.
    apply eq_dffun => it' //=.
    rewrite ffunE.
    case (boolP (@eq_op (Finite.eqType (tag_finType T)) it it')) => H1;
                          case (boolP (projT1 it == projT1 it')) => H2.
    - case (boolP ( @eq_op (Finite.eqType (T (projT1 it')))
           (eq_rect (projT1 it) _ (projT2 it) (projT1 it')
              (@elimT (@eq (Finite.sort N) (projT1 it) (projT1 it'))
                 (@eq_op (Finite.eqType N) (projT1 it) (projT1 it'))
                 (@eqP (Finite.eqType N) (projT1 it) (projT1 it'))
                 H2))
           (projT2 it'))) => H3.
      + rewrite (rew_map X (@projT1 _ _) (eqP H1) xi).
          by rewrite (Eqdep_dec.eq_proofs_unicity
                (@finType_decidable N) (f_equal _ (eqP H1))(eqP H2)).
      + move/eqP in H3.
        have Hcontra := projT2_eq (eqP H1).
        rewrite (Eqdep_dec.eq_proofs_unicity (@finType_decidable N)
                  (projT1_eq (eqP H1)) (eqP H2)) in Hcontra.
        contradiction.
    - move /eqP in H2.
      have Hcontra := projT1_eq (eqP H1).
      contradiction.
    - case (boolP ( @eq_op (Finite.eqType (T (projT1 it')))
           (eq_rect (projT1 it) _ (projT2 it) (projT1 it')
              (@elimT (@eq (Finite.sort N) (projT1 it) (projT1 it'))
                 (@eq_op (Finite.eqType N) (projT1 it) (projT1 it'))
                 (@eqP (Finite.eqType N) (projT1 it) (projT1 it'))
                 H2))
           (projT2 it'))) => H3.
      + have Hcontra := eq_sigT it it' (eqP H2) (eqP H3).
        move /eqP in H1.
        contradiction.
      + by rewrite ffunE.
    - by rewrite ffunE.
    Qed.
  End Profiles.

End Games.





  Check profile.




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
      [forall ai : action g i,
        ~~ prec (@preceq _ _ _) (utility i p) (utility i (move p ai))
    ]].

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

  Record hggame (player : finType) : Type :=
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

  Definition global_utility player (g : hggame player) (i : player)
             (p : profile (action g)) :=
    \big[oplus g i/outcome0 g i]_(lg : local_game g | plays lg i)
     local_utility lg i p.

  Definition to_normal_form player (g : hggame player)
    : NFGame.game player :=
    {| NFGame.outcome := outcome g ;
       NFGame.preceq := @preceq _ g ;
       NFGame.action := action g ;
       NFGame.utility := @global_utility _ g ;
    |}.

  Definition NashEqb player (g : hggame player) :=
    @NFGame.NashEqb _ (to_normal_form g).

  Definition NashEq player (g : hggame player) :=
    @NFGame.NashEq _ (to_normal_form g).

  Lemma NashEqP player (g : hggame player) (p : profile (action g))
    : reflect (NashEq p) (NashEqb p).
  Proof. exact: NFGame.NashEqP. Qed.

  Lemma NashEq_HG_NFb player (g : hggame player) p :
    NashEqb p = @NFGame.NashEqb _ (to_normal_form g) p.
  Proof. by compute. Qed.

  Lemma nashEq_HG_NF player (g : hggame player) p :
    NashEq p <-> @NFGame.NashEq _ (to_normal_form g) p.
  Proof. by compute. Qed.

End HGGame.




Module BGame.

  Record bgame (player : finType) : Type :=
    { evalst : player -> eval_struct ;
      signal : player -> finType ;
      action : player -> finType ;
      utility : forall i : player,
        profile action -> profile signal -> U (evalst i) ;
      belief : forall i : player, profile signal -> W (evalst i) ;
    }.

  Definition GEutility player (g : bgame player) (i : player) t p :=
    \big[oplus (evalst g i)/V0 (evalst g i)]_(
     theta : fprofile (signal g) | (theta i) == t)
     otimes (belief i theta) (utility i (proj_iprofile p theta) theta).

  Definition to_hggame player (g : bgame player) : HGGame.hggame _ :=
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

  Definition to_normal_form player (g : bgame player)
    : NFGame.game _ :=
    HGGame.to_normal_form (to_hggame g).

  Definition NashEqb player (g : bgame player)
    : pred (iprofile (signal g) (action g)) :=
    fun bp =>
    [forall i : player,
      [forall t : signal g i,
        [forall ai : action g i,
          ~~ prec (@preceq_V _) (GEutility t bp)
             (GEutility t (bmove bp t ai)) ]]].

  Definition NashEq player (g : bgame player) p : Prop :=
    forall i : player,
    forall t : signal g i,
    forall ai : action g i,
    ~ prec (@preceq_V _) (GEutility t p) (GEutility t (bmove p t ai)).


  Lemma NashEqP player (g : bgame player)
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

End BGame.








Section HR.

  Lemma HowsonRosenthal :
    forall player (g : BGame.bgame player) i t p,
    @BGame.GEutility player g i t p
    = @HGGame.global_utility _ (BGame.to_hggame g) (existT _ i t)
                             (iprofile_flatten p).
  Proof.
  rewrite /BGame.GEutility /HGGame.global_utility
          /BGame.to_hggame => player g i t p //=.
  apply eq_bigr => theta Htheta.
    by rewrite -proj_iprof_flatprof.
  Qed.




  Lemma HowsonRosenthal_NashEqb :
    forall player (g : BGame.bgame player),
    forall  (p : iprofile (BGame.signal g) (BGame.action g)),
    @HGGame.NashEqb _ (BGame.to_hggame g) (iprofile_flatten p)
    = BGame.NashEqb p.
  Proof.
  move => player g p.
  apply /NFGame.NashEqP /BGame.NashEqP => /=.
  - rewrite /NFGame.NashEq /BGame.NashEq => /= H i t ai.
    move : (H (existT _ i t) ai).
      by rewrite {1}/iprofile_flatten !HowsonRosenthal move_bmove.
  - rewrite /NFGame.NashEq /BGame.NashEq => /= H it ai.
    have H' := (H (projT1 it) (projT2 it) ai).
      by rewrite {1 2 3 4}(sigT_eta it) move_bmove -!HowsonRosenthal.
  Qed.

  Lemma HowsonRosenthal_NashEq :
    forall player (g : BGame.bgame player),
    forall  (p : iprofile (BGame.signal g) (BGame.action g)),
    @HGGame.NashEq _ (BGame.to_hggame g) (iprofile_flatten p)
    <-> BGame.NashEq p.
  Proof.
  split => H.
  - apply/BGame.NashEqP ; move/HGGame.NashEqP in H.
      by rewrite -(HowsonRosenthal_NashEqb p).
  - apply/HGGame.NashEqP ; move/BGame.NashEqP in H.
      by rewrite (HowsonRosenthal_NashEqb p).
  Qed.
End HR.











Section Examples.

  Definition coordination_game : NFGame.game [finType of 'I_2] :=
    {| NFGame.outcome := fun _ => nat ;
       NFGame.preceq := fun _ => leq ;
       NFGame.action := fun _ => bool_finType ;
       NFGame.utility :=
         fun _ p => if p (inord 0) == p (inord 1) then 1 else 0
    |}.

  Eval compute in  NFGame.action coordination_game (inord 0).

End Examples.




