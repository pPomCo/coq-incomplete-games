From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import algebraic_HR.



Section GeneralLemmae.


  Lemma iter_add0:
    forall n, iter n (addn 0) 0 = 0.
  Proof. by elim. Qed.

  Lemma neqb_eqf (a b : bool) :
    (a != b) = (a == ~~b).
  Proof. by case a ; case b. Qed.

End GeneralLemmae.




  
Section Examples.

  (* Examples from the paper *)

  Lemma move_bool_eq (N : finType) :
    forall (b : bool_finType) (i : N),
    @move N _ [ffun _ => b] i b = [ffun _ => b].
  Proof.
  move => b i.
  rewrite /move (eq_dffun (fun _ => b)) => // j.
  case (boolP (i == j)) => Hij ; last by rewrite ffunE.
  exact : rew_const.
  Qed.


  Definition player3 := [finType of 'I_3].
  Definition player4 := [finType of 'I_4].
  
  Section Example1.

    (* Example 1.
       4 agents like to have lunch together. 
       They can have lunch in R1 or R2 (modelized with R1=true and R2=false).
       They want to eat with the people they like the most *)

    Definition example1 (aff : player4 -> player4 -> nat) : NFGame.game player4 :=
      {| NFGame.outcome := fun _ => nat ;
         NFGame.preceq := fun _ => leq ;
         NFGame.action := fun _ => bool_finType ;
         NFGame.utility :=
           fun i p => \sum_(j | (i != j) && (p i == p j)) aff i j ;
      |}.

    Lemma utility_allsame_eq4 i (b : NFGame.action (example1 (fun _ _ => 1)) i) :
      @NFGame.utility _ (example1 (fun _ _ => 1)) i [ffun _ => b] = 3.
    Proof.
    simpl ; rewrite (eq_bigl [pred j | j \in (setT :\ i)]) => /=.
    - rewrite big_const => /=.
      have := cardsD1 i setT.
      rewrite cardsT in_setT card_ord add1n => /= H.
      have H2 := eq_add_S _ _ H.
        by rewrite -H2.
    - move => j .
      case (boolP (i == j)) => H /=.
      + by rewrite in_setD1 (eqP H) eqxx.
      + rewrite eq_sym in H.
          by rewrite !ffunE eqxx in_setD1 in_setT H.
    Qed.

    Lemma utility_move_eq0 i (b : NFGame.action (example1 (fun _ _ => 1)) i) :
      @NFGame.utility _ (example1 (fun _ _ => 1)) i (@move _ _ [ffun _ => b] i (~~b)) = 0.
    Proof.
    simpl.
    rewrite (eq_bigr (fun _ => 0)) => //= [|j /andP H].
    - by rewrite big_const iter_add0.
    - destruct H.
      move: H0.
      rewrite !ffunE.
      case (boolP (i == i)) => H1 ; case (boolP (i == j)) => H2.
      + have H' := H. rewrite (eqP H2) in H'. move/eqP in H' ; contradiction.
      + by rewrite f_equal_dep ; case b. 
      + move/eqP in H1 ; contradiction.
      + move/eqP in H1 ; contradiction.
    Qed.      

    
    Lemma NashEq_ex1 (b : bool) :
      @NFGame.NashEq _ (example1 (fun _ _ => 1)) [ffun _ => b].
    Proof.
    move => i ai.
    case (boolP (ai == b)) => Hai.
    - rewrite (eqP Hai) move_bool_eq /prec.
        by destruct (NFGame.preceq (NFGame.utility i _) (NFGame.utility i _)).
    - rewrite neqb_eqf in Hai.
        by rewrite (eqP Hai) utility_allsame_eq4 utility_move_eq0. 
    Qed.

  End Example1.




  Section Example2.

    Definition example2 (aff : player4 -> player4 -> nat) (tps : player4 -> player4 -> nat) : NFGame.game player4 :=
      {| NFGame.outcome := fun _ => prod nat nat ;
         NFGame.preceq := fun _ => fun x y => leq x.1 y.1 && leq x.2 y.2 ;
         NFGame.action := fun _ => bool_finType ;
         NFGame.utility :=
           fun i p => (\sum_(j | (i != j) && (p i == p j)) aff i j,
                       \sum_(j | (i != j) && (p i == p j)) tps i j) ;
      |}.

    Lemma NashEq_ex2 :
      forall (tps : player4 -> player4 -> nat),
      @NFGame.NashEq _ (example2 (fun _ _ => 1) tps) [ffun _ => true].
    Proof.
    move => tps i ai.
    case (boolP ai) => Hai.
    - rewrite move_bool_eq /prec.
        by destruct (NFGame.preceq (NFGame.utility i _) (NFGame.utility i _)).
    - by admit.
    Admitted.

  End Example2.  



  Section Example3.
(*
    Check seq_sub_finType [:: (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)].

    Definition example3 (aff : player4 -> player4 -> nat) (tps : player4 -> player4 -> nat) : HGGame.hggame player4 :=
      {| HGGame.local_game := seq_sub_finType [:: (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)] ;
         HGGame.plays := fun lg => match lg with
                                   | (1,2) => fun i => i == 1
                                   | _ => fun i => false
                                   end ;
         HGGame.outcome := fun _ => prod nat nat ;
         HGGame.outcome0 := fun _ => (0,0) ;
         HGGame.oplus := fun _ x y => (x.1+y.1, x.2+y.2) ;
         HGGame.preceq := fun _ => fun x y => leq x.1 y.1 && leq x.2 y.2 ;
         HGGame.action := fun _ => bool_finType ;
         HGGame.local_utility :=
           fun lg i p => if HGGame.plays lg i then (aff lg.1 lg.2, tps lg.1 lg.2) else (0,0) ;
      |}.



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
*)


  End Example3.

End Examples.




