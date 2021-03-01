From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import algebraic_HR.



Section GeneralLemmae.


  Lemma neqb_eqf (a b : bool) :
    (a != b) = (a == ~~b).
  Proof. by case a ; case b. Qed.


  Lemma card_ltn n :
    forall i : 'I_n,
    #|[pred j : 'I_n | j < i]| = i.
  Proof.
  induction i => //=.
  induction m.
  apply card0.
  Check (cardD1x _).
  Search _ (_ < _.+1).
  have th : is_true ((fun j => j < m.+1) m).
  exact : ltnSn.
  Admitted.

  
  Lemma big_addi {T : finType} :
    forall (P : pred T) (i : nat),
    \sum_(j | P j) i = #|P| * i.
  Proof.
  move => i P.
  rewrite big_const.
  elim : #|i| => // m IHm.
    by rewrite iterS IHm.
  Qed.

  

End GeneralLemmae.




  
Section Examples.

  (* Examples from the paper *)
  Definition player3 := [finType of 'I_3].
  Definition player4 := [finType of 'I_4].

  Definition player4_num i : player4 := inord i.

  Lemma card_player4_ltn2 (i : player4) :
    #|[pred j : player4 | (j < player4_num 2) == (i < player4_num 2)]| = 2.
  Proof.
  rewrite /player4_num inordK => //.
  case (boolP (i < 2)) => // Hi.
  - Search _ (card _) "D".
    Search _ (_ == true).
    Check (cardD1x).
    Search _ "ltn".
    rewrite (@cardD1x _ _ (inord 0)).
    rewrite (@cardD1x _ _ (inord 1)).
    Search _ "addn".
    rewrite addnA -{12}(addn0 2).
    Search _ addn subn.
    Search _ "addn".
    Search _ (_ + _ = _ -> _ = _ - _).
    Check addnC.
  Admitted.

  
  Section Example1.

    (* Example 1.
       4 agents like to have lunch together. 
       They can have lunch in R1 or R2 (modelized with R1=true and R2=false).
       They want to eat with the people they like the most *)

    Definition example1
               (aff : player4 -> player4 -> nat) : NFGame.game player4
      :=
      {| NFGame.outcome := fun _ => nat ;
         NFGame.preceq := fun _ => leq ;
         NFGame.action := fun _ => bool_finType ;
         NFGame.utility :=
           fun i p => \sum_(j | (j != i) && (p i == p j)) aff i j ;
      |}.

    
    Lemma NashEq_ex1 (b : bool) :
      let aff := fun i j => 1
      in
      @NFGame.NashEq _ (example1 aff) [ffun _ => b].
    Proof.
    move => aff i ai => /=.
    case (boolP (ai == b)) => Hai.
    - by rewrite (eqP Hai) move_constprof_eq /prec andbN.
    - rewrite neqb_eqf in Hai.
      rewrite /prec.
      rewrite move_constprofE eqxx (eqP Hai).
      rewrite {1}(eq_bigl (predC1 i)).
      + rewrite big_addi big_pred0 => /= [|j]; first by rewrite andbF.
        rewrite (move_constprofE b (~~b) i j).
        case (boolP (i == j)) => /eqP Hij ; first by rewrite Hij eqxx andFb.
          by rewrite (eq_sym _ b) -neqb_eqf eqxx andbF.
      + rewrite ffunE => j.
          by rewrite ffunE eqxx andbT.
    Qed.

  End Example1.




  Section Example2.

    Definition example2
               (aff : player4 -> player4 -> nat)
               (tps : player4 -> player4 -> nat) : NFGame.game player4
      :=
      {| NFGame.outcome := fun _ => prod nat nat ;
         NFGame.preceq := fun _ => fun x y => leq x.1 y.1 && leq x.2 y.2 ;
         NFGame.action := fun _ => bool_finType ;
         NFGame.utility :=
           fun i p => (\sum_(j | (j != i) && (p i == p j)) aff i j,
                       \sum_(j | (j != i) && (p i == p j)) tps i j) ;
      |}.

    Lemma NashEq_ex2a (b : bool):
      let aff := fun i j => 1
      in
      forall (tps : player4 -> player4 -> nat),
      @NFGame.NashEq _ (example2 aff tps) [ffun _ => b].
    Proof.
    move => aff tps i ai => /=.
    case (boolP (ai == b)) => Hai.
    - by rewrite (eqP Hai) move_constprof_eq /prec andbN.
    - rewrite neqb_eqf in Hai.
      rewrite move_constprofE eqxx (eqP Hai).
      rewrite (eq_bigl (predC1 i)) ;
        last by rewrite !ffunE => j ; rewrite ffunE eqxx andbT.
      rewrite big_addi (eq_bigl (predC1 i)) ;
        last by rewrite !ffunE => j ; rewrite ffunE eqxx andbT.
      rewrite (@big_pred0 _ _ _ _ _
          [pred j | (j != i) && (~~ b == move (N:=player4) (X:=fun=> bool_finType) [ffun=> b] (i:=i) (~~ b) j)]) => [|j /=];
        first by rewrite cardC1 card_ord.
      rewrite move_constprofE.
      case (boolP (i == j)) => /eqP Hij.
      + by rewrite Hij eqxx andFb.
      + by rewrite (eq_sym _ b) -neqb_eqf eqxx andbF.
    Qed.


    (* Ouch !*)
    Lemma NashEq_ex2b (b : bool) :
      let aff := fun i j => 1
      in
      let tps := fun i j => if (i < 2) == (j < 2) then 10 else 1
      in
      @NFGame.NashEq _ (example2 aff tps) [ffun i : player4 => if i < player4_num 2 then b else ~~b].
    Proof.
    - have th (j : player4) : (if j < player4_num 2 then b else ~~b) = [ffun k : player4 => if k < player4_num 2 then b else ~~b] j.
        by rewrite !inordK => // ; rewrite ffunE.
    - have th2 (j : player4) : (if j < player4_num 2 then ~~b else b) = [ffun k : player4 => if k < player4_num 2 then ~~b else b] j.
        by rewrite !inordK => // ; rewrite ffunE.

    - have th_pnum (j : player4) : j < player4_num 2 -> j < 2. by rewrite inordK.
    - have th_pnum' (j : player4) : ~~ (j < player4_num 2) -> (j < 2) = false.
        by move => H ; apply negbTE ; rewrite inordK in H.
    - have th_pnum'' (i j : player4) : (i < player4_num 2) = (j < player4_num 2) -> (i < 2) = (j < 2).
      case (boolP (i < player4_num 2)) => Hi ; case (boolP (j < player4_num 2)) => Hj.
      + by rewrite !th_pnum.
      + by rewrite (th_pnum _ Hi) th_pnum'.
      + by rewrite (th_pnum' _ Hi) th_pnum.
      + by rewrite (th_pnum' _ Hi) (th_pnum' _ Hj).
    - have th_pnum''' (i j : player4) : (i < player4_num 2) != (j < player4_num 2) -> (i < 2) == (j < 2) = false.
      case (boolP (i < player4_num 2)) => Hi ; case (boolP (j < player4_num 2)) => Hj.
      + by rewrite !th_pnum.
      + by rewrite (th_pnum _ Hi) th_pnum'.
      + by rewrite (th_pnum' _ Hi) th_pnum.
      + by rewrite (th_pnum' _ Hi) (th_pnum' _ Hj).

    - have th_ffun (i j : player4) : (j != i) && ([ffun i1 : player4 => if i1 < player4_num 2 then b else ~~ b] i == [ffun i1 : player4 => if i1 < player4_num 2 then b else ~~ b] j) = (j != i) && ((i < player4_num 2) == (j < player4_num 2)).
      rewrite !ffunE.
      case (i < player4_num 2) ; case (j < player4_num 2).
      + by rewrite eqxx.
      + by rewrite -neqb_eqf eqxx.
      + by rewrite (eq_sym _ b) -neqb_eqf eqxx.
      + by rewrite eqxx.

      

        
    - move => aff tps i ai => /=.
      case (boolP (ai == if i < player4_num 2 then b else ~~b)) => Hai.
      + rewrite (eqP Hai).
          by rewrite th -move_prof_eq /prec andbN.

      + have th_move (j : player4) : (j != i) && (move (N:=player4) (X:=fun=> bool_finType) [ffun i1 : player4 => if i1 < player4_num 2 then b else ~~ b] (i:=i) ai i == move (N:=player4) (X:=fun=> bool_finType) [ffun i1 : player4 => if i1 < player4_num 2 then b else ~~ b] (i:=i) ai j)
                                     = (j != i) && ((i < player4_num 2) != (j < player4_num 2)).
        case (boolP (j == i)) => /eqP H ; first by rewrite andFb.
        rewrite move_prof_ii move_prof_ij.
        rewrite neqb_eqf fun_if Bool.negb_involutive in Hai.
        rewrite !ffunE (eqP Hai).
        case (boolP (i < player4_num 2)) => Hi ; case (boolP (j < player4_num 2)) => Hj.
        * by rewrite (eq_sym _ b) -neqb_eqf eqxx.
        * by rewrite eqxx.
        * by rewrite eqxx.
        * by rewrite -neqb_eqf eqxx.
        * by rewrite eq_sym ; apply /eqP.

      + rewrite (eq_bigl (fun j => (j != i) && ((i < player4_num 2) == (j < player4_num 2)))) => [|j] ;
          last by rewrite th_ffun.
        rewrite big_addi.
        rewrite (eq_bigl (fun j => (j != i) && ((i < player4_num 2) == (j < player4_num 2)))) => [|j] ;
          last by rewrite th_ffun.
        rewrite (eq_bigr (fun _ => 10)) => [|j /andP H] ; 
           last destruct H ;
           last by rewrite /tps (th_pnum'' _ _ (eqP H0)) eqxx.
        rewrite big_addi.
        rewrite (eq_bigl (fun j => (j != i) && ((i < player4_num 2) != (j < player4_num 2)))) => [|j] ;
          last by rewrite th_move.
        rewrite big_addi.
        rewrite (eq_bigl (fun j => (j != i) && ((i < player4_num 2) != (j < player4_num 2)))) => [|j] ;
          last by rewrite th_move.
        rewrite (eq_bigr (fun _ => 1)) => [|j /andP H] ;
          last destruct H ;
          last by rewrite /tps (th_pnum''' _ _ H0).
        rewrite big_addi.

        rewrite /prec => /=.
        Check max_card (fun j : player4 => (j != i) && ((i < player4_num 2) == (j < player4_num 2))).
        Search _ "leq" "trans".
        rewrite !muln1.
        have th_card1 :
          #|[pred j : 'I_4 | (j != i) && ((i < player4_num 2) == (j < player4_num 2))]| = 1.
        Search _ (card _) "ltn".
        Search _ card pred.
        Check cardD1x _.
          by admit.
        have th_card2 :
          #|[pred j : 'I_4 | (j != i) && ((i < player4_num 2) != (j < player4_num 2))]| = 2.
          by admit.
        by rewrite th_card1 th_card2.
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




