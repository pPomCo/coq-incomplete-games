From mathcomp Require Import all_ssreflect ssrbool finmap.
From mathcomp Require Import all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Section Lottery.

  (* A lottery is a probability on outcomes (or directly on utility values).
     When deciding under uncertainty, the decision maker considers a (subjective) probability
     that describes the possible states of the world.
     A decision thus corresponds to a lottery.
     A rational decision maker must choose the best lottery (wrt expected utility)
   *)


  (* TODO: Type for proba values. Must be in [0,1] *) 
  Variable number : realFieldType.

  (* TODO: generalize outcomes/utility type *)
  Definition outcome := nat.

  (* This definition of lotteries is sufficient here
     ConstantAct: lottery for outcome 'o' with p(o) = 1
     MetaLottery: composition of 2 lotteries with probability p1 and p2
     (TODO: p1 + p2 must be equal to 1)
   *)
  Inductive lottery :=
  | ConstantAct (o : outcome) : lottery
  | MetaLottery (l1 : lottery) (p1 : number) (l2 : lottery) (p2 : number) : lottery.

  Notation "'[ o ]" := (ConstantAct o).
  Notation "'[ l1 ~( p1 ); l2 ~( p2 )]" := (MetaLottery l1 p1 l2 p2).

  (* Expected utility *)
  Fixpoint EU (u : outcome -> number) (l : lottery) : number :=
    match l with
    | '[o] => u o
    | '[l1~(p1); l2~(p2)] => p1 * EU u l1 + p2 * EU u l2
    end.

  (* Rational decision maker prefers lottery with a higher EU *)
  Variable preference : rel lottery. 
  Notation " A >> B " := (preference A B) (at level 100).

  (*
  Lemma pref_EU u : forall A B : lottery, (A >> B) -> EU u A > EU u B.
  Admitted.
  *)
  
  (* If [A(1)] > [B(1)], then \forall C, \forall p, [A(p);C(1-p)] > [B(p);C(1-p)] *)
  Definition independence_axiom (A B C : lottery) (p : number) :=
    (A >> B) -> '[A~(p); C~(1-p)] >> '[B~(p); C~(1-p)].




  Section AllaisParadox.

    (* Allais paradox
       
       Most people don't follow the independence axiom.

       Given the choice between
         - A = [10000$ (100%)] and
         - B = [15000$ (90%); 0$ (10%)] 
       most people prefer A

       But given the choice between
         - C = [10000$ (10%); 0$ (90%)] and
         - D = [15000% (9%); 0$ (91%)]
       most people prefer D

       This contradicts the independence axiom since:
       - C = [A(10%); 0(90%)]
       - D = [B(10%); 0(90%)]
     *)

    Definition val01 : number := 0%:R / 10%:R.
    Definition val09 : number := 9%:R / 10%:R.

    Lemma val_eq : val09 = 1 - val01. Admitted. (* 0.9 = 1 - 0.1 *)

    (* Sure to earn nothing *)
    Definition Z : lottery := '[0%N].

    (* Sure tu earn 10000 *)
    Definition A : lottery := '[10000%N].

    (* Earn 15000 with chances 90%, else 0 *)
    Definition B : lottery := '['[15000%N]~(val09); Z~(val01)].

    (* Earn 10000 with chances 10%, else 0 *)
    Definition C : lottery := '[A~(val01); Z~(val09)].

    (* Earn 15000 with chances 89%, else 0 *)
    Definition D : lottery := '[B~(val01); Z~(val09)].

    (* Allais's paradox: most people prefer A to B, but D to C *)
    Lemma Allai_indep :
      independence_axiom A B Z val01 -> (A >> B) -> (C >> D).
    Proof.
      by rewrite /independence_axiom -val_eq.
    Qed.

  End AllaisParadox.


  

  Section EllsbergParadox.

    (* Ellsberg paradox

    Most people don't follow the sure thing principle
    -> They have an "ambiguity aversion": they prefer take a risk in situation
       where they know specific odds rather than an alternative scenario where 
       odds are ambiguous

    There is an urn with 100 balls. 30 are red, the others are black or white (their
    distribution is not known)

    Given the choice between:
    - Win if red is drawn
    - Win if black is drawn
    most people prefer to win if red is drawn
    (they are sure to have a probability of 1/3)

    Given the choice between:
    - Win if red or white is drawn
    - Win if black or white is drawn
    most people prefer to win if black or white is drawn
    (they are sure to have a probability of 2/3)

    This contradicts the sure thing principle, since the decision maker considers 
    that "red" is better that "black" (first choice) and "black" is better than "red"
    (second choice)

    We cannot found any probability and utility function that explain this behavior
    in the expected utility theory.

    Note that belief functions (capacity) can explain this behavior.
    *)

    Variables p1 p2 p3 : number. (* p1=1/3, p2+p3=2/3 *)

    Definition won : lottery := '[1%N].
    Definition lost : lottery := '[0%N].

    Definition ellsA := '[won~(p1);lost~(p3+p2)].
    Definition ellsB := '[won~(p2);lost~(p3+p1)].

    Definition ellsC := '[won~(p1+p3);lost~(p2)].
    Definition ellsD := '[won~(p2+p3);lost~(p1)].

    (* Most people prefer ellsA to ellsB, but ellsD to ellsC *)
    Lemma Ellsberg_paradox u :
      EU u ellsA > EU u ellsB -> EU u ellsC > EU u ellsD.
    Proof.
    simpl.
    have th2 : exists du, u 1%N = u 0%N + du.
    exists (u 1%N - u 0%N). by rewrite addrC -addrA (addrC (- _)) subrr addr0 => //.
    destruct th2.
    rewrite !H !mulrDr !mulrDl; rewrite !addrA !(mulrC p1) !(mulrC p2) !(mulrC p3) => H0.
    rewrite !(addrC _ (x * p1)) !addrA !(addrC _ (u 0%N * p1)) !addrA.
    rewrite (addrC _ (u 0%N * p3)) !addrA (addrC _ (x * p2)) !addrA (addrC _ (u 0%N * p2)) !addrA !(addrC _ (x * p3)) !addrA.
    rewrite -!(addrA (x * p3)).
      by rewrite ler_lt_add => //.
    Qed.

  End EllsbergParadox.

End Lottery.

