From mathcomp Require Import all_ssreflect ssrbool finmap.
From mathcomp Require Import all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Section Lottery.

  Variable number : realFieldType.

  Inductive lottery outcome :=
  | ConstantAct (o : outcome) : lottery outcome
  | MetaLottery (l1 : lottery outcome) (p1 : number) (l2 : lottery outcome) (p2 : number) : lottery outcome.

  Notation "'[ o ]" := (ConstantAct o).
  Notation "'[ l1 ~( p1 ); l2 ~( p2 )]" := (MetaLottery l1 p1 l2 p2).


  Fixpoint EU Z (u : Z -> number) (l : lottery Z) : number :=
    match l with
    | '[o] => u o
    | '[l1~(p1); l2~(p2)] => p1 * EU u l1 + p2 * EU u l2
    end.
  

  Definition preference outcome : rel (lottery outcome). Admitted.
  Notation " A >> B " := (preference A B) (at level 100).

  (*
  Lemma pref_EU Z u : forall A B : lottery Z, (A >> B) -> EU u A > EU u B.
  Admitted.
  *)
  
  (* Si [A(1)] > [B(1)], alors \forall C, \forall p, [A(p);C(1-p)] > [B(p);C(1-p)] *)
  Definition independence_axiom outcome (A B C : lottery outcome) (p : number) :=
    (A >> B) -> '[A~(p); C~(1-p)] >> '[B~(p); C~(1-p)].


  

  Section AllaisParadox.

    Definition val01 : number. Admitted. (* = 0.1 *)
    Definition val09 : number. Admitted. (* = 0.9 *)

    Lemma val_eq : val09 = 1 - val01. Admitted. (* 0.9 = 1 - 0.1 *)

    (* Sure to earn nothing *)
    Definition Z : lottery nat := '[0%N].

    (* Sure tu earn 10000 *)
    Definition A : lottery nat := '[10000%N].

    (* Earn 15000 with chances 90%, else 0 *)
    Definition B : lottery nat := '['[15000%N]~(val09); Z~(val01)].

    (* Earn 10000 with chances 10%, else 0 *)
    Definition C : lottery nat := '[A~(val01); Z~(val09)].

    (* Earn 15000 with chances 89%, else 0 *)
    Definition D : lottery nat := '[B~(val01); Z~(val09)].

    (* Allais's paradox: most people prefer A to B, but D to C *)
    Lemma Allai_indep :
      independence_axiom A B Z val01 -> (A >> B) -> (C >> D).
    Proof.
      by rewrite /independence_axiom -val_eq.
    Qed.

  End AllaisParadox.


  

  Section EllsbergParadox.

    Variables p1 p2 p3 : number.

    Definition won : lottery nat := '[1%N].
    Definition lost : lottery nat := '[0%N].

    Definition ellsA := '[won~(p1);lost~(p3+p2)].
    Definition ellsB := '[won~(p2);lost~(p3+p1)].

    Definition ellsC := '[won~(p1+p3);lost~(p2)].
    Definition ellsD := '[won~(p2+p3);lost~(p1)].

    (* Most people prefer ellsA to ellsB, but ellsD to ellsC *)
    Lemma Ellsberg_paradox u :
      EU u ellsA > EU u ellsB -> EU u ellsC > EU u ellsD.
    Proof.
    simpl.
    have th2 : exists du, u 1%N = u 0%N + du. by admit.
    destruct th2.
    rewrite !H !mulrDr !mulrDl; rewrite !addrA !(mulrC p1) !(mulrC p2) !(mulrC p3) => H0.
    rewrite !(addrC _ (x * p1)) !addrA !(addrC _ (u 0%N * p1)) !addrA.
    rewrite (addrC _ (u 0%N * p3)) !addrA (addrC _ (x * p2)) !addrA (addrC _ (u 0%N * p2)) !addrA !(addrC _ (x * p3)) !addrA.
    rewrite -!(addrA (x * p3)).
      by rewrite ler_lt_add => //.
    Admitted.

  End EllsbergParadox.

End Lottery.

