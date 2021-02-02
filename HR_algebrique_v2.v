From mathcomp Require Import all_ssreflect ssrbool finmap.
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


  End Profiles.




  Section SNFGames.
    (* Jeux classiques en forme normale *)

    (* Situation de jeu *)
    Variables (N : finType)
              (A : N -> finType).
    (* Spécification des agents *)
    Variables (V : N ->  Type)
              (u : forall (i : N), profile A -> V i).

    Definition SNFutility := u.

  End SNFGames.





  Section IIGames.
    (* Jeux à information imparfaite/incomplète i.e. jeux sous incertitude
     *
     * Définis sur les états du monde omg \in Omega ->
     * tau i omg = theta i est le signal que i reçoit (i.e. son type)
     *)

    (* Situation de jeu *)
    Variables (N : finType)
              (Omega : finType)
              (Theta : N -> finType)
              (tau : forall (i : N), Omega -> Theta i)
              (A : forall (i : N), finType).
    (* Spécification des agents *)
    Variables (E : forall (i : N), eval_struct)
              (d : forall (i : N), Omega -> W (E i))
              (u : forall (i : N), profile A -> Omega -> U (E i)).

    (* Crée le 'profil de signaux' theta correspondant à un état du monde omega *)
    Definition mk_tprofile (omg : Omega) : fprofile Theta :=
      [ffun i => tau i omg].

    (* Utilité 'espérée' si i reçoit t *)
    Definition IIutility (i : N) (t : Theta i)  (bp : bprofile Theta A) : V (E i) :=
      \big[oplus (E i)/V0 (E i)]_(omg : Omega | tau i omg == t)
       otimes (d i omg) (u i (proj_profile bp (mk_tprofile omg)) omg).

  End IIGames.




  Section II2Games.
    (* Jeux à information imparfaite/incomplète i.e. jeux sous incertitude
     *
     * Définis sur les profils de signaux theta \in Theta ->
     * Les états du monde ne sont pas connus
     *)

    (* Situation de jeu *)
    Variables (N : finType)
              (Theta : N -> finType)
              (A : N -> finType).
    (* Spécification des agents *)
    Variables (E : N -> eval_struct)
              (d : forall i, profile Theta -> W (E i))
              (u : forall i, profile A -> profile Theta -> U (E i)).

    (* Utilité 'espérée' si i reçoit t *)
    Definition II2utility (i : N) (t : Theta i) (bp : bprofile Theta A) : V (E i) :=
      \big[oplus (E i)/V0 (E i)]_(theta : fprofile Theta | theta i == t)
       otimes (d i theta) (u i (proj_profile bp theta) theta).


    (* Un II2Game est un IIGame où les états du monde sont les profils de signaux. *)
    Lemma II2_2_II :
      forall i (t : Theta i) bp, II2utility t bp = IIutility (fun i (omg : [finType of fprofile Theta]) => omg i) d u t bp.
    Proof.
    move => i t bp.
    rewrite /IIutility /II2utility.
    apply eq_bigr => theta Htheta.
    rewrite /mk_tprofile.
    have th : [ffun i : N => theta i] = theta.
    apply /ffunP => j. by rewrite ffunE.
      by rewrite th.
    Qed.

  End II2Games.


  Section IIGames_lemma.
    (* Ici : lemme 'un IIGame est un II2Game où les états du monde correspondant à un même profil
     * de signaux sont 'regroupés'
     *
     * On ne peut pas le faire car il faut un peu plus de th. incertitude...
     * Grossièrement : 'addition' des 'probas' et 'marginalisation'.
     *)


    (* Situation de jeu *)
    Variables (N : finType)
              (Omega : finType)
              (Theta : N -> finType)
              (tau : forall (i : N), Omega -> Theta i)
              (A : forall (i : N), finType).
    (* Spécification des agents *)
    Variables (E : forall (i : N), eval_struct)
              (d : forall (i : N), Omega -> W (E i))
              (u : forall (i : N), profile A -> Omega -> U (E i)).



    (* Ici on est embêté car oplus est défini sur V et on voudrait l'avoir sur W *)
    Definition II2_d (i : N) (theta : fprofile Theta) : W (E i). (*
      \big[oplus (E i)/V0 (E i)]_(omg in Omega | [forall j : N, tau j omg == theta j])
       d i omg.
     *)
    Admitted.

    Definition II2_u (i : N) (pA : profile A) (pT : profile Theta) : U (E i).
    (* Ici il faut conditionner / marginaliser -> il faut en savoir plus (p.ex. savoir diviser),
       ça dépend de la th. de l'incertitude utilisée -- non modélisée *)
    Admitted.

    Check IIutility _ _ _ _ _.
    Check II2utility _ _ _ _.

    Lemma II_2_II2 :
      forall i (t : Theta i) bp,
      IIutility tau d u t bp = II2utility II2_d II2_u t bp.
    Admitted.

  End IIGames_lemma.




  Section HGGames.
    (* Jeux hyper-graphiques *)

    (* Situation de jeu *)
    Variables (N : finType)
              (E : {set {set N}})
              (A : forall (i : N), finType).

    (* Spécification des agents *)
    Variables (V : forall (i : N), Type)
              (V0 : forall (i : N), V i)
              (oplus : forall (i : N), Monoid.com_law (V0 i) )
              (u : forall e i, e \in E -> i \in e -> profile A -> V i).

    (* Version "totale" de l'utilité (on donne l'élément neutre si pas d'utilité définie) *)
    Definition u_total e i p :=
      match boolP (e \in E) with
      | AltTrue h1 =>
        match boolP (i \in e) with
        | AltTrue h2 => u h1 h2 p
        | AltFalse _ => V0 i
        end
      | AltFalse _ => V0 i
      end.

    (* Utilité globale *)
    Definition HGutility (i : N) (p : profile A) : V i :=
      \big[oplus i/V0 i]_(e | e \in E) u_total e i p.

  End HGGames.





  Section SNF_of_HG.
    (* Tout jeu hyper-graphique correspond à un jeu en forme normale - trivial *)

    (* Situation de jeu *)
    Variables (N : finType)
              (E : {set {set N}})
              (A : forall (i : N), finType).

    (* Spécification des agents *)
    Variables (V : forall (i : N), Type)
              (V0 : forall (i : N), V i)
              (oplus : forall (i : N), Monoid.com_law (V0 i) )
              (u : forall e i, e \in E -> i \in e -> profile A -> V i).

    Lemma SNF_of_HG :
      HGutility oplus u = SNFutility (HGutility oplus u).
    Proof. by auto. Qed.

  End SNF_of_HG.


  Section HG_of_SNF.
    (* Tout jeu classique correspond à un jeu hyper-graphique -- trivial *)

    (* Situation de jeu *)
    Variables (N : finType)
              (A : N -> finType).
    (* Spécification des agents *)
    Variables (V : N ->  Type)
              (u : forall (i : N), profile A -> V i).

    Definition HG_V0 : forall (i : N), V i. Admitted.
    Definition HG_oplus : forall (i : N), Monoid.com_law (HG_V0 i). Admitted.

    Lemma HG_of_SNF i pA :
      SNFutility u i pA = HGutility (E:=[set setT]) HG_oplus (fun e i He Hi => u i) i pA.
    Proof.
    rewrite /SNFutility /HGutility big_set1 /u_total.
    have th : [set: N] \in [set setT]. by rewrite set11.
    case (boolP
          (@in_mem (Finite.sort (set_of_finType N)) (@setTfor N (Phant (Finite.sort N)))
                   (@mem (Finite.sort (set_of_finType N)) (predPredType (Finite.sort (set_of_finType N)))
                         (@SetDef.pred_of_set (set_of_finType N) [set setT]))))
    => H ; last by move/negP in H.
    case (boolP
          (@in_mem (Finite.sort N) i (@mem (Finite.sort N) (predPredType (Finite.sort N))
                                           (@SetDef.pred_of_set N (@setTfor N (Phant (Finite.sort N)))))))
    => H2 ; last by move/negP in H2.
      by auto.
    Qed.
  End HG_of_SNF.


  Section HR.
    (* Tout jeu à information imparfaite/incomplète correspond à un jeu hyper-graphique *)

    (* Situation de jeu *)
    Variables (N : finType)
              (Omega : finType)
              (Theta : N -> finType)
              (tau : forall (i : N), Omega -> Theta i)
              (A : forall (i : N), finType).

    (* Spécification des agents *)
    Variables (E : forall (i : N), eval_struct)
              (d : forall (i : N), Omega -> W (E i))
              (u : forall (i : N), profile A -> Omega -> U (E i)).


    (* Ensemble de couples (joueur,signal) correspondant à un profil de signaux *)
    Definition e_theta (theta : fprofile Theta) := [set existT Theta i (theta i) | i in N].

    (* États du monde correspondant à un profil de signaux *)
    Definition omgs_of_theta (theta : fprofile Theta) : {set Omega} := [set omg : Omega | [forall i : N, (tau i omg) == (theta i)]].


    (* Sommets de l'hyper-graphe = couples (joueur,signal) *)
    Definition bar_N := [finType of {i : N & Theta i}].

    (* Opérateur pour le jeu hyper-graphique *)
    Definition bar_oplus := fun it : bar_N => oplus (E (projT1 it)).

    (* Actions pour le jeu hyper-graphique *)
    Definition bar_A := fun (it : bar_N) => A (projT1 it).

    (* Hyper-arêtes : une pour chaque profil de signaux *)
    Definition bar_E := [set e_theta theta | theta in fprofile Theta].

    (* Profil de signal correspondant à un ensemble e_theta \in bar_E *)
    Definition theta_of_e (e : {set {i : N & Theta i}}) : fprofile Theta. Admitted.

    (* Fonction d'utilité totale pour le jeu hyper-graphique *)
    Definition bar_u_total (e : {set bar_N}) (it : bar_N) bp :=
      let i := projT1 it in
      let t := projT2 it in
      let theta := theta_of_e e in
      match boolP (e \in bar_E) with
      | AltTrue he =>
        match boolP (it \in e) with

        | AltTrue hit => \big[oplus (E i)/V0 (E i)]_(omg in omgs_of_theta theta)
                          otimes (d i omg) (u i (proj_profile bp theta) omg)
        | _ => V0 (E i)
        end
      | _ => V0 (E i)
      end.

    (* TODO utiliser les preuves que e \in bar_E et i \in e ? *)
    Definition bar_u (e : {set bar_N}) (it : bar_N) (_ : e \in bar_E) (_ : it \in e) bp :=
      let i := projT1 it in
      let t := projT2 it in
      let theta := theta_of_e e in
      \big[oplus (E i)/V0 (E i)]_(omg in omgs_of_theta theta)
                          otimes (d i omg) (u i (proj_profile bp theta) omg).



    (* Morceaux de la preuve *)


    Lemma eq_oplus (i : N) (t : Theta i) :
      oplus (E i) = bar_oplus (existT _ i t).
    Proof. by auto. Qed.



    Lemma eq_pred_omg:
      forall i t, [set x | [pred omg | (tau i omg) == t] x] = [set x | (tau i x) == t].
    Proof. by compute. Qed.



    Lemma eq_pred_omg2_part i f :
       \big[oplus (E i)/V0 (E i)]_(theta in fprofile Theta) \big[oplus _/V0 _]_(omg in omgs_of_theta theta) f omg =
       \big[oplus _/V0 _]_(theta in fprofile Theta) \big[oplus _/V0 _]_(omg <- enum (omgs_of_theta theta)) f omg.
    Admitted.

    Lemma eq_pred_omg2_part2 i t :
      enum [set o | tau i o == t] = [seq i2 | i1 <- enum (fprofile Theta), i2 <- enum (omgs_of_theta i1)].
    Admitted.

    Lemma eq_pred_omg2 :
      forall i t f, \big[oplus (E i)/V0 (E i)]_(omg in [set o | (tau i o) == t]) f omg = \big[oplus _/V0 _]_(theta in fprofile Theta) \big[oplus _/V0 _]_(omg in omgs_of_theta theta) f omg.
    Proof.
    move => i t f.
      by rewrite eq_pred_omg2_part -!big_enum -big_allpairs_dep eq_pred_omg2_part2.
    Qed.



    Lemma theta_in_bar_E :
      forall theta,
      (@in_mem (Finite.sort (set_of_finType bar_N)) (e_theta theta)
           (@mem (Finite.sort (set_of_finType bar_N)) (predPredType (Finite.sort (set_of_finType bar_N)))
              (@SetDef.pred_of_set (set_of_finType bar_N) bar_E))).
    Proof.
    rewrite /bar_E => theta.
    apply/imsetP.
    exists theta => //.
    Qed.




    Lemma theta_of_e_K :
      cancel e_theta theta_of_e.
    Admitted.




    Lemma theta_ffun (theta : fprofile Theta) :
      theta = [ffun i0 => theta i0].
    Admitted.



    Lemma eq_tau_theta theta omg :
      omg \in omgs_of_theta theta -> [ ffun i0 : N => tau i0 omg] = theta.
    Proof.
    rewrite in_set ; move/forallP => Htheta.
    rewrite (theta_ffun theta) (eq_dffun (tau^~ omg)) => // i.
    apply/eqP ; rewrite eq_sym.
    exact : Htheta.
    Qed.

    Lemma e_theta_inj : {in fprofile Theta &, injective [eta e_theta]}.
    Proof.
    rewrite /e_theta => p1 p2 Hp1 Hp2.
    case (boolP (p1 == p2)); first by move/eqP.
    move/eqP => Hcontra.
    Admitted.





    Lemma HR :
      forall i t bp, IIutility tau d u t bp = HGutility bar_oplus bar_u (existT _ i t) bp.
    Proof.
    rewrite /IIutility /HGutility.
    move => i t bp.
    rewrite -eq_oplus => //=.
    rewrite -big_set eq_pred_omg eq_pred_omg2 big_imset ; last by apply e_theta_inj.
    apply eq_bigr => theta Htheta //=.
    rewrite /u_total.
    case (boolP (* e_theta theta \in bar_E *)
          (@in_mem (Finite.sort (set_of_finType bar_N)) (e_theta theta)
                   (@mem (Finite.sort (set_of_finType bar_N)) (predPredType (Finite.sort (set_of_finType bar_N)))
                         (@SetDef.pred_of_set (set_of_finType bar_N) bar_E)))); last by rewrite theta_in_bar_E.
    - move => Htheta_barE.
      case (boolP (* existT (fun i1 : N => Theta i1) i t \in e_theta theta *)
            (@in_mem (Finite.sort bar_N)
                     (@existT (Finite.sort N) (fun i0 : Finite.sort N => Finite.sort (Theta i0)) i t)
                     (@mem (Finite.sort bar_N) (predPredType (Finite.sort bar_N))
                           (@SetDef.pred_of_set bar_N (e_theta theta))))).
      + move => Hit.
        rewrite /bar_u theta_of_e_K => /=.
        apply eq_bigr => omg Homg.
        rewrite /mk_tprofile => //=.
          by rewrite (eq_tau_theta Homg).
      + move => Hcontra.
        * have th : existT _ i t \in e_theta theta.
          rewrite/e_theta => /=.
          have th2 : t = theta i. by admit. (* Pas sûr : ai-je un pb dans les defs ? *)
            by rewrite th2 mem_imset.
        * move/negP in Hcontra.
            by contradiction.
    Admitted.

  End HR.




  
  Section SNF_of_IIGame.
    
    (* Situation de jeu *)
    Variables (N : finType)
              (Omega : finType)
              (Theta : N -> finType)
              (tau : forall (i : N), Omega -> Theta i)
              (A : forall (i : N), finType).

    (* Spécification des agents *)
    Variables (E : forall (i : N), eval_struct)
              (d : forall (i : N), Omega -> W (E i))
              (u : forall (i : N), profile A -> Omega -> U (E i)).


    Definition SNF_N := [finType of {i : N & Theta i}].
    Definition SNF_A (it : SNF_N) := A (projT1 it).
    Definition SNF_u (it : SNF_N) (p : profile SNF_A) : V (E (projT1 it)) :=
      IIutility tau d u (projT2 it) p.

    Lemma SNF_of_IIGame :
      forall i t bp, IIutility tau d u t bp = SNFutility SNF_u (existT _ i t) bp.
    Proof.
        by rewrite /SNFutility /SNF_u.
    Qed.
    
    
    
  End SNF_of_IIGame.

End Games.
