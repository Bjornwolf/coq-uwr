(* Filip Chudy *)
Require Export Equiv.
Require Export Hoare2.

(** **** Problem 1 (10 p.) *)
(** Solve the following exercises: no_whiles (Imp), no_whiles_terminating (Imp).
*)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ;; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

Inductive no_whilesR: com -> Prop :=
  | NW_Ass : forall id exp, no_whilesR (id ::= exp)
  | NW_Seq : forall n m, no_whilesR n -> 
                         no_whilesR m -> 
                         no_whilesR (n ;; m)
  | NW_Skip : no_whilesR SKIP
  | NW_IfB : forall c1 c2 b, no_whilesR c1 -> 
                             no_whilesR c2 -> 
                             no_whilesR (IFB b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros c. split.
  Case "function -> relation".
    intros Hfun. induction c; inversion Hfun.
    SCase "SKIP".
      apply NW_Skip. 
    SCase "X ::= a".
      apply NW_Ass.
    SCase "c1;; c2".
      apply andb_true_iff in H0; inversion H0;
      apply IHc1 in H; apply IHc2 in H1.
      apply NW_Seq; assumption.
    SCase "IFB b THEN c1 ELSE c2 FI".
      apply andb_true_iff in H0; inversion H0;
      apply IHc1 in H; apply IHc2 in H1.
      apply NW_IfB; assumption.
  Case "relation -> function".
    intros Hrel; induction c; simpl; try reflexivity; inversion Hrel.
    SCase "c1;; c2".
      apply IHc1 in H1; apply IHc2 in H2.
      rewrite H1, H2. reflexivity.
    SCase "IFB b THEN c1 ELSE c2 END".
      apply IHc1 in H1. apply IHc2 in H3.
      rewrite H1, H3. reflexivity.
Qed.

Theorem no_whiles_terminating : forall c st,
no_whilesR c -> exists st', c / st || st'.
Proof.
  intros c st Hno_whilesR. generalize dependent st.
  induction c; intros st; inversion Hno_whilesR.
  Case "SKIP".
    exists st. apply E_Skip.
  Case "X ::= a".
    exists (update st i (aeval st a)). apply E_Ass; reflexivity.
  Case "c1;; c2".
    apply IHc1 with st in H1; inversion H1. 
    apply IHc2 with x in H2; inversion H2.
    exists x0. apply E_Seq with x; assumption.
  Case "IFB b THEN c1 ELSE c2 FI".
    apply IHc1 with st in H1; inversion H1.
    apply IHc2 with st in H3; inversion H3.
    remember (beval st b) as evalb. destruct evalb.
    SCase "b = true".
      exists x. apply E_IfTrue; try symmetry; assumption.
    SCase "b = false".
      exists x0. apply E_IfFalse; try symmetry; assumption.
Qed.

(** **** Problem 2 (15 p.) *)
(** Solve the following exercises: break_imp (Imp), 
                                   while_break_true (Imp), 
                                   ceval_deterministic (Imp).
*)

Module BreakImp.

Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "BREAK" 
  | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive status : Type :=
  | SContinue : status
  | SBreak : status.

Reserved Notation "c1 '/' st '||' s '/' st'"
                  (at level 40, st, s at level 39).

Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || SContinue / st
  | E_Break : forall st,
      BREAK / st || SBreak / st
  | E_Ass : forall st id num,
      (id ::= num) / st || SContinue / (update st id (aeval st num))
  | E_SeqC : forall c1 c2 st st' st'' sig, c1 / st || SContinue / st' -> 
              c2 / st' || sig / st'' -> (c1; c2) / st || sig / st''
  | E_SeqB : forall c1 c2 st st', c1 / st || SBreak / st' -> 
              (c1; c2) / st || SBreak / st'
  | E_IfTrue : forall st st' sig c1 c2 b,
                 beval st b = true -> c1 / st || sig / st' ->
                 (IFB b THEN c1 ELSE c2 FI) / st || sig / st'
  | E_IfFalse : forall st st' sig c1 c2 b,
                 beval st b = false -> c2 / st || sig / st' ->
                 (IFB b THEN c1 ELSE c2 FI) / st || sig / st'
  | E_WhileEnd : forall st c b,
                  beval st b = false -> 
                  (WHILE b DO c END) / st || SContinue / st
  | E_WhileLoopC : forall st st' st'' c b,
                  beval st b = true -> c / st || SContinue / st' ->
                  (WHILE b DO c END) / st' || SContinue / st'' ->
                  (WHILE b DO c END) / st || SContinue / st''
  | E_WhileLoopB : forall st st' c b,
                  beval st b = true -> c / st || SBreak / st' ->
                  (WHILE b DO c END) / st || SContinue / st'

  where "c1 '/' st '||' s '/' st'" := (ceval c1 st s st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Break" | Case_aux c "E_Ass"
  | Case_aux c "E_SeqC" | Case_aux c "E_SeqB"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd"
  | Case_aux c "E_WhileLoopC"  | Case_aux c "E_WhileLoopB"].

Theorem break_ignore : forall c st st' s,
     (BREAK; c) / st || s / st' ->
     st = st'.
Proof.
  intros. inversion H. inversion H2. inversion H5. reflexivity.
Qed.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st || s / st' ->
  s = SContinue.
Proof.
  intros; inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st || SBreak / st' ->
  (WHILE b DO c END) / st || SContinue / st'.
Proof.
  intros b c st st' Hb Hcb. inversion Hcb;
    apply E_WhileLoopB; subst; assumption.
Qed.

Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st || SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' || SBreak / st'.
Proof.
  intros b c st st' Hwhile Hb. remember (WHILE b DO c END) as prog.
  induction Hwhile; inversion Heqprog; subst.
  Case "E_WhileEnd".
    rewrite Hb in H; inversion H.
  Case "E_WhileLoopC".
    apply IHHwhile2 in Heqprog; assumption.
  Case "E_WhileLoopB".
    exists st. assumption. 
Qed.

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st || s1 / st1  ->
     c / st || s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros c st st1 st2 s1 s2 Hc1. 
  generalize dependent s2; generalize dependent st2.
  induction Hc1; intros st2 s2 Hc2.
  Case "E_Skip".
    inversion Hc2; subst; split; try reflexivity.
  Case "E_Break".
    inversion Hc2; subst; split; try reflexivity.
  Case "E_Ass".
    inversion Hc2; subst; split; try reflexivity.
  Case "E_SeqC".
    inversion Hc2; subst.
    SCase "E_SeqC".
      apply IHHc1_1 in H1. inversion H1; subst.
      apply IHHc1_2 in H5. assumption.
    SCase "E_SeqB".
      apply IHHc1_1 in H4; inversion H4. inversion H0.
  Case "E_SeqB".
    inversion Hc2; subst.
    SCase "E_SeqC".
      apply IHHc1 in H1; inversion H1. inversion H0.
    SCase "E_SeqB".
      apply IHHc1 in H4. assumption.
  Case "E_IfTrue".
    inversion Hc2; subst.
    SCase "E_IfTrue".
      apply IHHc1 in H7. assumption.
    SCase "E_IfFalse".
      rewrite H6 in H. inversion H.
  Case "E_IfFalse".
    inversion Hc2; subst.
    SCase "E_IfTrue".
      rewrite H6 in H. inversion H.
    SCase "E_IfFalse".
      apply IHHc1 in H7. assumption.
  Case "E_WhileEnd".
    inversion Hc2; subst.
    SCase "E_WhileEnd".
      split; reflexivity.
    SCase "E_WhileLoopC".
      rewrite H2 in H. inversion H.
    SCase "E_WhileLoopB".
      rewrite H2 in H. inversion H.
  Case "E_WhileLoopC".
    inversion Hc2; subst.
    SCase "E_WhileEnd".
      rewrite H5 in H. inversion H.
    SCase "E_WhileLoopC".
      apply IHHc1_1 in H3; inversion H3; subst.
      apply IHHc1_2 in H7. assumption.
    SCase "E_WhileLoopB".
      apply IHHc1_1 in H6; inversion H6. inversion H1.
  Case "E_WhileLoopB".
    inversion Hc2; subst.
    SCase "E_WhileEnd".
      rewrite H5 in H. inversion H.
    SCase "E_WhileLoopC".
      apply IHHc1 in H3; inversion H3. inversion H1.
    SCase "E_WhileLoopB".
      apply IHHc1 in H6; inversion H6. split; [assumption | reflexivity].       
Qed.

End BreakImp.

(** **** Problem 3 (20 p.) *)
(** Solve the following exercises: himp_ceval (Equiv), 
                                   havoc_swap (Equiv), 
                                   havoc_copy (Equiv), 
                                   p1_p2_equiv (Equiv), 
                                   p_3_p4_equiv (Equiv), 
                                   p5_p6_equiv (Equiv).  
*)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

(** **** Exercise: 2 stars (himp_ceval) *)
(** Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_Havoc : forall n X st, (HAVOC X) / st || update st X n


  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
  | Case_aux c "E_Havoc"
  ].

Example havoc_example1 : (HAVOC X) / empty_state || update empty_state X 0.
Proof.
  apply E_Havoc.
Qed.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state || update empty_state Z 42.
Proof.
  apply E_Seq with empty_state. apply E_Skip. apply E_Havoc.
Qed.
(** [] *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st || st' <-> c2 / st || st'.

(** **** Exercise: 3 stars (havoc_swap) *)
(** Are the following two programs equivalent? *)

Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  left. (* cequiv pXY pYX *)
  unfold cequiv, pXY, pYX. intros st st'.
  assert(Lem: forall A B n1 n2, B <> A ->
         update (update st B n2) A n1 = update (update st A n1) B n2).
  Case "proof of Lem".
    intros A B n1 n2 Hneq. apply functional_extensionality; intros x. 
    apply update_permute. assumption.
  split; intros p; inversion p; inversion H1; inversion H4; subst.
  Case "pXY -> pYX".
    apply E_Seq with (update st Y n0).
    SCase "HAVOC Y". 
      apply E_Havoc.
    SCase "HAVOC X".
      rewrite Lem; [apply E_Havoc | intros Hneq; inversion Hneq].
  Case "pYX -> pXY".
    apply E_Seq with (update st X n0).
    SCase "HAVOC X".
      apply E_Havoc.
    SCase "HAVOC Y".
      rewrite Lem; [apply E_Havoc | intros Hneq; inversion Hneq].
Qed.

(** **** Exercise: 4 stars, optional (havoc_copy) *)
(** Are the following two programs equivalent? *)

Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. 
  right. (* ~cequiv ptwice pcopy *)
  unfold cequiv, ptwice, pcopy. intros cont.
  assert(Htwice: (HAVOC X;; HAVOC Y) / empty_state
                 || update (update empty_state X 42) Y 1).
  Case "proof of Htwice".                
    apply E_Seq with (update empty_state X 42); apply E_Havoc.
  assert (Hcopy: (HAVOC X;; Y ::= AId X)  / empty_state 
                 || update (update empty_state X 42) Y 1).
  Case "proof of Hcopy".
    apply cont in Htwice. assumption.
  inversion Hcopy; inversion H1; inversion H4; subst.
  simpl in H12. rewrite update_eq in H12.
  remember (beq_nat n 42) as n42; destruct n42.
  Case "n = 42".
    apply beq_nat_eq in Heqn42. rewrite Heqn42 in H12.
    assert(F: update (update empty_state X 42) Y 42 Y
            = update (update empty_state X 42) Y  1 Y).
    SCase "proof of false".
      rewrite H12; reflexivity.
    rewrite update_eq in F; rewrite update_eq in F; inversion F.
  Case "n <> 42".
    assert(F: update (update empty_state X  n) Y n X 
            = update (update empty_state X 42) Y 1 X).
    SCase "proof of false".
      rewrite H12; reflexivity.
    rewrite update_neq in F; [rewrite update_eq in F | intros HF; inversion HF];
    rewrite update_neq in F; [rewrite update_eq in F | intros HF; inversion HF].
    rewrite F in Heqn42; simpl in Heqn42. inversion Heqn42.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (p1_p2_equiv) *)
(** Prove that p1 and p2 are equivalent. In this and the following
    exercises, try to understand why the [cequiv] definition has the
    behavior it has on these examples. *)

Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.


(** Intuitively, the programs have the same termination
    behavior: either they loop forever, or they terminate in the
    same state they started in.  We can capture the termination
    behavior of p1 and p2 individually with these lemmas: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ p1 / st || st'.
Proof.
  intros st st' H cont; generalize dependent H;
  remember p1 as p1. induction cont; try inversion Heqp1; subst.
  Case "E_WhileEnd".
    simpl in H. apply negb_false_iff in H. apply beq_nat_true in H.
    intros NotH. contradiction.
  Case "E_WhileLoop".
    simpl in H. apply negb_true_iff in H. apply beq_nat_false in H.
    apply IHcont2 in Heqp1. 
    SCase "subgoal using IHcont2". 
      inversion Heqp1.
    SCase "second condition of IHcont2".
      inversion cont1; inversion H2; inversion H5; subst. simpl in H5. simpl.
      rewrite update_eq. rewrite update_neq; [omega | intros HF; inversion HF].
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ p2 / st || st'.
Proof.
  intros st st' H cont; generalize dependent H;
  remember p2 as p2. induction cont; try inversion Heqp2; subst.
  Case "E_WhileEnd".
    simpl in H. apply negb_false_iff in H. apply beq_nat_true in H.
    intros NotH. contradiction.
  Case "E_WhileLoop".
    simpl in H. apply negb_true_iff in H. apply beq_nat_false in H.
    apply IHcont2 in Heqp2. 
    SCase "subgoal using IHcont2". 
      inversion Heqp2.
    SCase "second condition of IHcont2".
      inversion cont1; subst. assumption.
Qed.

(** You should use these lemmas to prove that p1 and p2 are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
  unfold cequiv, p1, p2. intros st st'. split.
  Case "p1 -> p2".
    intros Hp1. inversion Hp1; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. assumption.
    SCase "E_WhileLoop".
      apply E_WhileLoop with st'0; try assumption;
        simpl in H1; apply negb_true_iff in H1; apply beq_nat_false in H1;
        apply p1_may_diverge with st st' in H1; contradiction.
  Case "p2 -> p1".
    intros Hp2. inversion Hp2; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. assumption.
    SCase "E_WhileLoop".
      apply E_WhileLoop with st'0; try assumption;
        simpl in H1; apply negb_true_iff in H1; apply beq_nat_false in H1;
        apply p2_may_diverge with st st' in H1; contradiction.
Qed.

(** **** Exercise: 4 stars, advanced (p3_p4_inquiv) *)

(** Prove that the following programs are _not_ equivalent. *)

Definition p3 : com :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END.

Definition p4 : com :=
  X ::= (ANum 0);;
  Z ::= (ANum 1).


Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.
  unfold cequiv, p3, p4. intros cont.
  assert(Hp3: p3 / (update empty_state X 1) 
              || update (update (update (update empty_state X 1) Z 1) X 0) Z 2).
  Case "proof of Hp3".
    apply E_Seq with (update (update empty_state X 1) Z 1).
    SCase "assignment".
      apply E_Ass; reflexivity.
    SCase "while".
      apply E_WhileLoop with 
            (update (update (update (update empty_state X 1) Z 1) X 0) Z 2).
      SSCase "guard".
        reflexivity.
      SSCase "body".
        apply E_Seq with (update (update (update empty_state X 1) Z 1) X 0);
        apply E_Havoc.
      SSCase "remaining while".
        apply E_WhileEnd; reflexivity.
  apply cont in Hp3. inversion Hp3; subst. inversion H4; subst. simpl in H5.
  assert(Ext: forall (st st' : state) U, st = st' -> st U = st' U).
  Case "proof of Ext".
    intros st st'0 U Heq; rewrite Heq. reflexivity.
  apply Ext with (U:=Z) in H5. repeat rewrite update_eq in H5. inversion H5.
Qed.

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv) *)

Definition p5 : com :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END.

Definition p6 : com :=
  X ::= ANum 1.

Lemma p5_stops_with_x_1 : forall st st', 
  p5 / st || st' -> st' = update st X 1.
Proof.
  intros st st' Hp5stops; remember p5 as p5. 
  ceval_cases (induction Hp5stops) Case; try inversion Heqp5; subst; simpl in H.
  Case "E_WhileEnd".
    apply negb_false_iff in H; apply beq_nat_true in H.
    apply functional_extensionality; intros x.
    remember (eq_id_dec X x) as sameXx; destruct sameXx.
    SCase "X = x".
      rewrite <- e, update_eq. assumption. 
    SCase "X <> x".
      rewrite update_neq; [reflexivity | assumption].
  Case "E_WhileLoop".
    apply negb_true_iff in H; apply beq_nat_false in H.
    inversion Hp5stops1; subst.
    assert(update st X 1 = update (update st X n) X 1).
    SCase "proof of assertion".
      apply functional_extensionality; intros x.
      rewrite update_shadow; reflexivity.
    apply IHHp5stops2 in Heqp5; rewrite H0. assumption.
Qed.


Theorem p5_p6_equiv : cequiv p5 p6.
Proof.
  unfold cequiv, p5, p6. split.
  Case "p5 -> p6".
    intros Hp5. apply p5_stops_with_x_1 in Hp5; subst. apply E_Ass; reflexivity.
  Case "p6 -> p5".
    intros Hp6. inversion Hp6; subst; simpl.
    remember (beq_nat (st X) 1) as X1; destruct X1.
    SCase "st X = 1".
      apply beq_nat_eq in HeqX1.
      assert (Hshadow: st = update st X 1).
      SSCase "proof of Hshadow".
        apply functional_extensionality. intros x. symmetry; apply update_same.
        assumption.
      rewrite <- Hshadow. apply E_WhileEnd. simpl. rewrite HeqX1. reflexivity.
    SCase "st X <> 1".
      apply E_WhileLoop with (update st X 1).
      SSCase "guard".
        simpl; apply negb_true_iff; symmetry; assumption.
      SSCase "body".
        apply E_Havoc.
      SSCase "remaining iterations".
        apply E_WhileEnd; reflexivity.
Qed.
(** [] *)

End Himp.

(** **** Problem 4 (10 p.) *)
(** Solve the following exercises: hoare_repeat (Hoare).
*)

Module RepeatExercise.

(** **** Exercise: 4 stars, advanced (hoare_repeat) *)
(** In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [UNTIL] a [END]. You will write the
    evaluation rule for [repeat] and add a new Hoare rule to
    the language for programs involving it. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "CRepeat" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall st st' b c,
      ceval st c st' ->
      beval st' b = true ->
      ceval st (REPEAT c UNTIL b END) st'
  | E_RepeatLoop : forall st st' st'' b c,
      ceval st c st' ->
      beval st' b = false ->
      ceval st' (REPEAT c UNTIL b END) st'' ->
      ceval st (REPEAT c UNTIL b END) st''
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass"
  | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
  | Case_aux c "E_RepeatEnd" | Case_aux c "E_RepeatLoop"
].

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '||' st'" := (ceval st c1 st') 
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) 
                        : Prop :=
  forall st st', (c / st || st') -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** To make sure you've got the evaluation rules for [REPEAT] right,
    prove that [ex1_repeat evaluates correctly. *)

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state ||
               update (update empty_state X 1) Y 1.
Proof.
  unfold ex1_repeat. apply E_RepeatEnd.
    Case "loop body".
      apply E_Seq with (st':= update empty_state X 1).
        apply E_Ass; reflexivity.
        apply E_Ass; reflexivity.
    Case "loop condition".
      simpl; reflexivity.
Qed.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(**

REPEAT c UNTIL b END = c;; WHILE ~b DO c END


        ----------------------------------- (hoare_c)
                    {{P}} c {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}


               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

 Let b = ~b' and P = P' in hoare_while.

               {{P' /\ ~b'}} c {{P'}}
        -----------------------------------  (hoare_while)
        {{P'}} WHILE ~b' DO c END {{P' /\ b'}}

When applied to hoare_seq, we have (with R = P' /\ b', P' = Q).

                                     {{Q /\ ~b'}} c {{Q}}
                             --------------------------------------
           {{ P }} c {{ Q }}, {{Q}} WHILE ~b' DO c END {{Q /\ b'}}
          ----------------------------------------------------------
                  {{ P }} c;;WHILE ~b' DO c END {{ Q /\ b' }}

which simplifies to

           {{ P }} c {{ Q }}, {{Q /\ ~b'}} c {{Q}}
          -----------------------------------------
           {{ P }} REPEAT c UNTIL b' {{ Q /\ b' }}

What's more,

       {{ P }} c {{ Q }}, (Q /\ ~b') ->> P
    -----------------------------------------
     {{ P }} c {{ Q }}, {{Q /\ ~b'}} c {{Q}}

So the form of the theorem will be

           {{ P }} c {{ Q }}, (Q /\ ~b') ->> P
          -----------------------------------------
           {{ P }} REPEAT c UNTIL b' {{ Q /\ b' }}

We'll use b instead of b'.
*)

Lemma hoare_repeat : forall P Q b c,
  {{P}} c {{Q}} ->
  (fun st => Q st /\ ~(bassn b st)) ->> P ->
  {{P}} (REPEAT c UNTIL b END) {{fun st => Q st /\ bassn b st}}.
Proof.
  intros P Q b c Hc Hbc st st' Hcstates Hp.
  remember (REPEAT c UNTIL b END) as rcom.
  ceval_cases (induction Hcstates) Case; 
  try inversion Heqrcom; subst. 
  Case "E_RepeatEnd".
    split.
    SCase "Q st'".
      apply Hc in Hcstates; apply Hcstates in Hp. assumption.
    SCase "bassn b st'".
      apply bexp_eval_true in H. assumption.
  Case "E_RepeatLoop".
    apply IHHcstates2; [reflexivity | apply Hbc].
    split.
    SCase "Q st'".
      apply Hc in Hcstates1; apply Hcstates1 in Hp. assumption.
    SCase "~ bassn b st'".
      apply bexp_eval_false in H. assumption.
Qed.

(* COPYPASTE TO UPDATE HOARE RULES FOR REPEAT...UNTIL *)

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_asgn : forall Q X a,
{{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption. Qed.

(* COPYPASTE ENDS *)

Theorem hoare_repeat_works:
  {{ fun st => st X > 0 }}
  REPEAT
    Y ::= AId X;;
    X ::= AMinus (AId X) (ANum 1)
  UNTIL BEq (AId X) (ANum 0) END
  {{ fun st => st X = 0 /\ st Y > 0 }}.
Proof.
  remember (fun st => st Y > 0) as Q.
  remember (BEq (AId X) (ANum 0)) as b.
  remember (Y ::= AId X;;
            X ::= AMinus (AId X) (ANum 1)) as c.
  remember (REPEAT c UNTIL b END) as prog.
  assert((fun st => Q st /\ bassn b st) ->> (fun st => st X = 0 /\ st Y > 0)).
  Case "proof of assertion".
    intros st. rewrite HeqQ, Heqb; unfold bassn; simpl.
    intros Hs; inversion Hs. split; 
    [apply beq_nat_true; assumption | assumption].
  apply hoare_consequence_post with
        (P:=(fun st => st X > 0))
        (Q:=(fun st : state => st X = 0 /\ st Y > 0))
        (Q':=(fun st : state => Q st /\ bassn b st))
        (c:=prog).
  rewrite Heqprog, Heqc. apply hoare_repeat.
  Case "loop body".
    apply hoare_seq with Q;
    eapply hoare_consequence_pre;
    [ apply hoare_asgn | rewrite HeqQ; intros st HQ; unfold assn_sub; simpl
    | apply hoare_asgn | rewrite HeqQ; intros st HQ; unfold assn_sub; simpl];
    [ rewrite update_neq; [assumption | intros HF; inversion HF]
    | rewrite update_eq; assumption].
  Case "assertion convertion".
    rewrite HeqQ,Heqb; unfold bassn; simpl; intros st Qb. inversion Qb.
    apply not_true_is_false in H1.
    destruct (st X); [inversion H1 | omega].
  Case "another assertion convertion".
    rewrite HeqQ,Heqb; unfold bassn; simpl; intros st Qb. inversion Qb.
    apply beq_nat_true in H1. split; assumption.
Qed.

End RepeatExercise.

(** **** Problem 5 (5 p.) *)
(** Solve the following exercises: add_slowly_decoration (Hoare2).
*)

(** **** Exercise: 3 stars, optional (add_slowly_decoration) *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)
(*
(1) {{ X = n /\ Z = m }} ->>
(2) {{ Z + X = m + n }}
  WHILE X <> 0 DO
(3) {{ Z + X = m + n /\ X <> 0 }} ->>
(4) {{ (Z + 1) + (X - 1) = m + n }}
     Z ::= Z + 1;
(5) {{ Z + (X - 1) = m + n }}
     X ::= X - 1
(6) {{ Z + X = m + n }}
  END
(7) {{ Z + X = m + n /\ ~(X <> 0) }} ->>
(8) {{ Z = m + n }}
*)

Theorem add_slowly_correct : forall n m,
    {{ fun st => st X = n /\ st Z = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= APlus (AId Z) (ANum 1);;
    X ::= AMinus (AId X) (ANum 1)
  END
    {{ fun st => st Z = m + n }}.
Proof.
  intros n m.
  eapply hoare_consequence_post.
  Case "(1)..(7)".
    apply hoare_consequence_pre with (fun st => (st X) + (st Z) = m + n).
    SCase "(2)..(7)".
      apply hoare_while. eapply hoare_consequence_pre.
      SSCase "(4)..(6)".
        eapply hoare_seq; apply hoare_asgn.
      SSCase "(3) ->> (4)".
        intros st [Hst Hb]. unfold assn_sub. simpl. rewrite update_eq.
        rewrite <- Hst. rewrite update_neq. rewrite update_neq.
        rewrite update_eq, plus_assoc. 
        unfold bassn in Hb; simpl in Hb; apply negb_true_iff in Hb.
        destruct (st X).
        SSSCase "st X = 0". 
          inversion Hb.
        SSSCase "st X <> 0".
          simpl. omega.
        intros HF; inversion HF.
        intros HF; inversion HF.
    SCase "(1) ->> (2)".
      intros st [H0 H1]. rewrite H0, H1. omega.
  Case "(7) ->> (8)".
    intros st [Hst Hb]. rewrite <- Hst. unfold bassn in Hb; simpl in Hb. 
    apply not_true_is_false in Hb. apply negb_false_iff in Hb. 
    apply beq_nat_true in Hb. rewrite Hb; reflexivity.
Qed.


(** **** Problem 6 (5 p.) *)
(** Solve the following exercises: parity_formal (Hoare2).
*)

(** **** Exercise: 3 stars, optional (parity_formal) *)
(** Translate this proof to Coq. Refer to the reduce-to-zero example
    for ideas. You may find the following two lemmas useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    apply ex_falso_quodlibet. apply H. omega.
Qed.

(*
  (1)    {{ X = m }} ->>                              (a - OK)
  (2)    {{ parity X = parity m }}
    WHILE 2 <= X DO
  (3)      {{ parity X = parity m /\ 2 <= X }}  ->>    (c - OK)
  (4)      {{ parity (X-2) = parity m }}
  (5)    X ::= X - 2
  (6)      {{ parity X = parity m }}
    END
  (7)    {{ parity X = parity m /\ X < 2 }}  ->>       (b - OK)
  (8)    {{ X = parity m }}
*)

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros m.
  eapply hoare_consequence_post.
  Case "(1)..(7)".
    apply hoare_consequence_pre with (fun st => parity (st X) = parity m).
    SCase "(2)..(7)".
      apply hoare_while. eapply hoare_consequence_pre.
      SSCase "(4)..(6)".
        apply hoare_asgn.
      SSCase "(3) ->> (4)".
        intros st [Hst Hb]. unfold assn_sub. simpl. rewrite update_eq.
        rewrite <- Hst. apply parity_ge_2. unfold bassn in Hb. simpl in Hb.
        destruct (st X) as [|x']; try inversion Hb. 
        destruct x' as [|x'']; try inversion Hb. omega.
    SCase "(1) ->> (2)".
      intros st H. rewrite H. reflexivity.
  Case "(7) ->> (8)".
    intros st [Hst Hb]. rewrite <- Hst. unfold bassn in Hb; simpl in Hb. 
    apply not_true_is_false in Hb.
    destruct (st X) as [|x']; try reflexivity. 
    destruct x' as [|x'']; try reflexivity. inversion Hb.
Qed.

(** **** Problem 7 (5 p.) *)
(** Solve the following exercises: factorial_dec (Hoare2).
*)

(** **** Exercise: 4 stars, advanced (factorial_dec)  *)
(** Remember the factorial function we worked with before: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Following the pattern of [subtract_slowly_dec], write a decorated
    program that implements the factorial function and prove it
    correct. *)

(*
  (1) {{ X = n }}
      ->>
  (2) {{ 1 * (real_fact X) = real_fact n }}
  Y ::= 1;;
  (3) {{ Y * (real_fact X) = real_fact n }}
  WHILE X <> 0 DO
  (4) {{ Y * (real_fact X) = real_fact n /\ X >= 0 }}
      ->>
  (5) {{ (Y * X) * (real_fact (X - 1)) = real_fact n }}
    Y ::= Y * X;;
  (6) {{ Y * (real_fact (X - 1)) = real_fact n }}
    X ::= X - 1
  (7) {{ Y * (real_fact X) = real_fact n }}
  END
  (8) {{ Y * (real_fact X) = real_fact n /\ ~(X >= 0) }}
      ->>
  (9) {{ Y = real_fact n }}
*)

Theorem factorial_dec: forall n,
  {{ fun st => st X = n }}
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId X);;
    X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = real_fact n }}.
Proof.
  intros n.
  eapply hoare_consequence_post.
  Case "(1)..(8)".
   eapply hoare_consequence_pre. 
   SCase "(2)..(8)".
     apply hoare_seq with
           (fun st => st Y * real_fact (st X) = real_fact n).
     SSCase "(3)..(8)".
       apply hoare_while. eapply hoare_consequence_pre.
       SSSCase "(5)..(7)".
         eapply hoare_seq.
         SSSSCase "(6)..(7)".
           apply hoare_asgn.
         SSSSCase "(5)..(6)".
           apply hoare_asgn.
       SSSCase "(4) ->> (5)".
         intros st [Hst Hb]. unfold assn_sub. simpl.
         rewrite update_eq. rewrite update_neq; 
         try intros HNeq; try inversion HNeq.
         rewrite update_eq. rewrite update_neq; 
         try intros HNeq; try inversion HNeq. 
         unfold bassn in Hb. simpl in Hb.
         destruct (st X).
         SSSSCase "st X = 0".
           simpl in Hb. inversion Hb.
         SSSSCase "st X > 0". 
           unfold real_fact in Hst. fold real_fact in Hst. rewrite <- Hst.
           assert(S n0 - 1 = n0). omega.
           rewrite H. rewrite mult_assoc. omega.
     SSCase "(2)..(3)".
       apply hoare_asgn.
   SCase "(1) ->> (2)".
     intros st Hst. unfold assn_sub. rewrite update_eq.
     rewrite update_neq; try intros HNeq; try inversion HNeq.
     simpl. rewrite Hst. omega.
  Case "(8) ->> (9)".
    intros st [Hst Hb]. unfold bassn in Hb. apply not_true_is_false in Hb.
    simpl in Hb. destruct (st X) as [|x']. 
    SCase "st X = 0".
      simpl in Hst. rewrite <- Hst. omega.
    SCase "st X > 0".
      simpl in Hb. inversion Hb.
Qed.
