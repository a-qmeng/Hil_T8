Require Export Classical.

Axiom constructive_indefinition_descripption :
  forall {A : Type} {P: A -> Prop}, 
  (exists x, P x) -> { x : A | P x }.

Definition Cid {A : Type} {P : A -> Prop} (l:exists x, P x) :=
  constructive_indefinition_descripption l.

Ltac IST := intro; subst; tauto.



Parameter Point Line Flat : Set.
Parameter Incid : Point -> Line -> Prop.
Parameter Incid_P_F : Point -> Flat -> Prop.
Parameter l0 : Line.

(* 注解中给予的补充定义 *)
Definition Incid_L_F (l: Line) (f:Flat) : Prop := 
  forall A, Incid A l -> Incid_P_F A f.

Definition Col (A B C:Point) : Prop :=
  exists l, Incid A l /\ Incid B l /\ Incid C l.

Definition Cof A B C D := exists f, Incid_P_F A f /\ 
  Incid_P_F B f /\ Incid_P_F C f /\ Incid_P_F D f.



(* Group 1:关联公理 *)
Axiom Incid_1 : forall A B, A<>B -> 
  exists! l, Incid A l /\ Incid B l.

Axiom Incid_3_1 : forall l, exists A B, 
   A<>B /\ Incid A l /\ Incid B l.

Axiom Incid_3_2: exists A B C,  ~ Col A B C.

Axiom Incid_4_1: forall A B C, ~ Col A B C ->
  exists! f, Incid_P_F A f /\ 
  Incid_P_F B f /\ Incid_P_F C f.

Axiom Incid_4_2: forall f, exists A, Incid_P_F A f.

Axiom Incid_6 : forall l f A B, A<>B -> 
  Incid A l -> Incid B l -> 
  Incid_P_F A f -> Incid_P_F B f -> Incid_L_F l f.

Axiom Incid_7 : forall A f1 f2, f1<>f2 -> 
  Incid_P_F A f1 -> Incid_P_F A f2 ->
    exists B, A<>B /\ Incid_P_F B f1 /\ Incid_P_F B f2.

Axiom Incid_8 : exists A B C D,  ~ Cof A B C D.

Ltac Col_P := match goal with H: Col ?A ?B ?C |- _ =>
  destruct H as [lt]; exists lt; tauto end.

Ltac n_Col_P := match goal with H: ~ Col ?A ?B ?C |- _ =>
  intro; apply H; Col_P end.

Ltac Cof_P := match goal with H: Cof ?A ?B ?C ?D |- _ =>
  destruct H as [lt]; exists lt; tauto end.

Ltac n_Cof_P := match goal with H: ~Cof ?A ?B ?C ?D |- _ =>
  intro; apply H; Cof_P end. 

Fact P_existsl : forall A, exists l, Incid A l.
Proof.
  intros. destruct (classic (Incid A l0)).
  - exists l0. auto.
  - pose proof (Incid_3_1 l0) as [P[Q]].
    destruct (classic(A=P)). subst. tauto.
    apply Incid_1 in H1 as [l'[]]. exists l'. tauto.
Qed.  

Fact Col_tP : forall A B, Col A A B.
Proof.
  intros. destruct (classic(A=B)).
  - subst. pose proof (P_existsl B) as [l].
    exists l; tauto. 
  - apply Incid_1 in H as [l[]].
    exists l. tauto.
Qed.

Fact not_Col : forall A B C, ~ Col A B C 
  -> A<>B /\ A<>C /\ B<>C.
Proof.
  intros; repeat(split); intro;
  subst. pose proof (Col_tP B C). tauto.
  pose proof (Col_tP B C). apply H. Col_P. 
  pose proof (Col_tP C A). apply H. Col_P. 
Qed.
 
Parameter BetH : Point -> Point -> Point -> Prop.

(* 直线l与线段AB有交点 *)
Definition inter (l:Line) (A B:Point) :=
  ~ Incid A l /\ ~ Incid B l /\
  exists I, Incid I l /\ BetH A I B.

Axiom BetH_1_1 : forall A B C, BetH A B C -> Col A B C.

Axiom BetH_1_2: forall A B C, BetH A B C -> A <> C.

Axiom BetH_1_3: forall A B C, BetH A B C -> BetH C B A.

Axiom BetH_2 : forall A B, A <> B -> exists C, BetH A B C.

Axiom BetH_3 : forall A B C, BetH A B C -> ~ BetH B C A.

Axiom BetH_4: forall A B C l (H: ~ Col A B C), 
  Incid_L_F l (proj1_sig (Cid ( Incid_4_1 A B C H ))) ->
  ~ Incid C l -> inter l A B -> inter l A C \/ inter l B C.

Corollary BetH_diff12 : forall A B C, BetH A B C -> A <> B.
Proof.
  intros. pose proof H. 
  intro. apply BetH_1_3 in H0. 
  apply BetH_3 in H0.
  subst. tauto.
Qed.

Corollary BetH_diff23 : forall A B C, BetH A B C -> B <> C.
Proof.
  intros. apply BetH_1_3 in H. 
  apply BetH_diff12 in H. auto.   
Qed.

Corollary BetH_diff_P : forall A B C, BetH A B C -> 
  A<>B /\ A<>C /\ B<>C.
Proof.
  intros. split. eapply BetH_diff12; eauto.
  split. eapply BetH_1_2; eauto.
  eapply BetH_diff23; eauto.
Qed. 

(* 有两公共点的两直线是同一条直线 *) 
Lemma line_eq : forall A B l1 l2, A<>B 
  -> Incid A l1 -> Incid B l1
  -> Incid A l2 -> Incid B l2 
  -> l1=l2.
Proof.
  intros. apply Incid_1 in H as [l[]].
  assert (l=l1). { apply H4. auto. }
  assert (l=l2). { apply H4. auto. }
  subst. auto.
Qed.

Lemma unCol_t : forall A B C l,
  A<>B -> Incid A l -> Incid B l -> ~ Incid C l -> ~ Col A B C.
Proof.
  intros. intro. destruct H3.
  apply (line_eq A B l x) in H; try tauto.
  subst. tauto. 
Qed.

(* 过一直线和不在这直线上的一点，恒有一个而且只有一个平面 *)

Theorem Theorem2_1 : forall l C, ~ (Incid C l) -> 
  exists! f, Incid_P_F C f /\ Incid_L_F l f.
Proof.
  intros.
  pose proof (Incid_3_1 l) as [A[B[]]].
  assert(~ Col A B C). {
  eapply unCol_t; eauto; tauto. }
  pose proof H2 as H2'.
  apply Incid_4_1 in H2 as [f[]].
  exists f. split. split. tauto.
  eapply Incid_6; eauto; tauto.
  intros. apply H3. destruct H4. 
  repeat split; auto; apply H5; tauto.
Qed.

Lemma outline : forall l, exists A,  ~ Incid A l.
Proof.
  intros. pose proof (Incid_3_2) as [A[ B [C H2]]].
  destruct (classic (Incid A l)).
  - destruct (classic (Incid B l)).
    + assert(~ Incid C l). { intro.
      apply H2. exists l; auto. }
      exists C; auto. 
    + exists B; auto.
  - exists A; auto. 
Qed.

(* 定理4： 一直线上的任意三点A,B,C中，必有一点在其他两点之间 *)

Theorem Theorem4_1 : forall A B C, A<>B -> B<>C -> C<>A 
  -> Col A B C -> 
  ( BetH A C B \/ BetH B A C \/ BetH A B C ).
Proof. 
  intros A B C HAB HBC HCA H.
  destruct H as [l [HA [HB HC]]].
  destruct (classic (BetH A C B)); auto.
  destruct (classic (BetH B A C)); auto. 
  pose proof (outline l) as [D H2].
  assert (A<>D). { IST. }
  pose proof H1. apply Incid_1 in H3 as [l0[]].
  assert (B<>D). { IST. }
  apply BetH_2 in H5 as [G].
  pose proof H5.
  apply BetH_diff_P in H6 as [H6A[H6B H6C]].
  pose proof H5. apply BetH_1_1 in H6 as [l1].
  assert(~Incid G l). { intro.
  apply (line_eq B G l l1) in H6B; try tauto.
  subst. tauto. }
  assert(~Col B C G). { eapply unCol_t; eauto. }
  assert (~ Incid B l0).
  { intro. apply (line_eq A B l0 l) in HAB; try tauto.
    subst. tauto. }
  assert (~ Incid G l0). 
  { intro. apply (line_eq D G l0 l1) in H6C; try tauto.
    subst. tauto. } 
  assert (~ Incid C l0). 
  { intro. apply (line_eq C A l0 l) in HCA; try tauto.
    subst. tauto. } 
  assert (inter l0 B G). { repeat split; auto. 
  exists D. tauto. }
  assert(~Col B G C). { n_Col_P. }
  pose proof (Theorem2_1 l D H2) as [f[[HfA HfB] HfC]].
  assert(Incid_L_F l1 f) as Hl1.
  { apply (Incid_6 l1 f B D); try tauto.
    apply HfB; tauto. }
  assert(Incid_L_F l0 f) as Hl0.
  { apply (Incid_6 l0 f A D); try tauto.
    apply HfB; tauto. }
  assert(Incid_P_F G f) as HG. { apply Hl1; tauto. }
  assert(inter l0 B C \/ inter l0 G C) as []. {
  apply BetH_4 with H13; auto.
  pose proof (proj2_sig (Cid (Incid_4_1 B G C H13))) as [].
  set (proj1_sig (Cid (Incid_4_1 B G C H13))) as f1.
  assert(f1=f). { apply H15. 
  repeat split; auto; apply HfB; auto. }
  subst. auto. }
  - destruct H14 as [H14A [H14B [E []]]].
    assert(A<>E). { IST. }
    apply BetH_1_1 in H15 as [l'].
    apply (line_eq B C l' l) in HBC; try tauto.
    subst. apply (line_eq A E l l0) in H16; try tauto.
    subst. tauto. 
  - assert(~Col A B G). { eapply unCol_t; eauto. }
    assert(C<>D). { IST. } 
    pose proof H16 as HCD.
    apply Incid_1 in H16 as [l2[]].
    assert (~ Incid A l2).
    { intro. apply (line_eq C A l2 l) in HCA; try tauto.
      subst. tauto. }
    assert (~ Incid B l2). 
    { intro. apply (line_eq B C l2 l) in HBC; try tauto.
      subst. tauto. } 
    assert (~ Incid G l2). 
    { intro. apply (line_eq D G l2 l1) in H6C; try tauto.
    subst. tauto. } 
    assert (inter l2 B G). { repeat split; auto. 
    exists D. tauto. }
    assert(~Col B G A). { n_Col_P. }
    assert(Incid_L_F l2 f) as Hl2.
    { apply (Incid_6 l2 f C D); try tauto.
      apply HfB. tauto. }
    assert(inter l2 B A \/ inter l2 G A) as []. {
    apply BetH_4 with H22; auto.
    pose proof (proj2_sig (Cid (Incid_4_1 B G A H22))) as [].
    set (proj1_sig (Cid (Incid_4_1 B G A H22))) as f1.
    assert(f1=f). { apply H24. 
    repeat split; auto; apply HfB; tauto. }
    subst. auto. }
    + destruct H23 as [H23A [H23B [F[]]]].
      assert(F<>C). { intro. subst. 
      apply BetH_1_3 in H24; tauto. }
      apply BetH_1_1 in H24 as [l'].
      apply (line_eq A B l' l) in HAB; try tauto.
      subst. apply (line_eq F C l l2) in H25; try tauto.
      subst. tauto.
    + destruct H23 as [H23A [H23B [F[]]]].
      destruct H14 as [H14A [H14B [E []]]].
      pose proof H25 as H25'.
      apply BetH_1_1 in H25 as [l'].
      assert(E<>A). { intro. subst.
      apply (line_eq C A l' l) in HCA; try tauto.
      subst. tauto. }
      assert(E<>D). { intro. subst.
      apply (line_eq D G l' l1 ) in H6C; try tauto.
      subst. apply (line_eq B C l1 l) in HBC; try tauto.
      subst. tauto. }
      assert (~Col G A E). { 
      intro. destruct H28 as [l''].
      apply (line_eq E A l'' l0) in H26; try tauto.
      subst. tauto. } 
      assert (~ Incid E l2). 
      { intro. apply (line_eq E D l2 l0) in H27; try tauto.
        subst. tauto. }
      assert (inter l2 G A). { repeat split; auto. 
      exists F. tauto. }
      assert(inter l2 G E \/ inter l2 A E) as []. {
      apply BetH_4 with H28; auto.
      pose proof (proj2_sig (Cid (Incid_4_1  G A E H28))) as [].
      set (proj1_sig (Cid (Incid_4_1 G A E H28))) as f1.
      assert(f1=f). { apply H32. 
      repeat split; auto; apply HfB; tauto. }
      subst. auto. }
      * destruct H31 as [H31A [H31B [D'[]]]].
        pose proof H25'.
        apply BetH_diff12 in H25'.
        pose proof H32 as H32'.
        apply BetH_1_1 in H32 as [l''].
        apply (line_eq G E l'' l') in H25'; try tauto.
        subst. assert(D'<>C). { intro.
        subst. apply BetH_3 in H33.
        apply BetH_1_3 in H32'. tauto. }  
        apply (line_eq D' C l' l2) in H34; try tauto.
        subst; tauto. 
      * destruct H31 as [H31A [H31B [D'[]]]].
        destruct (classic (D' = D)).
        -- subst. assert (~Col A E C). { 
           intro. destruct H33 as [l''].
           apply (line_eq C A l'' l) in HCA; try tauto.
           subst. apply (line_eq E A l0 l) in H26; try tauto.
           subst. tauto. }
           assert (~ Incid A l1).
           { intro. apply (line_eq A B l1 l) in HAB; try tauto.
             subst. tauto. }
           assert (~ Incid E l1). 
           { intro. apply (line_eq E D l1 l0) in H27; try tauto.
             subst. tauto. } 
           assert (~ Incid C l1). 
           { intro. apply (line_eq B C l1 l) in HBC; try tauto.
             subst. tauto. } 
           assert (inter l1 A E). { repeat split; auto. 
           exists D. tauto. }
           assert(inter l1 A C \/ inter l1 E C) as []. {
           apply BetH_4 with H33; auto.
           pose proof (proj2_sig (Cid (Incid_4_1 A E C H33))) as [].
           set (proj1_sig (Cid (Incid_4_1 A E C H33))) as f1.
           assert(f1=f). { apply H39. 
           repeat split; auto; apply HfB; tauto. }
           subst. auto. }
           { destruct H38 as [H38A [H38B [B'[]]]].
             destruct (classic (B'=B)). subst. auto.
             apply BetH_1_1 in H39 as [l''].
             apply (line_eq C A l'' l) in HCA; try tauto.
             subst. apply (line_eq B' B l1 l) in H40; try tauto.
             subst. tauto. }
           { destruct H38 as [H38A [H38B [B'[]]]].
             pose proof H39.
             apply BetH_1_1 in H39 as [l''].
             pose proof H25'.
             apply BetH_diff23 in H25'.
             apply (line_eq E C l'' l') in H25'; try tauto.
             subst. assert (B'<>G). { intro. subst.
             apply BetH_1_3 in H40. apply BetH_3 in H40.
             tauto. } apply (line_eq B' G l' l1) in H42; try tauto.
             subst. tauto. }
        -- apply BetH_1_1 in H32 as [l''].
           apply (line_eq E A l'' l0) in H26; try tauto.
           subst. 
           apply (line_eq D' D l0 l2) in H33; try tauto.
           subst. tauto.
Qed. 
 
(* 定理四：一直线上的任意三点A,B,C中，只有一点在其他两点之间 *) 
     
Theorem Theorem4_2 : forall A B C,  BetH A B C ->  
  ~ BetH B C A /\ ~ BetH B A C.
Proof.
  intros. split.
  - apply BetH_3 in H. auto.
  - apply BetH_1_3 in H. 
    apply BetH_3 in H. auto.
Qed.


(* 定理5 ：一直线上的任意四点，恒能如是记之为A,B,C,D,使得记为B的这一点既在A和C之间，又在A和D之间；
          而且记为C的这一点既在A和D之间，又在B和D之间 *)

Lemma lem1_1_T5 : forall A B C D ,
  BetH A B C -> BetH B C D -> BetH A C D. 
Proof.
  intros. pose proof H. pose proof H0.
  apply BetH_diff_P in H1 as [H1[]]. 
  apply BetH_diff_P in H2 as [H2[]].
  pose proof H as H'.
  pose proof H0 as H0'. 
  apply BetH_1_1 in H'. apply BetH_1_1 in H0'.
  destruct H' as [l].
  destruct H0' as [l0].
  apply (line_eq B C l l0) in H4; try tauto.
  subst l0. pose proof (outline l) as [E HL].
  assert (C<>E). { IST. } 
  pose proof H4. apply BetH_2 in H9 as [F]. 
  pose proof H9. apply BetH_1_2 in H10. 
  pose proof H9. apply BetH_1_1 in H11 as [l0].
  assert (~ Col C F B). { intro.
  destruct H12 as [l']. 
  apply (line_eq B C l' l) in H2; try tauto. subst.
  apply (line_eq C F l l0) in H10; try tauto.
  subst. tauto. }
  assert(A<>E). { IST. }
  assert(E<>F). { apply BetH_diff23 in H9. auto. }
  pose proof H13 as H13'.
  apply Incid_1 in H13 as [l1[]]. 
  assert (~Incid F l1). { intro.
  apply (line_eq E F l1 l0) in H14; try tauto. 
  subst. apply (line_eq A C l l0) in H3; try tauto. 
  subst. tauto. } 
  assert (~Incid C l1). { intro.
  apply (line_eq A C l1 l) in H3; try tauto. 
  subst. tauto. } 
  assert (~Incid B l1). { intro.
  apply ( line_eq A B l1 l) in H1; try tauto. 
  subst. tauto. }
  assert (inter l1 C F).
  { repeat split; auto. exists E. tauto. }
  pose proof (Theorem2_1 l E HL) as [f[[HA HB] HC]].
  assert(Incid_L_F l1 f) as Hl1.
  { apply (Incid_6 l1 f A E); try tauto.
    apply HB; tauto. }
  assert(Incid_L_F l0 f) as Hl0.
  { apply (Incid_6 l0 f C E); try tauto.
    apply HB; tauto. }
  assert(inter l1 C B \/ inter l1 F B) as [].
  { apply BetH_4 with H12; auto.
    pose proof (proj2_sig (Cid (Incid_4_1 C F B H12))) as [].
    set (proj1_sig (Cid (Incid_4_1 C F B H12))) as f1.
    assert(f1=f). { apply H21.
    repeat split; try (apply HB; tauto).
    apply Hl0. tauto.  } subst. auto. }
  - destruct H20 as [H20A[H20B[G[]]]].
    pose proof H21.
    apply BetH_1_1 in H21 as [l'].
    apply (line_eq B C l' l) in H2; try tauto.
    subst. assert(A<>G). { intro. subst.
    apply Theorem4_2 in H22. tauto. }
    apply (line_eq A G l l1) in H2; try tauto.
    subst. tauto.
  - destruct H20 as [H20A[H20B[G[]]]].
    pose proof H21. apply BetH_diff_P in H21 as [H21[]].
    pose proof H22 as H22'.
    apply BetH_1_1 in H22 as [l'].
    assert(~ Incid G l). { intro.
    apply (line_eq G B l l') in H24; try tauto.
    subst l'. apply (line_eq C F l l0) in H10; try tauto.
    subst. tauto. }
    assert(~Col B D G). { eapply unCol_t; eauto; tauto. }
    assert(~Incid G l0). { intro. 
    apply (line_eq F G l0 l') in H21; try tauto. subst.
    apply (line_eq B C l l') in H2; try tauto. subst.
    tauto. }
    assert (~Incid B l0). { intro.
    apply (line_eq F B l0 l') in H23; try tauto. 
    subst. tauto. }
    assert (~Incid D l0). { intro.
    apply ( line_eq C D l0 l) in H6; try tauto. 
    subst. tauto. }
    assert(inter l0 B D). { repeat (split; auto).
    exists C; tauto. }
    assert(inter l0 B G \/ inter l0 D G) as [].
    { apply BetH_4 with H26; auto.
      pose proof (proj2_sig (Cid (Incid_4_1 B D G H26))) as [].
      set (proj1_sig (Cid (Incid_4_1 B D G H26))) as f1.
      assert(f1=f). { apply H32.
      repeat split; try (apply HB; tauto).
      apply Hl1; tauto. } subst. auto. }
    + destruct H31 as [H31A[H31B[P[]]]].
      pose proof H32. apply BetH_1_1 in H33 as [l''].
      apply (line_eq G B l'' l') in H24; try tauto.
      subst. assert(P<>F). { intro. subst.
      apply BetH_3 in H32. tauto. }
      apply (line_eq P F l' l0) in H24; try tauto.
      subst. tauto.
    + destruct H31 as [H31A[H31B[P[]]]].
      assert (A<>D). { intro. subst.
      apply BetH_3 in H. tauto. }
      assert(~Col A D G). 
      { apply unCol_t with (l:=l); tauto. }
      assert (~Incid A l0). { intro.
      apply (line_eq A C l0 l) in H3; try tauto. 
      subst. tauto. }
      assert(inter l0 D G). { repeat (split; auto).
      exists P; tauto. }
      assert(~Col D G A). { n_Col_P. }
      assert(inter l0 D A \/ inter l0 G A) as [].
      { apply BetH_4 with H37; auto. 
        pose proof (proj2_sig (Cid (Incid_4_1 D G A H37))) as [].
        set (proj1_sig (Cid (Incid_4_1 D G A H37))) as f1.
        assert(f1=f). { apply H39.
        repeat split; try (apply HB; tauto).
        apply Hl1; tauto. } subst. auto. }
      * destruct H38 as [H38A[H38B[C'[]]]].
        destruct (classic (C=C')). 
        subst. apply BetH_1_3. auto.
        apply BetH_1_1 in H39 as [l''].
        apply (line_eq A D l l'') in H33; try tauto.
        subst l''. apply (line_eq C C' l l0) in H40; try tauto.
        subst. tauto. 
      * destruct H38 as [H38A[H38B[C'[]]]].
        pose proof H39. assert(A<>G). {
        IST. }
        assert(~Col A C E). { eapply unCol_t; eauto; tauto. }
        assert(~Incid A l'). { intro. 
        apply (line_eq A B l' l) in H1; try tauto.
        subst. tauto. }
        assert(~Incid C l'). { intro. 
        apply (line_eq B C l' l) in H2; try tauto.
        subst. tauto. }
        assert(~Incid E l'). { intro.
        apply (line_eq E F l' l0) in H14; try tauto.
        subst. tauto. }
        assert(inter l' A C). { repeat (split; auto).
        exists B; tauto. }
        assert(inter l' A E \/ inter l' C E) as [].
        { apply BetH_4 with H42; auto. 
          pose proof (proj2_sig (Cid (Incid_4_1 A C E H42))) as [].
          set (proj1_sig (Cid (Incid_4_1 A C E H42))) as f1.
          assert(f1=f). { apply H48.
          repeat split; try (apply HB; tauto); auto. }
          subst. apply (Incid_6 l' f1 F B); try tauto.
          apply Hl0; tauto. apply HB; tauto. } 
        destruct H47 as [H47A[H47B[G'[]]]].
        -- destruct (classic (G'=G)). subst.
           apply BetH_1_1 in H40 as [l''].
           apply (line_eq A G l'' l1) in H41; try tauto.
           subst. assert(C'<>E). { intro. subst.
           apply Theorem4_2 in H48. tauto. }
           apply (line_eq C' E l0 l1) in H41; try tauto.
           subst. tauto. 
           apply BetH_1_1 in H48 as [l''].
           apply (line_eq A E l'' l1) in H13'; try tauto.
           subst. apply (line_eq G' G l' l1) in H49; try tauto.
           subst. tauto.
        -- destruct H47 as [H47A[H47B[G'[]]]].
           assert(G'<>F). { intro. subst.
           apply Theorem4_2 in H9. 
           apply BetH_1_3 in H48. tauto. }
           apply BetH_1_1 in H48 as [l''].
           apply (line_eq C E l'' l0) in H4; try tauto.
           subst. apply (line_eq G' F l' l0) in H49; subst; tauto.
Qed.


Lemma lem1_2_T5 : forall A B C D, BetH A B C -> 
  BetH B C D -> BetH A B D.
Proof. 
  intros. apply BetH_1_3. 
  apply BetH_1_3 in H.
  eapply lem1_1_T5; eauto. 
  apply BetH_1_3; auto.
Qed.

Lemma lem1_T5 : forall A B C D, BetH A B C -> 
  BetH B C D -> BetH A C D /\ BetH A B D.
Proof.
  intros. split. eapply lem1_1_T5; eauto.
  eapply lem1_2_T5; eauto.
Qed.
 
Lemma lem2_1_T5 : forall A B C D, BetH A B C -> 
  BetH A C D -> BetH B C D.
Proof.
  intros. pose proof H. pose proof H0.
  apply BetH_diff_P in H1 as [H1[]]. 
  apply BetH_diff_P in H2 as [H2[]].
  pose proof H as H'.
  pose proof H0 as H0'. 
  apply BetH_1_1 in H' as [l].
  apply BetH_1_1 in H0' as [l0].
  apply (line_eq A C l l0) in H2; try tauto.
  subst l0. pose proof (outline l) as [G HL].
  assert(B<>G). { IST. }
  pose proof H2. apply BetH_2 in H9 as [F].
  pose proof H9. apply BetH_1_1 in H10 as [l0].
  pose proof H9. apply BetH_diff_P in H11 as [H11A[H11B]].
  assert(~Incid F l). { intro.
  apply (line_eq B F l l0) in H11B; try tauto.
  subst. tauto. }
  assert(C<>F). { IST. }
  pose proof H13. apply Incid_1 in H14 as [l1[]].
  assert(~Col A D G). { eapply unCol_t; eauto; tauto. }
  assert (~Incid A l1). { intro.
  apply (line_eq A C l1 l) in H3; try tauto. 
  subst. tauto. } 
  assert (~Incid D l1). { intro.
  apply ( line_eq C D l1 l) in H6; try tauto. 
  subst. tauto. }
  assert(~Incid G l1). { intro.
  apply (line_eq G F l1 l0) in H11; try tauto.
  subst. apply ( line_eq B C l0 l) in H4; try tauto. 
  subst. tauto. } 
  assert (inter l1 A D).
  { repeat split; auto. exists C. tauto. }
  pose proof (Theorem2_1 l G HL) as [f[[HA HB] HC]].
  assert(Incid_P_F A f /\ Incid_P_F B f /\ 
  Incid_P_F C f /\ Incid_P_F D f) as HD.
  { repeat split; apply HB; tauto. }
  assert(Incid_L_F l0 f) as Hl0.
  { apply (Incid_6 l0 f B G); tauto. }
  assert(Incid_P_F F f) as HF.
  { apply Hl0; tauto. }
  assert(Incid_L_F l1 f) as Hl1.
  { apply (Incid_6 l1 f C F); tauto. }
  assert(inter l1 A G \/ inter l1 D G) as [].
  { apply BetH_4 with H16; auto. 
    pose proof (proj2_sig (Cid (Incid_4_1 A D G H16))) as [].
    set (proj1_sig (Cid (Incid_4_1 A D G H16))) as f1.
    assert(f1=f). { apply H22. tauto. }
    subst. auto. }
  - assert(A<>G). { IST. }
    pose proof H22. apply Incid_1 in H23 as [l2[]].
    assert(Incid_L_F l2 f) as Hl2. {
    apply (Incid_6 l2 f A G); tauto. }
    assert(~Col B C F). { eapply unCol_t; eauto; tauto. }
    assert (~Incid B l2). { intro.
    apply (line_eq A B l2 l) in H1; try tauto. 
    subst. tauto. } 
    assert (~Incid C l2). { intro.
    apply ( line_eq A C l2 l) in H3; try tauto. 
    subst. tauto. }
    assert(~Incid F l2). { intro.
    apply (line_eq G F l2 l0) in H11; try tauto.
    subst. tauto. }
    assert (inter l2 B F).
    { repeat split; auto. exists G. tauto. }
    assert(~Col B F C). { n_Col_P. }
    assert(inter l2 B C \/ inter l2 F C) as [].
    { apply BetH_4 with H30; auto. 
      pose proof (proj2_sig (Cid (Incid_4_1 B F C H30))) as [].
      set (proj1_sig (Cid (Incid_4_1 B F C H30))) as f1.
      assert(f1=f). { apply H32. tauto. }
      subst. auto. } 
    + destruct H31 as [H31A[H31B[A'[]]]].
      destruct (classic(A'=A)).
      subst. apply Theorem4_2 in H32; tauto.
      apply (line_eq A' A l2 l) in H33; try tauto.
      subst. tauto. apply BetH_1_1 in H32 as [l'].
      apply (line_eq B C l' l) in H4; try tauto.
      subst. tauto.
    + destruct H31 as [H31A[H31B[A'[]]]].
      pose proof H32. apply BetH_1_1 in H33 as [l'].
      pose proof H32. apply BetH_diff_P in H34 as [H34A[H34B]].
      apply (line_eq C F l' l1) in H13; try tauto.
      subst.
      assert(~Col A C A').
      { intro. destruct H13 as[l'].
      apply (line_eq A C l' l) in H3; try tauto.
      subst. apply (line_eq A' C l1 l) in H34; try tauto. 
      subst. tauto. }
      assert (~Incid A l0). { intro.
      apply (line_eq A B l0 l) in H1; try tauto. 
      subst. tauto. }
      assert(~Incid C l0). { intro.
      apply (line_eq B C l0 l) in H4; try tauto.
      subst. tauto. }
      assert (~Incid A' l0). { intro.
      apply (line_eq F A' l0 l1) in H34A; try tauto.
      subst. tauto. }
      assert (inter l0 A C).
      { repeat split; auto. exists B. tauto. }
      assert(inter l0 A A' \/ inter l0 C A') as [].
      { apply BetH_4 with H13; auto. 
        pose proof (proj2_sig (Cid (Incid_4_1 A C A' H13))) as [].
        set (proj1_sig (Cid (Incid_4_1 A C A' H13))) as f1.
        assert(f1=f). { apply H40; repeat split; try tauto.
        apply Hl2; auto. } subst. auto. }
      * destruct H39 as [H39A[H39B[G'[]]]].
        destruct (classic(G'=G)).
        subst. destruct H21 as [H21A[H21B[P[]]]].
        assert(A'<>P). { intro. subst.
        apply Theorem4_2 in H41. apply BetH_1_3 in H40. tauto. }
        apply (line_eq A' P l1 l2) in H42; try tauto.
        subst. tauto. apply BetH_1_1 in H41 as [l'].
        apply (line_eq A G l' l2) in H22; try tauto.
        subst. tauto.
        apply BetH_1_1 in H40 as [l'].
        assert(A<>A'). { IST. }
        apply (line_eq A A' l' l2) in H42; try tauto.
        subst. apply (line_eq G' G l0 l2) in H41; try tauto.
        subst. tauto.
      * destruct H39 as [H39A[H39B[G'[]]]].
        pose proof H40. apply BetH_1_1 in H41 as [l'].
        apply (line_eq A' C l' l1) in H34; try tauto.
        subst. assert(F<>G').
        { intro. subst. apply BetH_3 in H40. tauto. }
        apply (line_eq F G' l1 l0) in H34; try tauto.
        subst. tauto.
  - destruct H21 as [H21A[H21B[P[]]]].
    assert(B<>D). { intro. subst.
    apply BetH_3 in H0. apply BetH_1_3 in H; tauto. }
    assert(~Col B D G). { apply unCol_t with (l:=l); tauto. } 
    assert (~Incid B l1). { intro.
    apply (line_eq B F l1 l0) in H11B; try tauto. 
    subst;  tauto. }
    assert (inter l1 D G).
    { repeat split; auto. exists P. tauto. }
    assert(~Col D G B). { n_Col_P. }
    assert(inter l1 D B \/ inter l1 G B) as [].
    { apply BetH_4 with H27; auto. 
      pose proof (proj2_sig (Cid (Incid_4_1 D G B H27))) as [].
      set (proj1_sig (Cid (Incid_4_1 D G B H27))) as f1.
      assert(f1=f). { apply H29; tauto. } subst. auto. }
    + destruct H28 as [H28A[H28B[C'[]]]].
      destruct (classic (C'=C)).
      subst. apply BetH_1_3. auto.
      apply (line_eq C' C l1 l) in H30; try tauto.
      subst. tauto. apply BetH_1_1 in H29 as [l'].
      apply (line_eq B D l' l) in H23; try tauto.
      subst. tauto.
    + destruct H28 as [H28A[H28B[C'[]]]].
      assert(C'<>F). { intro. subst.
      apply Theorem4_2 in H9. tauto. }
      apply BetH_1_1 in H29 as [l'].
      apply (line_eq B G l' l0) in H11A; try tauto.
      subst. apply (line_eq C' F l0 l1) in H30; try tauto.
      subst. tauto.
Qed.

Lemma lem2_T5 : forall A B C D,  BetH A B C -> BetH A C D 
  ->  BetH B C D /\ BetH A B D.
Proof.
  intros. pose proof (lem2_1_T5 A B C D H H0).
  split; auto.
  apply (lem1_T5 A B C D); auto.  
Qed.
  
Lemma lem3_T5 : forall A B C D l, 
  A<>B -> B<>C -> C<>D -> A<>D -> A<>C -> B<>D ->
  Incid A l -> Incid B l -> Incid C l -> Incid D l -> 
  (BetH A B C /\ BetH A D C)\/ (BetH A C B /\ BetH A D B) \/
  (BetH B A C /\ BetH B D C) \/ (BetH B A D /\ BetH B C D) \/ 
  (BetH C A D /\ BetH C B D) \/ (BetH A B D /\ BetH A C D).
Proof.
  intros. destruct (classic (BetH A B C /\ BetH A D C)); auto.
  apply not_and_or in H9 as [].
  - assert(Col A B C). { exists l; auto. }
    apply Theorem4_1 in H10; auto.
    destruct H10 as [H10|[H10|H10]]; try tauto.
    + destruct (classic (BetH A D B)); auto.
      assert(Col A D B). { exists l; auto. }
      apply Theorem4_1 in H12; auto.
      destruct H12 as [H12|[H12|H12]]; try tauto.
      * pose proof (lem2_T5 A C B D H10 H12). tauto.
      * apply BetH_1_3 in H10. apply BetH_1_3 in H12.
        pose proof (lem2_T5 B C A D H10 H12). tauto. 
    + destruct (classic (BetH B D C)); auto.
      assert(Col B D C). { exists l; auto. }
      apply Theorem4_1 in H12; auto.
      destruct H12 as [H12|[H12|H12]]; try tauto.
      * pose proof (lem2_T5 B A C D H10 H12). tauto.
      * apply BetH_1_3 in H10. apply BetH_1_3 in H12.
        pose proof (lem2_T5 C A B D H10 H12). tauto.
  - assert(Col A D C). { exists l; auto. }
    apply Theorem4_1 in H10; auto.
    destruct H10 as [H10|[H10|H10]]; try tauto.
    + destruct (classic (BetH A B D)). auto 7.
      assert(Col A B D). { exists l; auto. }
      apply Theorem4_1 in H12; auto.
      destruct H12 as [H12|[H12|H12]]; try tauto.
      * pose proof (lem2_T5 A C D B H10 H12). tauto.
      * apply BetH_1_3 in H10. apply BetH_1_3 in H12.
        pose proof (lem2_T5 D C A B H10 H12) as [].
        apply BetH_1_3 in H14. 
        apply BetH_1_3 in H12. tauto. 
    + apply BetH_1_3 in H10. 
      destruct (classic (BetH C B D)); auto 7.
      assert(Col C B D). { exists l; auto. }
      apply Theorem4_1 in H12; auto.
      destruct H12 as [H12|[H12|H12]]; try tauto.
      * pose proof (lem2_T5 C A D B H10 H12) as [].
        apply BetH_1_3 in H12. apply BetH_1_3 in H14. auto.
      * apply BetH_1_3 in H10. apply BetH_1_3 in H12.
        pose proof (lem2_T5 D A C B H10 H12) as []. 
        apply BetH_1_3 in H14. apply BetH_1_3 in H12. auto 6.
Qed.
 

Theorem Theorem5 : forall A B C D, B<>C ->
  BetH A B D -> BetH A C D -> 
  ( BetH A B C /\ BetH B C D) \/
  ( BetH A C B /\ BetH C B D). 
Proof.
  intros. pose proof H0 as H0'. 
  apply BetH_diff_P in H0' as [HA [HB HC]].
  destruct (classic (BetH A B C)). 
  - pose proof (lem2_T5 A B C D H2 H1). tauto.
  - assert(Col A B C). { apply BetH_1_1 in H0 as []. 
    apply BetH_1_1 in H1 as [].
    apply (line_eq A D x x0) in HB; try tauto.
    subst. exists x0. tauto. } 
    apply Theorem4_1 in H3; auto.
    destruct H3 as [H3|[H3|H3]]; try tauto.
    + pose proof (lem2_T5 A C B D H3 H0). tauto.
    + apply BetH_1_3 in H3.
      pose proof (lem1_T5 C A B D H3 H0) as [].
      apply Theorem4_2 in H5. tauto.
    + apply BetH_diff12 in H1. auto.     
Qed.


Definition diff_side_L A B a := inter a A B.

Lemma Col_F : forall A B C f, 
  A<>B -> Col A B C -> Incid_P_F A f -> 
  Incid_P_F B f -> Incid_P_F C f.
Proof.
  intros. destruct H0 as [l].
  apply (Incid_6 l f A B ); auto; tauto.
Qed.

Fact inter_cof : forall A B l, inter l A B ->
  exists f, Incid_P_F A f /\ Incid_P_F B f /\ Incid_L_F l f.
Proof.
  intros. destruct H as [H[]].
  destruct H1 as [I[]].
  apply Theorem2_1 in H as [f[]].
  destruct H. exists f. repeat (split; auto).
  apply H4 in H1. apply (Col_F A I B); auto.
  eapply BetH_diff12; eauto.
  apply BetH_1_1. auto.
Qed.

Definition same_side_L A A' a f :=
  Incid_P_F A f /\ Incid_P_F A' f /\
  Incid_L_F a f /\ ~ Incid A a /\
  ~ Incid A' a /\ ~ inter a A A'.

Definition same_side_L_eq A A' a :=
  exists P, inter a A P /\ inter a A' P. 

Lemma same_side_l1 : forall A A' a,
  same_side_L_eq A A' a -> exists f,
  Incid_P_F A f /\ Incid_P_F A' f /\
  Incid_L_F a f.
Proof.
  intros.  
  destruct H as [P[]].
  destruct H,H0,H1,H2.
  destruct H3 as [I[]].
  destruct H4 as [I0[]].
  pose proof H5 as H5'.
  apply BetH_1_1 in H5 as [l0].
  pose proof H6 as H6'.
  apply BetH_1_1 in H6 as [l1].
  apply Theorem2_1 in H1 as [f[[H1]]].
  assert (Incid_L_F l0 f).
  { apply (Incid_6 l0 f P I); try tauto.
  apply BetH_diff23 in H5'. auto.
  apply H7 in H3. auto. }
  assert (Incid_L_F l1 f).
  { apply (Incid_6 l1 f P I0); try tauto.
  apply BetH_diff23 in H6'. auto.
  apply H7 in H4. auto. }
  exists f. destruct H5,H6.
  apply H9 in H5. apply H10 in H6.
  tauto.
Qed.

Lemma BetH_Ips_P : forall A B C D, BetH A C D 
  -> BetH B C D -> ~ BetH A C B. 
Proof.
  intros.  
  pose proof H. apply BetH_diff_P in H1.
  pose proof H0. apply BetH_diff_P in H2.
  pose proof H. apply BetH_1_1 in H3 as []. 
  pose proof H0. apply BetH_1_1 in H4 as []. 
  destruct H1 as [H1 [H1' H1'']].
  apply (line_eq C D x x0) in H1''; try tauto. subst.
  assert(Col A C B). { exists x0; tauto. } 
  destruct H2 as [H2' ].
  intro. pose proof H6. apply BetH_diff_P in H7. 
  assert (BetH A B C /\ BetH A D C \/
     BetH A C B /\ BetH A D B \/
     BetH B A C /\ BetH B D C \/
     BetH B A D /\ BetH B C D \/
     BetH C A D /\ BetH C B D \/
     BetH A B D /\ BetH A C D).
  { apply lem3_T5 with (l:=x0); try tauto. }  
  destruct H8 as [H8|[H8|[H8|[H8|[H8|H8]]]]]; 
  destruct H8.
  - apply BetH_3 in H8. apply BetH_1_3 in H6. tauto.
  - apply BetH_1_3 in H9. 
    pose proof (lem2_T5 B C D A H0 H9) as [].
    apply Theorem4_2 in H10. 
    apply BetH_1_3 in H. tauto.
  - apply BetH_3 in H9. 
    apply BetH_1_3 in H0. tauto.
  - apply BetH_1_3 in H.
    apply BetH_1_3 in H8.
    pose proof (lem2_T5 D C A B H H8) as []. 
    apply Theorem4_2 in H10. tauto.
  - apply Theorem4_2 in H9. tauto. 
  - apply BetH_1_3 in H0. 
    apply BetH_1_3 in H8.
    pose proof (lem2_T5 D C B A H0 H8) as []. 
    apply Theorem4_2 in H10.
    apply BetH_1_3 in H6. tauto.
Qed.

Lemma Col_notinter : forall A B C l, 
  Col A B C -> inter l A B -> 
  inter l A C -> ~ inter l B C.
Proof.
  intros.
  intro. destruct H0 as [H0A [H0B]].
  destruct H1 as [H1A[H1B]].
  destruct H0 as [I[]]. 
  destruct H1 as [I0[]].
  destruct H as [l0].
  pose proof H3 as H3'.
  apply BetH_1_1 in H3' as [x].
  pose proof H3 as H3''.
  apply BetH_1_2 in H3.
  destruct (classic (I=I0)). 
  - subst. destruct H2 as [H2A[H2B]].
    destruct H2 as [I1[]]. 
    destruct (classic(I0=I1)).
    + subst. apply BetH_1_3 in H6. 
      apply (BetH_Ips_P A) in H6; auto. 
    + apply (line_eq I0 I1 l l0) in H7; auto.
      subst. tauto. 
      apply (line_eq A B l0 x) in H3; try tauto.
      subst. tauto. pose proof H6.
      apply BetH_1_2 in H8.
      apply BetH_1_1 in H6 as [].
      apply (line_eq B C l0 x0) in H8; try tauto.
      subst. tauto. 
  - apply (line_eq I I0 l l0) in H6; auto.
    subst. tauto. 
    apply (line_eq A B l0 x) in H3; try tauto.
    subst. tauto. pose proof H4.
    apply BetH_1_2 in H7.
    apply BetH_1_1 in H4 as [].
    apply (line_eq A C l0 x0) in H7; try tauto.
    subst. tauto.
Qed. 

Lemma Col_inter : forall A B C l, Col A B C -> 
  ~ Incid C l -> inter l A B -> 
  inter l C B \/ inter l A C.
Proof.
  intros. destruct H1 as [H1 [H1' [I [H1'' H2]]]].
  destruct H. assert (inter l A B).
  { repeat(split; auto). exists I; auto. } 
  destruct (classic (A=C)).
  - subst. auto. 
  - destruct (classic (B=C)). 
    + subst; auto.
    + pose proof H2. apply BetH_1_1 in H2 as [].
      pose proof H6. apply BetH_diff_P in H6. 
      destruct H6 as [H6'[]].
      destruct (classic (BetH A B C)). 
      pose proof (lem2_T5 A I B C H7 H9).
      right. repeat(split; auto). 
      * exists I; tauto.
      * destruct (classic (BetH A C B)). 
        assert(I<>C). { IST. }
        pose proof (Theorem5 A I C B H11 H7 H10).
        destruct H12. right. 
        repeat(split; auto). exists I; tauto.
        left. repeat(split; auto).
        exists I; tauto.
        assert (BetH A C B \/ BetH B A C \/ BetH A B C).
        { apply Theorem4_1; auto. exists x; auto. } 
        repeat destruct H11; try tauto. 
        apply BetH_1_3 in H7. 
        pose proof (lem2_T5 B I A C H7 H11) as []. 
        apply BetH_1_3 in H13. left. 
        repeat(split; auto). exists I; auto.
Qed.

Lemma lem_inter_BetH_4 : forall A B C L M N l, 
  ~ Col A B C -> ~ Incid A l -> ~ Incid B l -> 
  ~ Incid C l ->  Incid L l ->  Incid N l -> Incid M l ->
  BetH L N M -> BetH A L B -> BetH A N C -> 
  BetH B M C -> False.
Proof.
  intros. assert(~Col L M B). { 
  eapply unCol_t; eauto.
  apply BetH_1_2 in H6. auto. }
  assert(A<>L) as HAL. { IST. } 
  pose proof H7. 
  apply BetH_1_1 in H11 as [l1].
  pose proof H8.
  apply BetH_1_1 in H12 as [l0].
  pose proof H9. 
  apply BetH_1_1 in H13 as [l2].
  assert (~Incid L l0). { intro.
  apply (line_eq A L l1 l0) in HAL; try tauto.
  subst. apply H. exists l0; tauto. } 
  assert(C<>M) as HCM. { IST. } 
  assert (~Incid M l0). { intro.
  apply (line_eq C M l2 l0) in HCM; try tauto.
  subst. apply H. exists l0; tauto. } 
  assert(inter l0 L M). { 
  repeat split; auto. exists N. tauto. } 
  assert(~Incid B l0). {
  intro. apply H. exists l0; tauto. }
  pose proof H as H'.
  apply not_Col in H'. pose proof H as H''.
  apply Incid_4_1 in H'' as [f[]].
  assert(Incid_L_F l1 f /\ Incid_L_F l0 f /\
  Incid_L_F l2 f) as [H18A[H18B H18C]].
  { repeat split. apply (Incid_6 l1 f A B); tauto.
    apply (Incid_6 l0 f A C); tauto.
    apply (Incid_6 l2 f B C); tauto. }
  assert(inter l0 L B \/ inter l0 M B) as [].
  { apply BetH_4 with H10; auto. 
  pose proof ((proj2_sig (Cid (Incid_4_1 L M B H10)))) as [].
  set (proj1_sig (Cid (Incid_4_1 L M B H10))) as f1.
  assert(f1=f). { apply H21. repeat split.
  apply H18A; tauto. apply H18C; tauto. tauto. } 
  subst. auto. }
  - destruct H20 as [H20A[H20B [P[]]]].
    assert(P<>A). { intro. subst.
    apply Theorem4_2 in H21. tauto. } 
    apply BetH_1_1 in H21 as [l'].
    assert(L<>B). { intro. subst. auto. }
    apply (line_eq L B l' l1) in H23; try tauto.
    subst. apply (line_eq P A l0 l1) in H22; try tauto.
    subst. tauto.  
  - destruct H20 as [H20A[H20B[P[]]]].
    assert(P<>C). { intro. subst. 
    apply BetH_3 in H9. tauto. }
    assert(B<>M). { IST. }
    apply BetH_1_1 in H21 as [l'].
    apply (line_eq B M l' l2) in H23; try tauto.
    subst. apply (line_eq P C l0 l2) in H22; try tauto.
    subst. tauto.
Qed.

Lemma inter_BetH_4 : forall A B C l,
  ~ Col A B C -> inter l A B ->
  inter l A C -> ~ inter l B C.
Proof.
  intros. intro.
  destruct H0 as [H0A[H0B[L[]]]]. 
  destruct H2 as [H2A[H2B[M[]]]].
  destruct H1 as [H1A[H1B[N[]]]].
  assert(B<>M). { IST. }
  assert(A<>N). { IST. }
  assert(C<>N). { IST. }
  pose proof H3 as H3'.
  pose proof H4 as H4'.
  pose proof H5 as H5'.
  apply BetH_1_1 in H3 as [].
  apply BetH_1_1 in H4 as [].
  apply BetH_1_1 in H5 as [].
  assert(L<>M). { intro. subst.
  apply (line_eq B M x x0) in H6; try tauto.
  subst. apply H. exists x0; tauto. }
  assert(L<>N). { intro. subst.
  apply (line_eq A N x x1) in H7; try tauto.
  subst. apply H. exists x1; tauto. }
  assert(M<>N). { intro. subst.
  apply (line_eq C N x0 x1) in H8; try tauto.
  subst. apply H. exists x1; tauto. }
  assert( BetH L N M \/ BetH M L N \/ BetH L M N).
  { apply Theorem4_1; auto. exists l; auto. }
  destruct H12 as [H12|[H12|H12]].
  - apply (lem_inter_BetH_4 A B C L M N l); auto. 
  - apply (lem_inter_BetH_4 B C A M N L l); auto; 
    try (apply BetH_1_3; auto). n_Col_P. 
  - apply (lem_inter_BetH_4 B A C L N M l); auto;
    try (apply BetH_1_3; auto). n_Col_P.
Qed. 

Lemma exc_diff_side_L : forall A B a,
  diff_side_L A B a ->
  diff_side_L B A a.
Proof.
  intros;
  destruct H as [H[H1[P[]]]];
  apply BetH_1_3 in H2; repeat(split; auto);
  exists P; auto.
Qed.

Lemma same_side_l2 : forall A A' a,
  same_side_L_eq A A' a ->
  ~ Incid A a /\ ~ Incid A' a /\ ~ inter a A A'.
Proof.
  intros. destruct H as [P[]].
  pose proof H. pose proof H0. 
  destruct H,H0. 
  apply exc_diff_side_L in H1, H2. 
  destruct (classic(Col P A A')). 
  - pose proof (Col_notinter P A A' a H5 H1 H2).
    tauto.  
  - pose proof (inter_BetH_4 P A A' a H5 H1 H2).
    tauto. 
Qed.

Theorem Hil_T8_1 : forall a B A A',
  same_side_L_eq A B a -> 
  diff_side_L A' B a ->
  diff_side_L A A' a.
Proof.
  intros. pose proof H.
  apply same_side_l2 in H as [H [H' H'']].
  destruct (classic (Col A' B A)).
  - apply (Col_inter A' B A a) in H2 as []; auto.
    tauto. apply exc_diff_side_L. auto.
  - assert(inter a A' A \/ inter a B A) as [].
    { apply BetH_4 with H2; auto.
    apply inter_cof in H0 as [f].
    apply same_side_l1 in H1 as [f1]. 
    apply Theorem2_1 in H' as [f2[]].
    assert(f2=f /\ f2=f1) as [].
    { split; apply H4; tauto. } subst.
    pose proof ((proj2_sig (Cid 
    (Incid_4_1 A' B A H2)))) as [].
    set (proj1_sig (Cid (Incid_4_1 A' B A H2))) as f.
    assert(f=f1). { apply H6. tauto. }
    subst. tauto. } 
    apply exc_diff_side_L. auto.
    apply exc_diff_side_L in H3. tauto.
Qed.

Theorem Hil_T8_2 : forall a A A' B,
  diff_side_L A B a ->
  diff_side_L A' B a ->
  same_side_L_eq A A' a.
Proof. intros. exists B; auto. Qed.

Theorem Hil_T8_3 : forall a A A' B,
  same_side_L_eq A B a ->
  same_side_L_eq A' B a ->
  same_side_L_eq A A' a.
Proof.
  intros. pose proof H as [P[]].
  pose proof H0 as [Q[]]. exists P.
  split; auto. apply exc_diff_side_L.
  apply (Hil_T8_1 a Q P A'); auto. 
  apply Hil_T8_2 with (B:=B); 
  apply exc_diff_side_L; auto.
Qed. 