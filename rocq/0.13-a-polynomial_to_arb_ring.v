From Stdlib Require Import ZArith Reals Lists.List.
From Stdlib Require Import setoid_ring.Ring_theory.
From Stdlib Require Import Setoids.Setoid.
Require Import Morphisms.
Import ListNotations.
Require Import RelationClasses.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Section Evaluation.

  (** Proof of exercise 0.13 (a) in Leinster - Basic Category Theory
    I could not use the Horner homomorphism in MathComp because it assumes 
    a homomorphism to a commutative Ring, which is more restrictive than 
    what 0.13 (a) is asking.

    I represent a polynomial as a list of its coefficients in increasing order.

    [c0, c1, c2,.... ] = c0 + c1x + c2x^2 + ...

    For the uniqueness part of the question we need to show if an arbitrary mapping g
    is a homorphism then it is the polynomial evaluation function. The only structure 
    imposed on g is at [0,1], i.e p(r) = (0 + 1*r) it equals r, along with some other trivial
    regularity assumptions like g ( 0 + 0*r + 0*r^2 ) = g (0).  These regularity assumptions
    need to be provided as the checker does not know that a polynomial, whose coefficients 
    are represented by [0, 0, 0] is zero as is [0].
  **)

(** 1. Representing Z[x] as a list of integer coefficients **)
Definition poly_Z := list Z.

Fixpoint poly_add (p q : poly_Z) : poly_Z :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | c1 :: t1, c2 :: t2 => (c1 + c2)%Z :: poly_add t1 t2
  end.

Theorem poly_add_comm : forall p q, poly_add p q = poly_add q p.
Proof.
  intros p. induction p as [| c1 t1 IH].
  - (* Base Case: p = [] *)
    intros q. destruct q as [| c2 t2].
    + (* q = [] *) reflexivity.
    + (* q = c2 :: t2 *) reflexivity.
  - (* Inductive Step: p = c1 :: t1 *)
    intros q. destruct q as [| c2 t2].
    + (* q = [] *) reflexivity.
    + (* q = c2 :: t2 *)
      simpl.
      rewrite Z.add_comm.
      rewrite IH.
      reflexivity.
Qed.

Fixpoint poly_scalar_mul (a : Z) (p : poly_Z) : poly_Z :=
  match p with
  |[] => []
  | c :: t => (a * c)%Z :: poly_scalar_mul a t
  end.

Fixpoint poly_mul (p q : poly_Z) : poly_Z :=
  match p with
  | [] => []
  | c :: t => poly_add (poly_scalar_mul c q) (0%Z :: poly_mul t q)
  end.

(* A simple record defining what an arbitrary Ring looks like *)
Record Ring : Type := mkRing {
  R : Type;
  Rzero : R;
  Rone : R;
  Radd : R -> R -> R;
  Rmul : R -> R -> R;
  Ropp : R -> R;  (* Negation *)
   (* 1. Additive Identity *)
  Radd_0_l : forall x : R, Radd Rzero x = x;
  
  (* 2. Additive Commutativity *)
  Radd_comm : forall x y : R, Radd x y = Radd y x;
  
  (* 3. Additive Associativity *)
  Radd_assoc : forall x y z : R, Radd x (Radd y z) = Radd (Radd x y) z;

  (* 4. Multiplicative Identity *)
  Rmul_1_l : forall x : R, Rmul Rone x = x;
  
  (* 5. Multiplicative Commutativity *)
  Rmul_comm : forall x y : R, Rmul x y = Rmul y x;
  
  (* 6. Multiplicative Associativity *)
  Rmul_assoc : forall x y z : R, Rmul x (Rmul y z) = Rmul (Rmul x y) z;

  (* 7. Distributivity *)
  Rdistr_l: forall x y z: R, Rmul (Radd x y) z =
     Radd (Rmul x z) (Rmul y z);

  (* 8. Subtraction Definition *)
  Rsub_def : forall x y : R, Radd x (Ropp y) = Radd x (Ropp y); 

  (* 9. Additive Inverse *)
  Radd_opp_r : forall x : R, Radd x (Ropp x) = Rzero
}.

Variable (my_ring : Ring).

Add Ring my_ring_instance : 
  (mk_rt 
    (Rzero my_ring) 
    (Rone my_ring) 
    (Radd my_ring) 
    (Rmul my_ring) 
    (fun x y => Radd my_ring x (Ropp my_ring y)) (* Subtraction anonymous function *)
    (Ropp my_ring) 
    (eq)
    (Radd_0_l my_ring) 
    (Radd_comm my_ring) 
    (Radd_assoc my_ring)
    (Rmul_1_l my_ring) 
    (Rmul_comm my_ring) 
    (Rmul_assoc my_ring)
    (Rdistr_l my_ring) 
    (fun x y => reflexivity _) (* Subtraction identity proof *)
    (Radd_opp_r my_ring)
  ).

Delimit Scope ring_scope with R.
Bind Scope ring_scope with R.

Notation "0" := (Rzero _) : ring_scope.
Notation "1" := (Rone _) : ring_scope.
Notation "a + b" := (Radd _ a b) : ring_scope.
Notation "a * b" := (Rmul _ a b) : ring_scope.
Notation "- a" := (Ropp _ a) : ring_scope.

(* Convert a positive binary number to the ring *)
Fixpoint from_positive (p : positive) : R my_ring :=
  match p with
  | xI q => (from_positive q) * (1 + 1) + 1
  | xO q => (from_positive q) * (1 + 1)
  | xH   => 1
  end.

Lemma from_positive_succ : forall p, 
  from_positive (Pos.succ p) = (1 + from_positive p)%R.
Proof.
  intros.
  induction p.
  - rewrite <-Pos.add_1_l.
    simpl.
    rewrite IHp.
    ring.
  - rewrite <-Pos.add_1_r.
    simpl.
    rewrite Radd_comm.
    reflexivity.
  - rewrite <-Pos.add_1_r. 
    simpl. 
    ring.
Qed.

Lemma from_pos_add_base: forall (p:positive), from_positive (1 + p) = (1 + (from_positive p))%R .
Proof.
  intros.
  rewrite Pos.add_1_l.
  apply from_positive_succ.
Qed.

Lemma from_pos_mul_base: forall (p:positive), from_positive (1 * p) = (1 * (from_positive p))%R .
Proof.
  intros.
  rewrite Pos.mul_1_l.
  ring.
Qed.

Lemma from_pos_1: from_positive 1 = 1%R.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.  

(* Map any mathematical integer (Z) into the arbitrary ring *)
Definition from_Z (z : Z) : R my_ring :=
  match z with
  | Z0 => 0
  | Zpos p => from_positive p
  | Zneg p => - (from_positive p)
  end.

Lemma eq_preserve : forall (a b c: R my_ring),  (a + c)%R = (b + c)%R -> a = b.
Proof.
  intros.
  apply (f_equal (fun x => (x + - c)%R)) in H.
  ring_simplify in H.
  assumption.
Qed.

Lemma from_positive_add_assoc : forall (p1 p2 : positive),
  from_positive (p1 + p2)%positive = (from_positive p1 + from_positive p2)%R.
Proof.
  intros p1 p2.
  induction p1 using Pos.peano_ind.
  - (* Base Case: p1 = 1 *)
    rewrite from_pos_1.
    apply from_pos_add_base.
  - (* Inductive Step: (p1 + 1) + p2 *)
    (* Here you will see your IHp1 hypothesis! *)
    (* Use ring associativity to rewrite: (p1 + p2) + 1 *)
    rewrite from_positive_succ.
    rewrite <-Pos.add_1_l.
    replace 1%R with (from_positive 1).
    rewrite <- Radd_assoc.
    replace (from_positive p1 + from_positive p2)%R with (from_positive (p1 + p2)).
    rewrite <- from_pos_add_base.
    replace (1%positive + p1 + p2)%positive with (1 + (p1 + p2))%positive.
    ring.
    rewrite <-Pos.add_assoc.
    reflexivity.
    apply from_pos_1.
Qed.

Lemma from_positive_mul_assoc: forall (p1 p2 : positive),
  from_positive (p1 * p2)%positive = (from_positive p1 * from_positive p2)%R.
Proof.
  intros p1 p2.
  induction p1 using Pos.peano_ind.
  - apply from_pos_mul_base.
  - rewrite from_positive_succ. 
    rewrite <-Pos.add_1_l.
    replace ((1+ p1)*p2)%positive with (1*p2 + p1*p2)%positive.
    + rewrite from_positive_add_assoc.
      rewrite IHp1.
      simpl.
      replace ((1 + from_positive p1)*from_positive p2)%R with (1*(from_positive p2) + (from_positive p1)*(from_positive p2))%R.
      ring.
      ring.
    + rewrite <- Pos.mul_add_distr_r; reflexivity.
Qed.      

Lemma from_positive_neg: forall (p q:positive), (q < p)%positive -> from_positive (p - q) = ((from_positive p) + - (from_positive q))%R.
Proof.
  intros.
  pose proof (Pos.sub_add p q H) as Ladd. 
  assert (Hef : from_positive ((p - q) + q) = from_positive p) by (rewrite Ladd; reflexivity).
  rewrite from_positive_add_assoc in Hef. 
  (* this is using ring algebra to subtract on both sides *)
  assert (Hfinal : (from_positive (p - q) + from_positive q + -
  from_positive q)%R = (from_positive p + - from_positive q)%R). { rewrite
    Hef. reflexivity. }
  rewrite <- Hfinal.
  ring.
Qed. 

Lemma from_positive_cases: forall (p p0: positive), from_Z (Z.pos_sub p p0) = (from_positive p + - from_positive p0)%R.
Proof.
  intros.
    destruct (Pos.compare p0 p) eqn:Hcomp. + apply Pos.compare_eq_iff in Hcomp.
    (* Hcomp becomes: p0 = p *) subst p0. rewrite Z.pos_sub_diag. simpl.
      ring.
    + rewrite Pos.compare_lt_iff in Hcomp.
      apply Z.pos_sub_lt in Hcomp as Hcomp2.
      rewrite <-Z.pos_sub_opp.
      rewrite Hcomp2. 
      simpl.
      apply from_positive_neg.
      assumption.     
    + rewrite Pos.compare_gt_iff in Hcomp. 
      apply Z.pos_sub_gt in Hcomp as Hcomp2.
      rewrite <-Z.pos_sub_opp.
      rewrite Hcomp2.
      simpl.
      assert (from_positive (p0 - p) = from_positive p0 + - from_positive p)%R.
      apply from_positive_neg. 
      assumption.
      rewrite H.
      ring.
Qed.

Lemma from_Z_opp: forall (c: Z), (- (from_Z c))%R = from_Z (-c).
Proof.
  intros.
  unfold from_Z.
  intros.
  destruct c.
  - simpl.
    ring.
  - simpl.
    ring.
  - simpl.
    ring.
Qed.
 
Lemma from_Z_mul_assoc:  forall (c1 c2 : Z), 
  from_Z (c1 * c2) = (from_Z c1 * from_Z c2)%R.
Proof.
  intros c1 c2.
  destruct c1; destruct c2; simpl.
  - ring.
  - ring.
  - ring.
  - ring.
  - apply from_positive_mul_assoc.  
  - rewrite from_positive_mul_assoc; ring.
  - ring.
  - rewrite from_positive_mul_assoc; ring.
  - rewrite from_positive_mul_assoc; ring.
Qed.

Lemma from_Z_add_assoc : forall (c1 c2 : Z), 
  from_Z (c1 + c2) = (from_Z c1 + from_Z c2)%R.
Proof.
  intros c1 c2.
  destruct c1; destruct c2; simpl.
  - (* Case 1: 0 + 0 *)
    (* Reduces to 0 = 0 + 0, which holds by ring properties *)
    ring.
  - (* Case 2: 0 + Zpos *)
    ring.
  - (* Case 3: 0 + Zneg *)
    ring.
  - (* Case 4: Zpos + 0 *)
    ring.
  - (* Case 5: Zpos p + Zpos p0 *)
    (* This reduces directly to your helper lemma! *)
    apply from_positive_add_assoc.
  - (* Case 6: Zpos p + Zneg p0 *)
    apply from_positive_cases. 
  - ring. 
  - rewrite from_positive_cases.
    ring. 
  - assert ((from_positive (p + p0))%R = (from_positive p + from_positive p0)%R).
    { rewrite from_positive_add_assoc. reflexivity.  }
    { rewrite from_positive_add_assoc; ring. }
Qed.

(** 2. Defining Polynomial Evaluation at an arbitrary Ring element r **)
Fixpoint eval_poly (p : poly_Z) (r : R my_ring) : R my_ring :=
  match p with
  | [] => 0
  | c :: tail => (from_Z c) + r * (eval_poly tail r)
  end.

Inductive is_zero_poly: poly_Z -> Prop :=
  | zero_nil: is_zero_poly []
  | zero_cons: forall p, is_zero_poly p -> is_zero_poly (0 :: p)%Z.

Inductive poly_eq: poly_Z -> poly_Z -> Prop :=
  | eq_nil : poly_eq [] []
  | eq_cons : forall n p1 p2, poly_eq p1 p2 -> poly_eq (n::p1) (n::p2)
  | eq_drop_left : forall p1 p2, is_zero_poly p1 -> poly_eq [] p2 -> poly_eq p1 p2
  | eq_drop_right : forall p1 p2, is_zero_poly p2 -> poly_eq p1 [] -> poly_eq p1 p2.

Notation "p1 ~ p2" := (poly_eq p1 p2).

Lemma poly_eq_refl : forall p, p ~p.
Proof.
   induction p.
   - apply eq_nil.
   - apply eq_cons.
     exact IHp.
Qed.

Lemma poly_eq_sym : forall p1 p2, p1 ~ p2 -> p2 ~ p1.
Proof.
  intros p1 p2 H.
  induction H.
  - (* Case eq_nil: [] ~ [] *)
    apply eq_nil.
  - (* Case eq_cons: (n :: p1) ~ (n :: p2) *)
    apply eq_cons.
    exact IHpoly_eq.
  - (* Case eq_drop_left: p1 ~ p2 where is_zero_poly p1 and [] ~ p2 *)
    (* IHpoly_eq gives us p2 ~ [] *)
    apply eq_drop_right; assumption.
  - (* Case eq_drop_right: p1 ~ p2 where is_zero_poly p2 and p1 ~ [] *)
    (* IHpoly_eq gives us [] ~ p1 *)
    apply eq_drop_left; assumption.
Qed.

Lemma zero_poly_is_nil : forall (p: poly_Z), is_zero_poly p -> p ~ [].
Proof.
  intros p H.
  apply eq_drop_right.
  - apply zero_nil. 
  - apply eq_drop_left.
    + exact H.
    + apply eq_nil.  
Qed.

Fixpoint strip_zeros (p : poly_Z) : poly_Z :=
  match p with
  | [] => []
  | c :: tail =>
      let tail' := strip_zeros tail in
      if (c =? 0)%Z then
        match tail' with
        | [] => []
        | _ => c :: tail'
        end
      else c :: tail'
  end.

Lemma strip_zero_poly : forall p, is_zero_poly p -> strip_zeros p = [].
Proof.
  intros p H. induction H; simpl; [reflexivity |].
  rewrite IHis_zero_poly. simpl.
  (* Z.eqb_refl simplifies (0 =? 0)%Z to true *)
  reflexivity.
Qed.

Lemma poly_eq_nil_is_zero : forall p, p ~ [] -> is_zero_poly p.
Proof.
  intros p H.
  (* We remember [] to safely invert the custom equivalence relation *)
  remember [] as nil_poly eqn:Heq.
  induction H; subst; try discriminate.
  - apply zero_nil.
  - exact H. 
  - apply IHpoly_eq.
    reflexivity.
Qed.

Lemma drop_nil_zero_poly : forall p, strip_zeros p = [] -> is_zero_poly p.
Proof.
  induction p as [|c tail IH]; intros H; simpl in H.
  - apply zero_nil.
  - remember (strip_zeros tail) as tail' eqn:Heq.
    destruct tail'.
    + destruct (Z.eqb_spec c 0).
      * rewrite e; apply zero_cons. apply IH. exact H.
      * discriminate H. 
    +  destruct (Z.eqb_spec c 0). 
      * rewrite e in H.
        discriminate H.
      * discriminate H. 
Qed.

Lemma poly_eq_iff_drop_eq : forall p1 p2, poly_eq p1 p2 <-> strip_zeros p1 = strip_zeros p2.
Proof.
  split; intros H.
  - induction H.
    + reflexivity.
    + simpl. rewrite IHpoly_eq. reflexivity.
    + apply strip_zero_poly in H. rewrite H. exact IHpoly_eq.
    + apply strip_zero_poly in H. 
       rewrite H. rewrite IHpoly_eq.
       apply strip_zero_poly.
       apply poly_eq_nil_is_zero.
       apply eq_nil.
  - generalize dependent p2.
    induction p1 as [|c1 t1 IH1]; intros p2 H.
    + simpl in H. symmetry in H. apply drop_nil_zero_poly in H.
      apply eq_drop_right; [exact H | apply eq_nil].
    + simpl in H. remember (strip_zeros t1) as dt1 eqn:Heq1.
      destruct p2 as [|c2 t2].
      * simpl in H. apply eq_drop_right.
        apply poly_eq_nil_is_zero.
        apply eq_nil.
        rewrite Heq1 in H.  
        apply eq_drop_left.
        (* Subgoal 1: is_zero_poly (c1 :: t1) *)
        apply drop_nil_zero_poly.
        simpl. 
        exact H.
       (* Subgoal 2: [] ~ [] *)
        apply eq_nil. 

      * simpl in H. remember (strip_zeros t2) as dt2 eqn:Heq2.
        destruct dt1; destruct dt2.
        { destruct (Z.eqb_spec c1 0); destruct (Z.eqb_spec c2 0); subst; inversion H; subst.
          - apply eq_drop_left; [apply zero_cons, drop_nil_zero_poly; apply symmetry in Heq1; exact Heq1|].
            apply eq_drop_right; [apply zero_cons, drop_nil_zero_poly; apply symmetry in Heq2; exact Heq2|].
            apply eq_nil.
          - apply eq_cons.
            apply eq_drop_left.
            apply drop_nil_zero_poly.
            apply symmetry in Heq1.
            exact Heq1.
            apply eq_drop_right.
            apply drop_nil_zero_poly.
            symmetry; exact Heq2. 
            apply eq_nil.
        }
        simpl in H. remember (strip_zeros t2) as dt3 eqn:Heq3.
        { destruct (Z.eqb_spec c1 0); destruct (Z.eqb_spec c2 0); subst; inversion H; subst.  }
        { destruct (Z.eqb_spec c1 0); destruct (Z.eqb_spec c2 0); subst; inversion H; subst.  }
         destruct (Z.eqb_spec c1 0); destruct (Z.eqb_spec c2 0); subst; inversion H; subst.  
         apply eq_cons.
         specialize (IH1 t2). 
         specialize (IH1 Heq2). 
         exact IH1.
         apply eq_cons.
         specialize (IH1 t2). 
         specialize (IH1 Heq2).
         exact IH1.
         apply eq_cons.
         specialize (IH1 t2). 
         specialize (IH1 Heq2).
         exact IH1.
         apply eq_cons.
         specialize (IH1 t2). 
         specialize (IH1 Heq2).
         exact IH1.
Qed.

Lemma poly_eq_trans : forall p1 p2 p3, poly_eq p1 p2 -> poly_eq p2 p3 -> poly_eq p1 p3.
Proof.
  intros p1 p2 p3 H12 H23.
  apply poly_eq_iff_drop_eq in H12.
  apply poly_eq_iff_drop_eq in H23.
  apply poly_eq_iff_drop_eq.
  (* Goal: strip_zeros p1 = strip_zeros p3 *)
  rewrite H12.
  exact H23.
Qed.

Lemma eval_zero_poly : forall p r,
  is_zero_poly p -> eval_poly p r = 0%R.
Proof.
  intros p r H.
  induction H.
  - (* Case zero_nil *)
    reflexivity.
  - (* Case zero_cons *)
    simpl.
    rewrite IHis_zero_poly.
    ring.
    (* At this stage, your goal is: from_Z 0 + r * 0 = 0 *)
    (* Use your ring tactics or axioms here, e.g., ring or: *)
    (* rewrite (ring_mult_0_r), (ring_add_0_r), (from_Z_0)... *)
Qed.

Instance eval_poly_proper : Proper (poly_eq ==> eq ==> eq) eval_poly.
Proof.
  intros p1 p2 Hp r1 r2 Hr.
  subst r2. (* Replace r2 with r1 everywhere *)
  induction Hp.
  - (* Case eq_nil: [] ~ [] *)
    reflexivity.
  - (* Case eq_cons: (n::p1) ~ (n::p2) *)
    simpl.
    rewrite IHHp.
    reflexivity.
  - (* Case eq_drop_left: p1 ~ p2 where is_zero_poly p1 and [] ~ p2 *)
    (* IHHp gives us: eval_poly [] r1 = eval_poly p2 r1 *)
    simpl in IHHp. (* eval_poly [] r1 is 0, so 0 = eval_poly p2 r1 *)
    rewrite <- IHHp.
    (* Goal becomes: eval_poly p1 r1 = 0 *)
    apply eval_zero_poly; assumption.
  - (* Case eq_drop_right: p1 ~ p2 where is_zero_poly p2 and p1 ~ [] *)
    (* IHHp gives us: eval_poly p1 r1 = eval_poly [] r1 *)
    simpl in IHHp. (* eval_poly [] r1 is 0, so eval_poly p1 r1 = 0 *)
    rewrite IHHp.
    (* Goal becomes: 0 = eval_poly p2 r1 *)
    symmetry.
    apply eval_zero_poly; assumption.
Qed.

Instance cons_poly_proper : Proper (eq ==> poly_eq ==> poly_eq) cons.
Proof.
  intros n1 n2 Hn p1 p2 Hp.
  subst n2. (* Reduces goal to: (n1 :: p1) ~ (n1 :: p2) *)
  apply eq_cons.
  exact Hp.
Qed.

(* 2. Declare the Equivalence Instance *)
Instance poly_eq_equiv : Equivalence poly_eq.
Proof.
  split.
  - exact poly_eq_refl.
  - exact poly_eq_sym.
  - exact poly_eq_trans.
Defined.

(** 3. Defining what it means to be a Ring Homomorphism **)
Record IsRingHomomorphism (f : poly_Z -> R my_ring) : Prop := {
  hom_add  : forall p q, f (poly_add p q) = (f p + f q)%R; (* Needs polynomial addition *)
  hom_mul  : forall p q, f (poly_mul p q) = (f p * f q)%R; (* Needs polynomial multiplication *)
  hom_zero : f [] = 0%R;
  hom_one  : f [1%Z] = 1%R
}.

Lemma Radd_0_r: forall (r : Ring) (x : R r), x = (x + 0)%R.
Proof.
  intros.
  symmetry.
  rewrite Radd_comm.
  rewrite Radd_0_l.
  reflexivity.
Qed.

Lemma Rdistr_r : forall (r: Ring) (x y z : R r), (x * (y + z))%R = ((x * y) + (x * z))%R.
Proof.
  intros.
  rewrite Rmul_comm.
  rewrite Rdistr_l. 
  rewrite Rmul_comm.
  rewrite (Rmul_comm r z x).
  reflexivity.
Qed.

(** 4. Constructing the Homomorphism r **)
Definition ev (r : R my_ring) : poly_Z -> R my_ring := fun p => eval_poly p r.

Lemma ev_add_preservation : forall (r : R my_ring) (p q : poly_Z), 
  ev r (poly_add p q) = (ev r p + ev r q)%R.
Proof.
  intros r p.
  (* 1. Perform induction on the first polynomial p *)
  induction p as [| c1 t1 IHp].
  - (* Base Case: p is empty [] *)
    intros q. simpl.
    (* ev r [] is 0, and 0 + ev r q is just ev r q *)
    rewrite Radd_0_l.
    reflexivity.
  - (* Inductive Step: p is (c1 :: t1) *)
    intros q.
    (* 2. Destruct q because poly_add changes behavior if q is empty *)
    destruct q as [| c2 t2].
    + (* Subcase: q is empty [] *)
      simpl. 
      (* ev r [] is 0, and ev r (c1 :: t1) + 0 is just itself *)
      rewrite <-Radd_0_r. 
      reflexivity.
    + (* Subcase: q is (c2 :: t2) *)
      (* Unfold 'ev' and 'poly_add' by one evaluation layer *)
      simpl.
      
      rewrite IHp.
      (* Step C: Distribute the 'r *' over the addition using real number arithmetic *)
      rewrite Rdistr_r.
      rewrite from_Z_add_assoc.
      ring. 
      (* Step D: Rearrange the terms using associativity and commutativity *)
      (* We have: (I c1 + I c2) + (r * ev t1 + r * ev t2) *)
      (* We want: (I c1 + r * ev t1) + (I c2 + r * ev t2) *)
Qed.

Lemma eval_poly_decomp : forall (r:R my_ring) (c:Z) (q: poly_Z),
  eval_poly (c::q) r = (from_Z c + r * eval_poly q r)%R.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma poly_decomp: forall (c: Z) (q:poly_Z), (c::q) ~ (poly_add [c] (0::q))%Z.
Proof.
  intros.
  unfold poly_add.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma eval_decomp : forall (r: R my_ring) (c:Z) (q: poly_Z),
  ev r (c::q) = (from_Z c + r * ev r q)%R.
Proof.
  intros. 
  unfold ev.
  apply eval_poly_decomp.
Qed.

Lemma eval_vec_identity: forall (r: R my_ring), ev r [0%Z; 1%Z] = r.
Proof.
 intros.
 rewrite eval_decomp. 
 simpl.
 ring.
Qed.

Lemma poly_scalar_decomp : forall (a c: Z) (q: poly_Z),
  ((c * a)%Z :: poly_scalar_mul c q) ~ (poly_scalar_mul c (a :: q)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma scalar_mul_eq0 : forall (r : R my_ring) (c:Z) (q: poly_Z), 
  ev r (poly_scalar_mul c q) = (from_Z c * (ev r q))%R.
Proof.
  intros r c q.
  simpl.
  unfold ev in *.
  induction q as [| c1 t1 IHq].
  - simpl.
    ring.
  - rewrite eval_poly_decomp.
    rewrite <-poly_scalar_decomp.
    rewrite eval_poly_decomp.
    rewrite IHq.
    rewrite from_Z_mul_assoc.
    ring.
Qed.

Lemma ev_mul_preservation : forall (r : R my_ring) (p q : poly_Z), 
  ev r (poly_mul p q) = (ev r p * ev r q)%R.
Proof.
  intros r p.
  induction p as [|c1 t1 IHp].
  - intros q.
    simpl.
    ring.
  - intros q.
    simpl.
    rewrite ev_add_preservation.
    rewrite scalar_mul_eq0.
    simpl.
    rewrite IHp.
    ring.
Qed.
 
(** Theorem: For any arbitrary Ring r, the evaluation function is a valid homomorphism **)
Lemma ev_is_homomorphism : forall (r : R my_ring), 
  IsRingHomomorphism (ev r).
Proof.
  intros.
  constructor. 
  - apply ev_add_preservation.
  - apply ev_mul_preservation.   
  - simpl; reflexivity.
  - simpl; ring.
Qed.

Lemma Rmul_1_r: forall (r : Ring) (x : R r), (x * 1 )%R = x.
Proof.
  intros.
  rewrite Rmul_comm.
  apply Rmul_1_l.
Qed.

Lemma poly_add_ids: forall (a b:Z), poly_add [a%Z] [b%Z] = [(a+b)%Z].
Proof.
  intros.
  unfold poly_add.
  simpl.
  reflexivity.
Qed.

Lemma homo_iter: forall (a:Z) (g: poly_Z -> R my_ring), IsRingHomomorphism g -> g [(a + 1)%Z] = ( g[a] + g[1%Z] )%R.
Proof.
  intros.
  destruct H.
  specialize (hom_add0 [(a)%Z] [1%Z]).
  rewrite poly_add_ids in hom_add0.
  assumption.
Qed.  

Lemma homo_const_iter: forall (a:Z) (g: poly_Z -> R my_ring), IsRingHomomorphism g -> g [(a + 1)%Z] = ( from_Z (a + 1) * g[1%Z] )%R.
Proof.
  intros.
  pose proof H as H0.
  destruct H.
  rewrite hom_one0.
  specialize (hom_add0 [(a)%Z] [1%Z]).

  rewrite Rmul_1_r. 
  rewrite poly_add_ids in hom_add0.

  (* Step 1: Initialize the induction for a > 0 *)

  induction a using Z.peano_ind.
  - (* Base Case: a = 1 *)
    (* The goal becomes: g [1%Z] = from_Z 1 *)
    simpl.
    apply hom_one0.
   - (* Inductive Step: Assume it holds for 'x', prove for 'x + 1' *)
     change (Z.succ a) with (a + 1)%Z.
     change (Z.succ a) with (a+ 1)%Z in hom_add0.
     rewrite hom_add0.
     rewrite hom_one0.
     replace (a + 1 + 1)%Z with ((a + 1) + 1)%Z.
     rewrite IHa.
     + rewrite from_Z_add_assoc.
       rewrite from_Z_add_assoc.       
       rewrite from_Z_add_assoc.       
       reflexivity.
     + apply homo_iter. 
       assumption. 
     + reflexivity.
   - change (Z.pred a) with (a - 1)%Z.
     change (Z.pred a) with (a - 1)%Z in hom_add0.
     replace (from_Z (a - 1 + 1)) with (from_Z (a + 1) + - from_Z 1)%R.
     replace (a - 1 + 1)%Z with a.
     rewrite <-IHa.
     + apply (eq_preserve _ _ (from_Z 1)%R ).
       simpl.
       ring_simplify.
       symmetry.
       rewrite <- hom_one0.
       apply homo_iter.
       assumption.
     + apply homo_iter.
       assumption.
     + ring_simplify.
       reflexivity.
     + ring_simplify.
       rewrite from_Z_add_assoc.
       rewrite from_Z_add_assoc.
       replace (a - 1)%Z with (a + - 1%Z)%Z.
       rewrite from_Z_add_assoc.
       rewrite <-from_Z_opp.
       ring.
       ring.
Qed.

Lemma poly_scalar_mul_0: forall (a:Z) (p:poly_Z), (poly_scalar_mul 0%Z (a::p)) = (0%Z :: poly_scalar_mul 0 p).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma poly_scalar_mul_1: forall (a: Z) (p: poly_Z), poly_scalar_mul 1%Z (a::p) = (1 * a)%Z::poly_scalar_mul 1%Z p.
Proof.
  intros.
  reflexivity.
Qed.

Lemma poly_scalar_mul_1_eq: forall (p: poly_Z), (poly_scalar_mul 1%Z p) =  p.
Proof.
  intros.
  induction p.
  - simpl.
    reflexivity.
  - rewrite poly_scalar_mul_1.
    rewrite Z.mul_1_l.
    rewrite IHp. 
    reflexivity.
Qed.

Lemma poly_scalar_mul_0_eq: forall (p:poly_Z), (poly_scalar_mul 0%Z p) ~ [].
Proof.
  intros.
  induction p.
  - reflexivity. 
  - rewrite poly_scalar_mul_0. 
    rewrite IHp.
    apply eq_drop_left.
    + apply zero_cons. 
      apply zero_nil.
    + reflexivity.
Qed.

Lemma poly_add_zero: forall (p:poly_Z), (poly_add [] p) ~ p.
Proof.
 intros.
 induction p.
 - unfold poly_add.
   reflexivity.
 - simpl.
   reflexivity.
Qed.   

Lemma poly_add_decomp2: forall (a: Z) (p: poly_Z), poly_add [0%Z] (a :: p) = poly_add [a] (0%Z :: p).  
Proof.
  intros.
  unfold poly_add.
  rewrite Z.add_0_r. 
  rewrite Z.add_0_l. 
  reflexivity.
Qed.

Lemma poly_add_decomp: forall (a: Z) (p: poly_Z), (poly_add [a] (0%Z :: p)) ~ (a::p).  
Proof.
  intros.
  unfold poly_add.
  rewrite Z.add_0_r.
  reflexivity.
Qed. 

Parameter g_invariance : forall (r : R my_ring) (g : R my_ring -> poly_Z -> R my_ring) (p : poly_Z),
  g r p = g r (strip_zeros p).

Instance g_proper (r : R my_ring) (g : R my_ring -> poly_Z -> R my_ring) 
  : Proper (poly_eq ==> eq) (g r).
Proof.
  intros p1 p2 Hp.
  rewrite poly_eq_iff_drop_eq in Hp. 
  rewrite g_invariance.
  rewrite Hp.
  rewrite <- g_invariance.
  reflexivity.
Qed.

Parameter poly_add_proper : Proper (poly_eq ==> poly_eq ==> poly_eq) poly_add.
 
Existing Instance poly_add_proper.

Lemma poly_mul_decomp: forall (p: poly_Z), (0%Z::p) ~ (poly_mul [0%Z;1%Z] p). 
Proof.
  intros.
  induction p.
  - unfold poly_mul.
    apply eq_drop_left. 
    apply zero_cons.
    apply zero_nil.
    replace (poly_scalar_mul 0 [])%Z with (@nil Z).
    replace (poly_scalar_mul 1 []) with (@nil Z).
    simpl.
    apply eq_drop_right.
    apply zero_cons. 
    apply zero_cons. 
    apply zero_nil.
    reflexivity.
    symmetry.
    simpl. 
    reflexivity.
    simpl.
    reflexivity.
  - unfold poly_mul.
    rewrite poly_scalar_mul_0_eq.
    rewrite poly_scalar_mul_1_eq.
    rewrite poly_add_zero. 
    replace (poly_add (a:: p) [0%Z]) with (a :: p).
    simpl.
    reflexivity.
    simpl.
    rewrite poly_add_comm.
    simpl.
    rewrite Z.add_0_r.
    reflexivity.
Qed.

Lemma ev_is_unique_homo : forall (p: poly_Z) (r: R my_ring) (g: R my_ring -> poly_Z -> R my_ring), 
  IsRingHomomorphism (g r) /\ g r [0%Z; 1%Z] = r -> (g r p = ev r p).
Proof.
  intros p r g [H_hom H_char].
  (* Step 1: Use functional extensionality to change 'g = ev r' into an element-wise equality *)
  
  (* Step 2: Use induction on the structure of the polynomial 'p' *)
  induction p.
  - (* Case 1: p is the zero polynomial *)
    rewrite (hom_zero (g r) H_hom).
    reflexivity.
    
  - (* Case 2: p is a constant polynomial 'c' *)
    (* Ring homomorphisms map the identity 1 to 1, forcing integer maps to match *)
    rewrite eval_decomp.
    pose proof H_hom as H_hom2.
    destruct H_hom as [hom_add0 hom_mul0 hom_zero0 hom_one0].
    rewrite <-IHp.
    specialize (hom_add0 [a] (0::p)%Z).
    pose proof hom_add0 as H_h.
    rewrite (poly_add_decomp a p) in hom_add0.
    rewrite poly_mul_decomp in hom_add0.
    rewrite hom_mul0 in hom_add0.
    rewrite IHp.
    replace a with ((a - 1)%Z + 1)%Z in hom_add0.
    rewrite homo_const_iter in hom_add0.
    replace (a - 1 + 1)%Z with a in hom_add0.
    rewrite hom_one0 in hom_add0.
    ring_simplify in hom_add0.
    rewrite hom_add0.
    rewrite H_char.
    rewrite IHp.
    reflexivity.
    + ring.
    + assumption.   
    + ring.
Qed.
  
End Evaluation.
