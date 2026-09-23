From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Arith Lia.

Record Finnat (n : nat) : Set := mkFinnat {
  finnat_val :> nat;
  finnat_lt : finnat_val < n
}.
Arguments mkFinnat {n}.
Arguments finnat_val {n}.
Arguments finnat_lt {n}.

Lemma Finnat_ext {n : nat} (a b : Finnat n) :
  finnat_val a = finnat_val b -> a = b.
Proof.
  destruct a as [va Ha], b as [vb Hb]; simpl.
  intros ->. f_equal. apply Peano_dec.le_unique.
Qed.

Definition Finnat_eq_dec {n : nat} (a b : Finnat n) : {a = b} + {a <> b}.
Proof.
  destruct (Nat.eq_dec (finnat_val a) (finnat_val b)) as [H | H].
  - left. now apply Finnat_ext.
  - right. intros He. apply H. now rewrite He.
Defined.

Definition fin0 {n : nat} : Finnat (S n) :=
  {| finnat_val := 0; finnat_lt := Nat.lt_0_succ n |}.

Inductive direction : Set := L | R.

(* Alphabet: Finnat (2 + k).  Value 0 is blank, and 1 is the default score state. *)
Definition symbol (k : nat) : Set := Finnat (S (S k)).
Definition blank {k : nat} : symbol k := fin0.
Definition one   {k : nat} : symbol k :=
  {| finnat_val := 1; finnat_lt := le_n_S 1 (S k) (le_n_S 0 k (Nat.le_0_l k)) |}.

Lemma blank_neq_one {k : nat} : @blank k <> @one k .
Proof.
  intros H. discriminate.
Qed.

Record TM (k : nat) : Set := mkTM {
  number_of_states : nat;
  transition_function :
    Finnat number_of_states -> symbol k ->
    option (Finnat number_of_states * symbol k * direction);
  start_state : Finnat number_of_states
}.
Arguments number_of_states {k}.
Arguments transition_function {k}.
Arguments start_state {k}.

Definition state {k : nat} (tm : TM k) : Set := Finnat (number_of_states tm).

Record Config {k : nat} (tm : TM k) : Set := makeConfig {
  cur_state : state tm;
  tape_left : list (symbol k);   (* cell at head-1 is the list head *)
  current_symbol : symbol k;
  tape_right : list (symbol k)   (* cell at head+1 is the list head *)
}.
Arguments makeConfig {k tm}.
Arguments cur_state {k tm}.
Arguments tape_left {k tm}.
Arguments current_symbol {k tm}.
Arguments tape_right {k tm}.

Definition init {k : nat} (tm : TM k) : Config tm :=
  makeConfig (start_state tm) [] blank [].

Definition halts {k : nat} (tm : TM k) (c : Config tm) : bool :=
  match transition_function tm (cur_state c) (current_symbol c) with
  | None => true
  | Some _ => false
  end.

Definition step {k : nat} (tm : TM k) (c : Config tm) : option (Config tm) :=
  match transition_function tm (cur_state c) (current_symbol c) with
  | None => None
  | Some (s', sym', d) =>
      match d with
      | L =>
          let new_current := match tape_left c with
                             | [] => blank
                             | h :: _ => h
                             end in
          let new_left := match tape_left c with
                          | [] => []
                          | _ :: t => t
                          end in
          Some (makeConfig s' new_left new_current (sym' :: tape_right c))
      | R =>
          let new_current := match tape_right c with
                             | [] => blank
                             | h :: _ => h
                             end in
          let new_right := match tape_right c with
                           | [] => []
                           | _ :: t => t
                           end in
          Some (makeConfig s' (sym' :: tape_left c) new_current new_right)
      end
  end.

Fixpoint run_steps {k : nat} (tm : TM k) (c : Config tm) (n : nat)
  : option (Config tm) :=
  match n with
  | O => Some c
  | S n' => match run_steps tm c n' with
            | Some c' => step tm c'
            | None => None
            end
  end.

(* tm, started in c1, is in configuration c2 after n steps *)
Definition run {k : nat} (tm : TM k) (c1 c2 : Config tm) (n : nat) : Prop :=
  run_steps tm c1 n = Some c2.

Lemma run_steps_deterministic {k : nat} (tm : TM k) (c c1 c2 : Config tm) (n : nat) :
  run_steps tm c n = Some c1 -> run_steps tm c n = Some c2 -> c1 = c2.
Proof. congruence. Qed.

Lemma halts_step {k : nat} (tm : TM k) (c : Config tm) :
  halts tm c = true -> step tm c = None.
Proof.
  unfold halts, step.
  destruct (transition_function tm (cur_state c) (current_symbol c))
    as [[[s' sym'] d]|]. discriminate.  reflexivity.
Qed.
(* Addition of steps is associative. *)
Lemma run_steps_plus {k : nat} (tm : TM k) (c : Config tm) (a b : nat) :
  run_steps tm c (a + b) =
  match run_steps tm c b with
  | Some c' => run_steps tm c' a
  | None => None
  end.
Proof.
  induction a as [|a IH]; simpl.
  - destruct (run_steps tm c b); reflexivity.
  - rewrite IH. destruct (run_steps tm c b) as [c'|]; reflexivity.
Qed.

(* Addition of steps after halting is idempotent: f∘f=f *)
Lemma run_steps_halted {k : nat} (tm : TM k) (c : Config tm) (n : nat) :
  halts tm c = true -> run_steps tm c (S n) = None.
Proof.
  intros H. induction n as [|n IH]; simpl.
  - rewrite halts_step. reflexivity. rewrite H. reflexivity.
  - simpl in IH.  rewrite IH. reflexivity.
 Qed.

(*For a given tape configuration, halting state and tape is unique. *)
Lemma halting_unique {k : nat} (tm : TM k) (c : Config tm)
    (n1 n2 : nat) (c1 c2 : Config tm) :
  run_steps tm c n1 = Some c1 -> halts tm c1 = true ->
  run_steps tm c n2 = Some c2 -> halts tm c2 = true ->
  c1 = c2.
Proof.
  intros Hrun1 Hhalt1 Hrun2 Hhalt2.
  (* trichotomy destructs c1=c2 to cases <, >, = *)
  destruct (Nat.lt_trichotomy n1 n2) as [Hlt | [Heq | Hgt]].
  - (* n1 < n2 *)
    exfalso.
    assert (Hsplit : n2 = (n2 - n1) + n1) by lia.
    rewrite Hsplit in Hrun2.
    rewrite run_steps_plus in Hrun2.
    rewrite Hrun1 in Hrun2.
    destruct (n2 - n1) as [|m].
    + lia.
    + rewrite run_steps_halted in Hrun2 by exact Hhalt1.
      discriminate.
  - (* n1 = n2 *)
    subst.
    rewrite Hrun1 in Hrun2. injection Hrun2 as ->.  reflexivity.
  - (* n2 < n1 *)
    exfalso.
    assert (Hsplit : n1 = (n1 - n2) + n2) by lia.
    rewrite Hsplit in Hrun1.
    rewrite run_steps_plus in Hrun1.
    rewrite Hrun2 in Hrun1.
    destruct (n1 - n2) as [|m].
    + lia.
    + rewrite run_steps_halted in Hrun1 by exact  Hhalt2.
      discriminate.
Qed.


Definition is_non_blank {k : nat} (s : symbol k) : bool :=
  if Finnat_eq_dec s blank then false else true.

Fixpoint count_non_blank_list {k : nat} (l : list (symbol k)) : nat :=
  match l with
  | [] => O
  | h :: t => if is_non_blank h
              then S (count_non_blank_list t)
              else count_non_blank_list t
  end.

Definition count_non_blank {k : nat} {tm : TM k} (c : Config tm) : nat :=
  count_non_blank_list (tape_left c) +
  (if is_non_blank (current_symbol c) then 1 else 0) +
  count_non_blank_list (tape_right c).

(* tm, started on the blank tape, halts with m non-blank symbols. *)
Definition BB_score {k : nat} (tm : TM k) (m : nat) : Prop :=
  exists (n : nat) (c : Config tm),
    run_steps tm (init tm) n = Some c /\
    halts tm c = true /\
    count_non_blank c = m.

(* BB n m: some n-state 2-symbol machine achieves m, and none exceeds it. *)
Definition BB (n m : nat) : Prop :=
  (exists tm : TM 0,
      number_of_states tm = n /\ BB_score tm m)
  /\
  (forall (tm : TM 0) (m' : nat),
      number_of_states tm = n -> BB_score tm m' -> m' <= m).

Lemma BB_functional (n m1 m2 : nat) :
  BB n m1 -> BB n m2 -> m1 = m2.
Proof.
  intros [(tm1 & Hstates1 & Hscore1) Hmax1]
         [(tm2 & Hstates2 & Hscore2) Hmax2].
  specialize (Hmax2 tm1 m1 Hstates1 Hscore1). (* m1 <= m2 *)
  specialize (Hmax1 tm2 m2 Hstates2 Hscore2). (* m2 <= m1 *)
  lia. 
Qed.
(* Partial is not necessarily defined for all elements in the domain, e.g. f(n)=m iff m^2 = n, m ∈ N , n ∈ Z *)
(* A partial function is not necessarily total. Busy Beaver is a total function. *)
Record partfun (A B : Type) : Type := mkPartfun {
  funrel :> A -> B -> Prop;
  (* A funrel must be deterministic: f(x) = y1 -> f(x) = y2  -> y1 = y2 *)
  functional : forall x y1 y2, funrel x y1 -> funrel x y2 -> y1 = y2
}.
Arguments funrel {A B}.
Arguments functional {A B}.
(* Every total function is also a partial function. *)
Definition partfun_of_fun {A B : Type} (f : A -> B) : partfun A B.
Proof.
  refine {| funrel := fun x y => f x = y |}.
  intros x y1 y2 H1 H2. subst. reflexivity. 
Defined.
(* equality of partial functions *)
Definition partfun_eq {A B : Type} (f1 f2 : partfun A B) : Prop :=
  forall x y, funrel f1 x y <-> funrel f2 x y.

Definition BB_pf : partfun nat nat :=
  {| funrel := BB; functional := BB_functional |}.

  (* Value of BB is encoding where head points the leftmost of the tape and unary marks are lined up to the right *)
Definition encoding_config {k : nat} (tm : TM k) (n : nat) : Config tm :=
  match n with
  | O => init tm
  | S n' => makeConfig (start_state tm) [] one (repeat one n')
  end.

(* l consists of n marks followed by blanks. *)
Definition encodes_list {k : nat} (l : list (symbol k)) (n : nat) : Prop :=
  exists prefix suffix,
    l = prefix ++ suffix /\
    length prefix = n /\
    Forall (fun x => x = one) prefix /\
    Forall (fun x => x = blank) suffix.

Definition encodes {k : nat} {tm : TM k} (c : Config tm) (n : nat) : Prop :=
  Forall (fun x => x = blank) (tape_left c) /\
  encodes_list (current_symbol c :: tape_right c) n.

(* A list of marks that is also a list of blanks is empty. *)
Lemma all_one_all_blank_nil {k : nat} (l : list (symbol k)) :
  Forall (fun x => x = one) l -> Forall (fun x => x = blank) l -> l = [].
Proof.
  intros H1 H2. destruct l as [|h t]. reflexivity.
  inversion H1. inversion H2. subst.
  exfalso. apply (@blank_neq_one k). congruence.
Qed.

Lemma encodes_list_functional {k : nat} (l : list (symbol k)) (n1 n2 : nat) :
  encodes_list l n1 -> encodes_list l n2 -> n1 = n2.
Proof.
  intros (p1 & s1 & Hl1 & Hlen1 & Hone1 & Hblank1)
         (p2 & s2 & Hl2 & Hlen2 & Hone2 & Hblank2).
  subst n1 n2.
  assert (Hpp : p1 ++ s1 = p2 ++ s2) by congruence.
  destruct (app_eq_app _ _ _ _ Hpp) as (m & [[Hp Hs] | [Hp Hs]]); subst.
  - (* p1 = p2 ++ m, s2 = m ++ s1 : m is all-one and all-blank, so [] *)
    apply Forall_app in Hone1 as [_ Hm1].
    apply Forall_app in Hblank2 as [Hm2 _].
    rewrite (all_one_all_blank_nil m Hm1 Hm2). rewrite app_nil_r. reflexivity.
  - (* p2 = p1 ++ m, s1 = m ++ s2 : symmetric *)
    apply Forall_app in Hone2 as [_ Hm1].
    apply Forall_app in Hblank1 as [Hm2 _].
    rewrite (all_one_all_blank_nil m Hm1 Hm2). rewrite app_nil_r. reflexivity.
Qed.

Lemma encodes_functional {k : nat} {tm : TM k} (c : Config tm) (m1 m2 : nat) :
  encodes c m1 -> encodes c m2 -> m1 = m2.
Proof.
  (* eapply creates existential variable ?l*)
  (*eauto : Implements a Prolog-like resolution procedure to solve the current goal.
   It first tries to solve the goal using the assumption tactic, 
   then it reduces the goal to an atomic one using intros and introduces the newly generated hypotheses as hints.
    Then it looks at the list of tactics associated with the head symbol of the goal and tries to apply one of them. 
  Lower cost tactics are tried before higher-cost tactics. This process is recursively applied to the generated subgoals.*)
  intros [_ H1] [_ H2]. eapply encodes_list_functional. eauto. eauto.
Qed.

(* On input n, tm halts with output m  *)
Definition computes {k : nat} (tm : TM k) (n m : nat) : Prop :=
  exists (steps : nat) (c : Config tm),
    run_steps tm (encoding_config tm n) steps = Some c /\
    halts tm c = true /\
    encodes c m.

Lemma computes_functional {k : nat} (tm : TM k) (n m1 m2 : nat) :
  computes tm n m1 -> computes tm n m2 -> m1 = m2.
Proof.
  (*st1: # of steps for tm1, i.e. n*)
  intros (st1 & c1 & Hr1 & Hh1 & He1) (st2 & c2 & Hr2 & Hh2 & He2).
  assert (c1 = c2). eapply halting_unique. eauto. eauto. eauto. eauto.   subst.
  eapply encodes_functional. eauto. eauto.
Qed.

Definition computes_pf {k : nat} (tm : TM k) : partfun nat nat :=
  {| funrel := computes tm; functional := computes_functional tm |}.
(* A function is computable iff there exists some Turing machine that computes it *)
Definition computable (f : nat -> nat -> Prop) : Prop :=
  exists tm : TM 0,
    forall n m, f n m <-> computes tm n m.

(* left embedding :  s < n1 + n2 *)
Lemma embed_l_lt {n1 : nat} (n2 : nat) (s : Finnat n1) :
  finnat_val s < n1 + n2.
Proof. destruct s. simpl. lia. Qed.

Definition embed_l {n1 : nat} (n2 : nat) (s : Finnat n1) : Finnat (n1 + n2) :=
  {| finnat_val := s; finnat_lt := embed_l_lt n2 s |}.

Lemma embed_r_lt (n1 : nat) {n2 : nat} (s : Finnat n2) :
   n1 + finnat_val s < n1 + n2.
Proof. destruct s. simpl. lia. Qed.

Definition embed_r (n1 : nat) {n2 : nat} (s : Finnat n2) : Finnat (n1 + n2) :=
  {| finnat_val := n1 + s; finnat_lt := embed_r_lt n1 s |}.

Lemma split_lt (n1 n2 v : nat) : v < n1 + n2 -> ~ v < n1 -> v - n1 < n2.
Proof. lia. Qed.

(* Split a state of the combined machine into tm1's side or tm2's side. *)
Definition split_fin (n1 n2 : nat) (s : Finnat (n1 + n2))
  : Finnat n1 + Finnat n2 :=
  match lt_dec s n1 with
  (* if s < n1, s belongs to tm1 *)
  | left H => inl {| finnat_val := s; finnat_lt := H |}
  (* if s >= n1, s belongs to tm2 *)
  | right H => inr {| finnat_val := finnat_val s - n1;
                      finnat_lt := split_lt n1 n2 _ (finnat_lt s) H |}
  end.

Lemma split_fin_embed_l (n1 n2 : nat) (s : Finnat n1) :
  split_fin n1 n2 (embed_l n2 s) = inl s.
Proof.
  unfold split_fin. simpl.
  destruct (lt_dec (finnat_val s) n1).
  - f_equal. apply Finnat_ext. reflexivity.
  - exfalso. destruct s. simpl in *. lia.
Qed.

Lemma split_fin_embed_r (n1 n2 : nat) (s : Finnat n2) :
  split_fin n1 n2 (embed_r n1 s) = inr s.
Proof.
  unfold split_fin. simpl.
  destruct (lt_dec (n1 + finnat_val s) n1) as [H | H].
  - exfalso. lia.
  - f_equal. apply Finnat_ext. simpl. lia.
Qed.

(* M.N: run M; if and when M halts, pass control to N on the same tape.  *)
Definition compose {k : nat} (tm1 tm2 : TM k) : TM k :=
  {| number_of_states := number_of_states tm1 + number_of_states tm2;
     start_state := embed_l (number_of_states tm2) (start_state tm1);
     transition_function := fun s sym =>
       match split_fin _ _ s with
       (*tm1*)
       | inl s1 =>
           match transition_function tm1 s1 sym with
           (* tm1 has a transition *)
           | Some (s1', sym', d) => Some (embed_l (number_of_states tm2) s1', sym', d)
           (* tm1 halts tm2 begins*)
           | None =>
               match transition_function tm2 (start_state tm2) sym with
               (* tm2 has a transition *)
               | Some (s2', sym', d) => Some (embed_r (number_of_states tm1) s2', sym', d)
               (* tm2 has no transition, halts *)
               | None => None
               end
           end
       | inr s2 =>
           match transition_function tm2 s2 sym with
            (* tm2 has a transition *)
           | Some (s2', sym', d) => Some (embed_r (number_of_states tm1) s2', sym', d)
           (* tm2 has no transition, halts *)
           | None => None
           end
       end |}.

Lemma compose_states {k : nat} (tm1 tm2 : TM k) :
  number_of_states (compose tm1 tm2)
  = number_of_states tm1 + number_of_states tm2.
Proof. reflexivity. Qed.

Definition lift_l {k : nat} {tm1 tm2 : TM k} (c : Config tm1)
  : Config (compose tm1 tm2) :=
  makeConfig (tm := compose tm1 tm2)
           (embed_l (number_of_states tm2) (cur_state c))
           (tape_left c) (current_symbol c) (tape_right c).

Definition lift_r {k : nat} {tm1 tm2 : TM k} (c : Config tm2)
  : Config (compose tm1 tm2) :=
  makeConfig (tm := compose tm1 tm2)
           (embed_r (number_of_states tm1) (cur_state c))
           (tape_left c) (current_symbol c) (tape_right c).
