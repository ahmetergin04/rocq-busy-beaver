From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Vectors.Fin.

Inductive direction : Set := L | R.

Record TM : Set := {
  number_of_states : nat;
  state : Set := Fin.t number_of_states;
  number_of_symbols : nat;
  symbol : Set := Fin.t number_of_symbols;
  blank_symbol : symbol;
  transition_function : state -> symbol -> option (state * symbol * direction); 
  start_state : state
}.

Record Tape (tm : TM) : Set := make_tape {
  cur_state : state tm;
  tape_left : list (symbol tm);      
  current_symbol : symbol tm;       
  tape_right : list (symbol tm)     
}.
Arguments make_tape {tm}.
Arguments cur_state {tm}.
Arguments tape_left {tm}.
Arguments current_symbol {tm}.
Arguments tape_right {tm}.


Definition init (tm : TM) : Tape tm :=
  make_tape (start_state tm) [] (blank_symbol tm) [].

Definition halts (tm : TM) (config : Tape tm) : bool :=
  match transition_function tm (cur_state config) (current_symbol config) with
  | None => true
  | Some _ => false
  end.

Definition step (tm : TM) (config : Tape tm) : option (Tape tm) :=
  match transition_function tm (cur_state config) (current_symbol config) with
  | None => None
  | Some (s', sym', d) =>
      match d with
      | L =>
          let new_current := match tape_left config with
                             | [] => blank_symbol tm
                             | h :: _ => h
                             end in
          let new_left := match tape_left config with
                          | [] => []
                          | _ :: t => t
                          end in
          let new_right := sym' :: tape_right config in
          Some (make_tape s' new_left new_current new_right)
      | R =>
          let new_current := match tape_right config with
                             | [] => blank_symbol tm
                             | h :: _ => h
                             end in
          let new_right := match tape_right config with
                           | [] => []
                           | _ :: t => t
                           end in
          let new_left := sym' :: tape_left config in
          Some (make_tape s' new_left new_current new_right)
      end
  end.

Fixpoint run_steps (tm : TM) (config : Tape tm) (n : nat) : option (Tape tm) :=
  match n with
  | O => Some config
  | S n' => match run_steps tm config n' with
            | Some config' => step tm config'
            | None => None
            end
  end.
(* TM with config c1 visits config c2 in n steps *)
Definition run (tm : TM) (c1 c2 : Tape tm) : Prop :=
  exists n, run_steps tm c1 n = Some c2.
(* TM halts after n steps *)
Definition takes_steps (tm : TM) (start : Tape tm) (n : nat) : Prop :=
  exists config, run_steps tm start n = Some config /\ halts tm config = true.

(* For all step numbers n, TM with given config does not halt. *)
Definition runs_forever (tm : TM) (start : Tape tm) : Prop :=
  forall n, exists config, run_steps tm start n = Some config.


Definition is_non_blank {tm : TM} (s : symbol tm) : bool :=
  if Fin.eq_dec s (blank_symbol tm) then false else true.
  

Fixpoint count_non_blank_list {tm : TM} (l : list (symbol tm)) : nat :=
  match l with
  | [] => O
  | h :: t => if is_non_blank h then S (count_non_blank_list t) else count_non_blank_list t
  end.

Definition count_non_blank_state {tm : TM} (config : Tape tm) : nat :=
  count_non_blank_list (tape_left config) +
  (if is_non_blank (current_symbol config) then 1 else 0) +
  count_non_blank_list (tape_right config).

(* Definition for a TM producing m non-blank symbols upon halting *)
Definition produces_ones (tm : TM) (m : nat) : Prop :=
  exists (steps : nat) (config : Tape tm),
    run_steps tm (init tm) steps = Some config /\
    halts tm config = true /\
    count_non_blank_state config = m.

(* Busy Beaver Sigma Function BB(n) *)
Definition BB (n ones : nat) : Prop :=
  (* There exists a TM with n states and 2 symbols that produces ones non-blank symbols upon halting *)
  (exists tm : TM,
     number_of_states tm = n /\
     number_of_symbols tm = 2%nat /\
     produces_ones tm ones)
  /\
  (* and this TM scores the highest number of ones before halting *)
  (forall tm : TM,
     number_of_states tm = n ->
     number_of_symbols tm = 2%nat ->
     forall m, produces_ones tm m -> (m <= ones)%nat).

(* A TM that runs forever *)
Definition loop_tm : TM := {|
  number_of_states := 1; number_of_symbols := 2;
  blank_symbol := Fin.F1;
  transition_function := fun s sym => Some (s, sym , R);
  start_state := Fin.F1
|}.


Compute run_steps loop_tm (init loop_tm) 5.  
Compute halts loop_tm (init loop_tm).       
 
(* A TM that halts immediately *)
Definition halt_tm : TM := {|
  number_of_states := 1; number_of_symbols := 2;
  blank_symbol := Fin.F1;
  transition_function := fun s sym => None;
  start_state := Fin.F1
|}.

Compute run_steps halt_tm (init halt_tm) 0.
Compute run_steps halt_tm (init halt_tm) 10.  

(* Unary encoding of natural numbers *)
Definition encodes {tm : TM} (config : Tape tm) (n : nat) : Prop :=
  exists s : symbol tm,
    s <> blank_symbol tm /\
    Forall (fun x => x = blank_symbol tm) (tape_left config) /\ (* left of tape is blank *)
     (* if n is zero, tape is blank else construct prefix as a sequence of s *)
    match n with
    | O => current_symbol config = blank_symbol tm /\ Forall (fun x => x = blank_symbol tm) (tape_right config)
    | S n' =>
        current_symbol config = s /\
        (* prefix = n' and  suffix = [blank_symbol tm]*)
        exists prefix suffix,
          tape_right config = prefix ++ suffix /\
          length prefix = n' /\
          Forall (fun x => x = s) prefix /\
          Forall (fun x => x = blank_symbol tm) suffix
    end.
(* A TM M is said to compute a function f:Σ*↦Σ* iff M halts and encodes f(n) *)
Definition computes_function (tm : TM) (f : nat -> nat -> Prop) : Prop :=
  exists mark : symbol tm,
    mark <> blank_symbol tm /\
    forall n m : nat, f n m ->
      exists config : Tape tm,
        run tm (init tm) config /\
        halts tm config = true /\
        encodes config m.

Proposition BB_uncomputable : ~exists tm : TM, computes_function tm BB.
Admitted.