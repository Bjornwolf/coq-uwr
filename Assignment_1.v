Require Export Logic.

(** **** Problem 1 (10 p.) *)
(** Solve the following exercises: binary (Basics), binary_commute (Induction), 
    and binary_inverse (Induction).
*)

(* FILL IN HERE *)
(** [] *)

(** **** Problem 2 (5 p.) *)
(** Implement the factorial function in the two usual ways: directly
    encoding the definition of the function, and tail-recursively
    using an accumulator. Prove that the two functions are
    extensionally equal.  *)

(* FILL IN HERE *)
(** [] *)

(** **** Problem 3 (5 p.) *)
(** Solve the exercise forall_exists_challenge (MoreCoq).
*)

(* FILL IN HERE *)
(** [] *)

(** **** Problem 4 (5 p.) *)
(** Prove the third duality law for fold.
*)

Definition flip {A B C: Type} (f: A -> B -> C) : B -> A -> C := 
  fun (b : B) => fun (a : A) => f a b.

Fixpoint foldr {A B: Type} (f : A -> B -> B) (u : B) (l : list A) :=
  match l with
    | [] => u
    | x :: l' => f x (foldr f u l')
  end.

Fixpoint foldl {A B: Type} (f : B -> A -> B) (u : B) (l : list A) :=
  match l with
    | [] => u
    | x :: l' => foldl f (f u x) l'
  end.

Theorem third_duality_law : forall (A B : Type) (f : A -> B -> B) (u : B) (l : list A),
  foldr f u l = foldl (flip f) u (rev l).
(* FILL IN HERE *) Admitted.
(** [] *)


(** **** Problem 5 (7 p.) *)
(** Prove the following theorems, either constructively, if the theorem
    is constructively valid, or using your favorite classical axiom, if not:
*)

Theorem t1: forall P Q R: Prop,
  ((P /\ Q) -> R) <-> (P -> (Q -> R)). 
(* FILL IN HERE *) Admitted.

Theorem t2: forall P Q R: Prop,
  (P -> (Q \/ R)) -> (P -> Q) \/ (P -> R). 
(* FILL IN HERE *) Admitted.

Theorem t3: forall P Q: Prop,
  ~ (P /\ Q) -> ~P \/ ~Q.
(* FILL IN HERE *) Admitted.

Theorem t4: forall P Q: Prop,
  ~P \/ ~Q -> ~ (P /\ Q).
(* FILL IN HERE *) Admitted.

Theorem t5: forall P: Prop,
  (~~P -> P) <-> (P \/ ~P).
(* FILL IN HERE *) Admitted.

Parameter X : Type.
Parameter P Q : X -> Prop. 

Theorem t6: (forall (x : X), P x /\ Q x) <-> (forall (x : X), P x) /\ (forall (x : X), Q x).
(* FILL IN HERE *) Admitted.

Theorem t7: (forall (x : X), ~~ P x) -> ~~(forall (x : X), P x).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Problem 6 (3 p.) *)
(** Formalize the following reasoning in Coq. Is it constructive or classical? 

Figaro shaves all men of Seville who do not shave themselves. 
Figaro is a man of Seville. 
Therefore Figaro shaves himself.
*)

(* FILL IN HERE *)
(** [] *)
