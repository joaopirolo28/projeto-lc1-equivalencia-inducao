(** Equivalência entre o Princípio da Indução Matemática e o Princípio da Indução Forte *)

(* begin hide *)
Require Import Arith.
Require Import Classical.
(* end hide *)

(** Seja [P] uma propriedade sobre os números naturais. O Princípio da Indução Matemática (PIM) pode ser enunciado da seguinte forma:  *)

Definition PIM :=
  forall P: nat -> Prop,
    (P 0) ->
    (forall k, P k -> P (S k)) ->
    forall n, P n.

(** Seja [Q] uma propriedade sobre os números naturais. O Princípio da Indução Forte (PIF) pode ser enunciado da seguinte forma:  *)

Definition PIF :=
  forall Q: nat -> Prop,
    (forall k, (forall m, m<k -> Q m) -> Q k) ->
    forall n, Q n.


(** Dado um predicado [P] sobre naturais, se existe um natural [n] que satisfaz a propriedade [P], então existe um [m] que é o menor natural que satisfaz a propriedade [P]. Esta propriedade é conhecida como o Princípio da Boa Ordenação (PBO): *)
Definition PBO := forall P : nat -> Prop,
  (exists n : nat, P n) ->
  exists m : nat, P m /\ forall x : nat, x < m -> ~ P x.

(** Prove que estes princípios são equivalentes: *)

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  split.
  - intro hweak.
    intros P hP.
    enough (H : forall n m, m < n -> P m).
    -- intro n. apply (H (S n) n). apply le_n.
    -- apply (hweak (fun n => forall m, m < n -> P m)).
      + intros m hm. inversion hm.
      + intros k hk m hm.
        apply le_S_n in hm.
        apply Nat.lt_eq_cases in hm.
        destruct hm.
        ++ apply hk. assumption.
        ++ subst m. apply hP. assumption.
  - intros hstrong P hbase hsucc.
    apply hstrong.
    intros k hk.
    destruct k.
    -- exact hbase.
    -- apply hsucc.
       apply hk.
       apply le_n.
Qed.


(** Dado um predicado [P] sobre naturais, se existe um natural [n] que satisfaz a propriedade [P], então existe um [m] que é o menor natural que satisfaz a propriedade [P]. Esta propriedade é conhecida como o Princípio da Boa Ordenação (PBO): *)
Definition PBO := forall P : nat -> Prop,
  (exists n : nat, P n) ->
  exists m : nat, P m /\ forall x : nat, x < m -> ~ P x.

(** Prove que estes princípios são equivalentes: *)

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof. Admitted.

Theorem PBO_equiv_PIM: PBO <-> PIM.
Proof. Admitted.

Theorem PBO_equiv_PIF: PBO <-> PIF.
Proof. Admitted.
