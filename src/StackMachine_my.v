Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set :=
| Plus
| Times.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
match b with
| Plus => plus
| Times => mult
end.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : exp -> exp -> binop -> exp.

Fixpoint expDenote (e : exp) : nat :=
match e with
| Const n => n
| Binop e1 e2 b => (binopDenote b) (expDenote e1) (expDenote e2)
end.

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Inductive type : Set := Nat | Bool.

Definition typeDenote (t : type) : Set :=
match t with
| Nat => nat
| Bool => bool
end.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes: tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

Definition tbinopDenote t1 t2 t3 (tb : tbinop t1 t2 t3) : 
typeDenote t1 -> typeDenote t2 -> typeDenote t3 :=
match tb with
| TPlus => plus
| TTimes => mult
| TEq Nat => beq_nat
| TEq Bool => eqb
| TLt => leb
end.

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Fixpoint texpDenote tp (t : texp tp) : typeDenote tp :=
match t with
| TNConst nt => nt
| TBConst bl => bl
| TBinop arg1 arg2 res b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
end.

Inductive tinstr : 
