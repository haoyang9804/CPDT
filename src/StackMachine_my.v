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

Definition Stack := list nat.

Definition instrDenote (i : instr) (s : Stack) : option Stack :=
match i with
| iConst n => Some (n :: s)
| iBinop b => match s with
                | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
                | _ => None
                end
end.

Definition prog := list instr.

Fixpoint progDenote (p : prog) (s : Stack) : option Stack :=
match p with
| nil => Some s
| i :: p' => match instrDenote i s with
            | Some s' => progDenote p' s'
            | None => None
            end
end.

Fixpoint compile (e : exp) : prog :=
match e with
| Const n => iConst n :: nil
| Binop e1 e2 b => compile e2 ++ compile e1 ++ iBinop b :: nil
end.

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



(* (*
The failure of executing the following self-defined *tinstrDenote* is the reason why we need both tstack and vstack and put tstack into the definition of tinstr to denote the type
*)

Inductive tinstr : type -> Set := 
| TiNConst : nat -> tinstr Nat
| TiBConst : bool -> tinstr Bool
| TiBinop : forall t1 t2 t3, tbinop t1 t2 t3 -> tinstr t3.

Definition tstack := list type.

Definition tinstrDenote t (ti : tinstr t) (ts : tstack) : option tstack :=
match ti with
| TiNConst n => Some (n :: ts)
| TiBConst b => Some (b :: ts)
| TiBinop e1 e2 e3 tb => 
    match ts with  
    | arg1 :: arg2 :: ts' => Some ((tbinopDenote tb) arg1 arg2 :: ts')
    | _ => None
    end
end. *)

Definition tstack := list type.

Check list type.
Check tstack.

Fixpoint vstack (ts : tstack) : Set :=
match ts with
| nil => unit
| t :: ts' => typeDenote t * vstack ts'
end%type.

Check forall ts, vstack ts.

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall ts, nat -> tinstr ts (Nat :: ts)
| TiBConst : forall ts, bool -> tinstr ts (Bool :: ts)
| TiBinop : forall arg1 arg2 res ts, tbinop arg1 arg2 res 
    -> tinstr (arg1 :: arg2 :: ts) (res :: ts).

Definition tinstrDenote ts1 ts2 (ti : tinstr ts1 ts2) : vstack ts1 -> vstack ts2 :=
match ti with
| TiNConst ts n => fun s => (n, s)
| TiBConst ts b => fun s => (b, s)
| TiBinop arg1 arg2 res ts tb =>
    fun s => let '(arg1, (arg2, s')) := s in
    ((tbinopDenote tb) arg1 arg2, s')
end.