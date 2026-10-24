import LowBandGraph
import LocalArenaRows

/-! A fixed padded radius-five/radius-eight local optional-arrow arena.
Removed messenger rows have no legal moves and collide universally. -/
namespace Delivery.LowBandLocal
open LocalArena LowBandGraph

abbrev R := Fin 66
abbrev C := Fin 103
def omega : C := 102
def rcop (r : R) : C := ⟨r.val+18,by omega⟩
def rcol (r : R) : Nat := r.val/6+3
def rtype (r : R) : Nat := r.val%6
def presentR (p : List Nat) (r : R) : Prop := rtype r≠4 ∨ rcol r∉p
def presentC (p : List Nat) (c : C) : Prop :=
  c.val=102 ∨ c.val%6≠4 ∨ c.val/6∉p
instance (p : List Nat) (r : R) : Decidable (presentR p r) :=
  inferInstanceAs (Decidable (_ ∨ _))
instance (p : List Nat) (c : C) : Decidable (presentC p c) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def pack (u : Nat) (j : Fin 6) : C :=
  if h : u<17 then ⟨6*u+j.val,by omega⟩ else omega

def first (p : List Nat) (c : C) : C :=
  let u := c.val/6
  match c.val%6 with
  | 0 => pack u 1
  | 1 => pack u 2
  | 2 => pack u 3
  | 3 => pack u (if u∈p then 5 else 4)
  | 4 => pack u 5
  | _ => pack (u+1) 0

def second (p : List Nat) (c : C) : C :=
  let u := c.val/6
  match c.val%6 with
  | 0 => pack u 5
  | 1 => if u+1∈p then pack (u+2) 2 else pack (u+1) 4
  | 2 => pack (u+1) 1
  | 3 => if u=0 then omega else pack (u-1) 0
  | 4 => pack (u+1) 2
  | _ => if u=0 then omega else pack (u-1) 3

def excluded (p : List Nat) (u : Nat) (e : Tag) : Prop :=
  ∃ h : Fin 17, h.val∈p ∧
    ((u=h.val ∧ (e=0 ∨ e=1)) ∨
     (u=h.val+1 ∧ (e=0 ∨ e=1 ∨ e=5)) ∨
     (u=h.val+2 ∧ (e=1 ∨ e=2)))
instance (p : List Nat) (u : Nat) (e : Tag) : Decidable (excluded p u e) :=
  inferInstanceAs (Decidable (∃ _h : Fin 17, _ ∧ _))

def extra (u : Nat) (e : Tag) : C :=
  match e.val with
  | 0 | 1 | 2 | 6 => if u<3 then omega else pack (u-3) (targetType e)
  | 3 | 4 | 5 => pack (u+3) (targetType e)
  | _ => if u<2 then omega else pack (u-2) (targetType e)

def extraReplies (p : List Nat) (c : C) : List C :=
  ((List.finRange 8).filter fun e =>
    decide (c.val%6=(sourceType e).val ∧ ¬excluded p (c.val/6) e)).map
      (fun e => extra (c.val/6) e)

def replies (p : List Nat) (c : C) : List C :=
  if c.val=102 then (List.finRange 103).filter fun d =>
    decide (presentC p d ∧ (d.val=102 ∨ d.val/6<3 ∨ 13<d.val/6))
  else if presentC p c then [c,first p c,second p c]++extraReplies p c else []

def arena (p : List Nat) : Arena R C where
  messenger r z := presentR p r ∧ presentR p z ∧
    (z=r ∨ rcop z=first p (rcop r) ∨ rcop z=second p (rcop r))
  pursuer c d := d∈replies p c
  collision r c := ¬presentR p r ∨ rcop r=c
instance (p : List Nat) (r z : R) : Decidable ((arena p).messenger r z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _ ∨ _)))
instance (p : List Nat) (c d : C) : Decidable ((arena p).pursuer c d) :=
  inferInstanceAs (Decidable (_ ∈ _))
instance (p : List Nat) (r : R) (c : C) : Decidable ((arena p).collision r c) :=
  inferInstanceAs (Decidable (_ ∨ _))

def transferGoal (p : List Nat) (r : R) : Prop := presentR p r ∧ rcol r=8
def deliveryGoal (p : List Nat) (t : Fin 6) (r : R) : Prop :=
  presentR p r ∧ rcol r=8 ∧ rtype r=t.val
instance (p : List Nat) (r : R) : Decidable (transferGoal p r) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (p : List Nat) (t : Fin 6) (r : R) : Decidable (deliveryGoal p t r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

structure Certificates (p : List Nat) : Prop where
  transfer : ∃ D : Data R C, SafeChecked (arena p) (transferGoal p) D ∧
    ∀ r c, presentR p r → rcol r=7 → presentC p c →
      ¬(arena p).collision r c → D.region r c ∧ D.rank r c≤9
  delivery : ∀ t : Fin 6, (t.val≠4 ∨ 8∉p) →
    ∃ D : Data R C, DeliveryChecked (arena p) (deliveryGoal p t) D ∧
      ∀ r c, presentR p r → (rcol r=5 ∨ rcol r=6) → presentC p c →
        ¬(arena p).collision r c →
        D.region r c ∧ D.rank r c≤(if rcol r=5 then 39 else 38)

end Delivery.LowBandLocal
