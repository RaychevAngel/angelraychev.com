import LocalArenaRows

/-! Fixed-size local arenas for the six-type construction. Removed vertices
have no messenger moves and collide with every cop state. This permits a
total embedding while all checked regions exclude those dummy rows. -/
namespace Delivery.SixTypeLocal
open LocalArena

abbrev R := Fin 54
abbrev C := Fin 79
def omega : C := 78
def rcop (r : R) : C := ⟨r.val+12, by omega⟩
def rcol (r : R) : Nat := r.val/6+2
def rtype (r : R) : Nat := r.val%6
def presentR (p : List Nat) (r : R) : Prop := rtype r ≠ 4 ∨ rcol r ∉ p
def presentC (p : List Nat) (c : C) : Prop :=
  c.val=78 ∨ c.val%6 ≠ 4 ∨ c.val/6 ∉ p
instance (p : List Nat) (r : R) : Decidable (presentR p r) :=
  inferInstanceAs (Decidable (_ ∨ _))
instance (p : List Nat) (c : C) : Decidable (presentC p c) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def pack (u : Nat) (j : Fin 6) : C :=
  if h : u<13 then ⟨6*u+j.val,by omega⟩ else omega

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

def replies (p : List Nat) (c : C) : List C :=
  if c.val=78 then (List.finRange 79).filter fun d =>
    decide (presentC p d ∧ (d.val=78 ∨ d.val/6<2 ∨ 10<d.val/6))
  else if presentC p c then [c,first p c,second p c] else []

def arena (p : List Nat) : Arena R C where
  messenger r z := presentR p r ∧ presentR p z ∧
    (z=r ∨ rcop z=first p (rcop r) ∨ rcop z=second p (rcop r))
  pursuer c d := d∈replies p c
  collision r c := ¬presentR p r ∨ (rcop r=c)

instance (p : List Nat) (r z : R) : Decidable ((arena p).messenger r z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _ ∨ _)))
instance (p : List Nat) (c d : C) : Decidable ((arena p).pursuer c d) :=
  inferInstanceAs (Decidable (_ ∈ _))
instance (p : List Nat) (r : R) (c : C) : Decidable ((arena p).collision r c) :=
  inferInstanceAs (Decidable (_ ∨ _))

def transferGoal (p : List Nat) (r : R) : Prop := presentR p r ∧ rcol r=6
def deliveryGoal (p : List Nat) (t : Fin 6) (r : R) : Prop :=
  presentR p r ∧ rcol r=6 ∧ rtype r=t.val
instance (p : List Nat) (r : R) : Decidable (transferGoal p r) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (p : List Nat) (t : Fin 6) (r : R) : Decidable (deliveryGoal p t r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The concrete certificate exporter supplies this for every catalog pattern. -/
structure Certificates (p : List Nat) : Prop where
  transfer : ∃ D : Data R C, SafeChecked (arena p) (transferGoal p) D ∧
    ∀ r c, presentR p r → rcol r=5 → presentC p c →
      ¬(arena p).collision r c → D.region r c ∧ D.rank r c≤9
  delivery : ∀ t : Fin 6, (t.val≠4 ∨ 6∉p) →
    ∃ D : Data R C, DeliveryChecked (arena p) (deliveryGoal p t) D ∧
      ∀ r c, presentR p r → rcol r=4 → presentC p c →
        ¬(arena p).collision r c → D.region r c ∧ D.rank r c≤27

end Delivery.SixTypeLocal
