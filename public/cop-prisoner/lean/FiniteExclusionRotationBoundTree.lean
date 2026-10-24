import FiniteExclusionBoolean

/-! Complete upper trees for second factors normalized by a commuting rotation.
The normalization premise is explicit and discharged by a separate theorem. -/
namespace Delivery.FiniteExclusion.RotationBounds
open FiniteGame Extremal Bounds BoundTreeRows

def displacement (b : Assignment 9) (s : Fin 9) : Nat := ((b s).val+9-s.val)%9

def Minimum (b : Assignment 9) : Prop := ∀ s, (b 0).val ≤ displacement b s

def UpperPrefix (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) : Prop :=
  ∀ b, Valid a b → Minimum b → Agrees p b → score (edgeOf a b) ≤ bound

def MinimumInvalid (p : List (Fin 9)) : Prop :=
  ∃ h0 : 0 < p.length, ∃ s : Fin 9, ∃ hs : s.val < p.length,
    (p[0]).val > ((p[s.val]).val+9-s.val)%9
instance (p : List (Fin 9)) : Decidable (MinimumInvalid p) :=
  inferInstanceAs (Decidable (∃ h0 : 0 < p.length, _))

theorem minimum_invalid (a : Assignment 9) (p : List (Fin 9)) (bound : Nat)
    (bad : MinimumInvalid p) : UpperPrefix a p bound := by
  intro b _ minimum agrees
  obtain ⟨h0,s,hs,bad⟩ := bad
  have lower := minimum s
  unfold displacement at lower
  rw [agrees 0 h0,agrees s hs] at lower
  change (p[0]).val ≤ ((p[s.val]).val+9-s.val)%9 at lower
  omega

theorem invalid_upper (a : Assignment 9) (p : List (Fin 9)) (bound : Nat)
    (bad : ¬PrefixOK a p) : UpperPrefix a p bound := by
  intro b valid _ agrees
  exact Bounds.invalid_upper a p bound bad b valid agrees

theorem branch_upper (a : Assignment 9) (p : List (Fin 9)) (bound : Nat)
    (h : p.length < 9) (children : ∀ v, UpperPrefix a (p++[v]) bound) :
    UpperPrefix a p bound := by
  intro b valid minimum agrees
  exact children (b ⟨p.length,h⟩) b valid minimum (agrees_append h agrees)

inductive Tree where
  | invalid
  | minimum
  | leaf (certificate : BoundTreeRows.Leaf)
  | camp (certificate : BoundTreeRows.Local)
  | branch (children : Fin 9 → Tree)

def check (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) : Tree → Bool
  | .invalid => decide (¬PrefixOK a p)
  | .minimum => decide (MinimumInvalid p)
  | .leaf leaf => Boolean.leafCheck a p bound leaf
  | .camp cert => decide (LocalOK a p bound cert)
  | .branch children => decide (p.length < 9) &&
      Boolean.all9 (fun v => check a (p++[v]) bound (children v))

theorem sound (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (tree : Tree)
    (checked : check a p bound tree = true) : UpperPrefix a p bound := by
  induction tree generalizing p with
  | invalid =>
    intro b valid _ agrees
    exact Bounds.invalid_upper a p bound (of_decide_eq_true checked) b valid agrees
  | minimum => exact minimum_invalid a p bound (of_decide_eq_true checked)
  | leaf certificate =>
    intro b valid _ agrees
    exact Boolean.leaf_sound a p bound certificate checked b valid agrees
  | camp certificate =>
    intro b valid _ agrees
    exact BoundTreeRows.local_sound a p bound certificate (of_decide_eq_true checked) b valid agrees
  | branch children ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq,Boolean.all9_true] at checked
    exact branch_upper a p bound checked.1 (fun v => ih v (p++[v]) (checked.2 v))

#print axioms minimum_invalid
#print axioms sound
end Delivery.FiniteExclusion.RotationBounds
