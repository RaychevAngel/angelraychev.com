import RowPrefixBooleanNine

/-! Complete next-row routing with an explicit invalid-column witness and a
reflexive shortcut. No previous row is rechecked for every next-row choice. -/
namespace Delivery.RowPrefix.FastRouting
open FiniteGame Extremal BooleanNine

def reject (R : Fin 9 → Nat) (p : List Nat) (h : p.length < 9) (mask : Nat) (column : Fin 9) : Bool :=
  decide (bit mask ⟨p.length,h⟩) ||
  !decide (used (p++[mask]) column ≤ R column ∧
    R column ≤ ((List.finRange 9).filter fun s => decide (possible (p++[mask]) s column)).length)

theorem reject_sound (D R : Fin 9 → Nat) (p : List Nat) (h : p.length < 9)
    (mask : Nat) (column : Fin 9) (bound : Nat)
    (checked : reject R p h mask column = true) : Upper D R (p++[mask]) bound := by
  apply invalid_upper
  intro valid
  simp only [reject,Bool.or_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,decide_eq_true_eq] at checked
  rcases checked with loop | capacity
  · have noLoop := (valid.1 ⟨p.length,h⟩ (by simp)).1
    apply noLoop
    simpa using loop
  · exact capacity (valid.2 column)

def check (D R : Fin 9 → Nat) (p : List Nat) (h : p.length < 9)
    (rows representatives : List Nat) (route : Route 9) (column : Nat → Fin 9) : Bool :=
  rows.all fun mask => reject R p h mask (column mask) ||
    (decide ((route mask).1 ∈ representatives) &&
      (decide ((route mask).1=mask) || mapCheck D R (p++[mask]) (p++[(route mask).1]) (route mask).2))

theorem sound (D R : Fin 9 → Nat) (p : List Nat) (bound : Nat) (h : p.length < 9)
    (rows representatives : List Nat) (route : Route 9) (column : Nat → Fin 9)
    (cover : RowCover 9 (D ⟨p.length,h⟩) rows)
    (checked : check D R p h rows representatives route column = true)
    (children : ∀ mask ∈ representatives, Upper D R (p++[mask]) bound) : Upper D R p bound := by
  apply branch_upper D R p bound h rows cover
  intro mask member
  have row := List.all_eq_true.mp checked mask member
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,mapCheck_true] at row
  rcases row with rejected | ⟨listed,same | mapped⟩
  · exact reject_sound D R p h mask (column mask) bound rejected
  · simpa only [same] using children (route mask).1 listed
  · exact map_upper D R _ _ (route mask).2 bound mapped (children (route mask).1 listed)

#print axioms sound
end Delivery.RowPrefix.FastRouting
