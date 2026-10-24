import CyclicArithmetic
import GraphRelabeling
import SparseCropCoverage

/-! The literal six-type cyclic graph, with type-four vertices removed. -/
namespace Delivery.SixTypeGraph
open CyclicArithmetic FiniteGame Extremal

abbrev Raw (k : Nat) := Fin k × Fin 6
def Present {k : Nat} (H : Fin k → Prop) (v : Raw k) : Prop := v.2 ≠ 4 ∨ ¬H v.1
abbrev Vertex {k : Nat} (H : Fin k → Prop) := {v : Raw k // Present H v}
instance {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Raw k) :
    Decidable (Present H v) := inferInstanceAs (Decidable (_ ∨ _))

def firstRaw {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Raw k) : Raw k :=
  match v.2.val with
  | 0 => (v.1,1)
  | 1 => (v.1,2)
  | 2 => (v.1,3)
  | 3 => (v.1,if H v.1 then 5 else 4)
  | 4 => (v.1,5)
  | _ => (shift v.1 1,0)

def secondRaw {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Raw k) : Raw k :=
  match v.2.val with
  | 0 => (v.1,5)
  | 1 => if H (shift v.1 1) then (shift v.1 2,2) else (shift v.1 1,4)
  | 2 => (shift v.1 1,1)
  | 3 => (prev v.1,0)
  | 4 => (shift v.1 1,2)
  | _ => (prev v.1,3)

@[simp] theorem val_three : (3 : Fin 6).val=3 := rfl
@[simp] theorem val_four : (4 : Fin 6).val=4 := rfl
@[simp] theorem val_five : (5 : Fin 6).val=5 := rfl

theorem type_cases (j : Fin 6) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega

theorem first_present {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Raw k) :
    Present H (firstRaw H v) := by
  obtain ⟨i,j⟩ := v
  rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [firstRaw,Present,val_three,val_four,val_five,Fin.val_zero,Fin.val_one]
  all_goals first | exact Or.inl (by decide) | (by_cases h : H i <;> simp [h])

theorem second_present {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Raw k) :
    Present H (secondRaw H v) := by
  obtain ⟨i,j⟩ := v
  rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [secondRaw,Present,val_three,val_four,val_five,Fin.val_zero,Fin.val_one]
  all_goals first | exact Or.inl (by decide) | (by_cases h : H (shift i 1) <;> simp [h])

def first {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Vertex H) : Vertex H :=
  ⟨firstRaw H v.val,first_present H v.val⟩
def second {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Vertex H) : Vertex H :=
  ⟨secondRaw H v.val,second_present H v.val⟩
def edge {k : Nat} (H : Fin k → Prop) [DecidablePred H] : Graph (Vertex H) :=
  fun s t => t=first H s ∨ t=second H s

theorem loopless {k : Nat} (H : Fin k → Prop) [DecidablePred H] : Loopless (edge H) := by
  intro s arrow
  rcases arrow with same | same
  · have h := congrArg (fun v : Vertex H => v.val.2.val) same
    obtain ⟨⟨i,j⟩,hp⟩ := s
    rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [first,firstRaw,val_three,val_four,val_five,Fin.val_zero,Fin.val_one] at h
    all_goals first | omega | (split at h <;> simp_all)
  · have h := congrArg (fun v : Vertex H => v.val.2.val) same
    obtain ⟨⟨i,j⟩,hp⟩ := s
    rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [second,secondRaw,val_three,val_four,val_five,Fin.val_zero,Fin.val_one] at h
    all_goals first | omega | (split at h <;> simp_all)

theorem distinct {k : Nat} (hk : 3≤k) (H : Fin k → Prop) [DecidablePred H]
    (s : Vertex H) : first H s ≠ second H s := by
  intro same
  have h := congrArg (fun v : Vertex H => v.val) same
  obtain ⟨⟨i,j⟩,hp⟩ := s
  rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [first,second,firstRaw,secondRaw] at h
  · split at h
    · exact shift_ne_self i (d:=2) (by decide) (by omega) (congrArg Prod.fst h).symm
    · simp at h
  · split at h <;> simp at h

def holes {k : Nat} (r : Nat) (i : Fin k) : Prop :=
  ∃ j : Fin 5, j.val<r ∧ i.val=3*j.val
instance {k : Nat} (r : Nat) (i : Fin k) : Decidable (holes r i) :=
  inferInstanceAs (Decidable (∃ _j : Fin 5, _ ∧ _))

end Delivery.SixTypeGraph
