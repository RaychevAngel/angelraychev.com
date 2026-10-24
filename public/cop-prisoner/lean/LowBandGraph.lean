import SixTypeGraph
import RobustTwoMove

/-! The optional-arrow envelope on the unchanged canonical six-type base.
The eight tags occur in the order displayed in sparse-packed-holes.md. -/
namespace Delivery.LowBandGraph
open SixTypeGraph CyclicArithmetic Extremal RobustTwoMove

abbrev Tag := Fin 8

def sourceType (e : Tag) : Fin 6 :=
  match e.val with
  | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 4
  | 4 => 2 | 5 => 3 | 6 => 3 | _ => 5

def targetType (e : Tag) : Fin 6 :=
  match e.val with
  | 0 => 5 | 1 => 5 | 3 => 1 | _ => 0

def targetColumn {k : Nat} (i : Fin k) (e : Tag) : Fin k :=
  match e.val with
  | 0 | 1 | 2 | 6 => shift i (k-3)
  | 3 | 4 | 5 => shift i 3
  | _ => shift i (k-2)

def targetRaw {k : Nat} (i : Fin k) (e : Tag) : Raw k :=
  (targetColumn i e,targetType e)

theorem target_survives (e : Tag) : targetType e ≠ 4 := by
  revert e
  decide +kernel

def target {k : Nat} (H : Fin k → Prop) (i : Fin k) (e : Tag) : Vertex H :=
  ⟨targetRaw i e,Or.inl (target_survives e)⟩

def excluded {k : Nat} (H : Fin k → Prop) (i : Fin k) (e : Tag) : Prop :=
  ∃ h : Fin k, H h ∧
    ((i=h ∧ (e=0 ∨ e=1)) ∨
     (i=shift h 1 ∧ (e=0 ∨ e=1 ∨ e=5)) ∨
     (i=shift h 2 ∧ (e=1 ∨ e=2)))

instance {k : Nat} (H : Fin k → Prop) [DecidablePred H] (i : Fin k) (e : Tag) :
    Decidable (excluded H i e) := inferInstanceAs (Decidable (∃ _h : Fin k, _ ∧ _))

def optional {k : Nat} (H : Fin k → Prop) (s t : Vertex H) : Prop :=
  ∃ e : Tag, s.val.2=sourceType e ∧ ¬excluded H s.val.1 e ∧ t=target H s.val.1 e

instance {k : Nat} (H : Fin k → Prop) [DecidablePred H] (s t : Vertex H) :
    Decidable (optional H s t) := inferInstanceAs (Decidable (∃ _e : Tag, _ ∧ _ ∧ _))

def upper {k : Nat} (H : Fin k → Prop) [DecidablePred H] : Graph (Vertex H) :=
  fun s t => edge H s t ∨ optional H s t

instance {k : Nat} (H : Fin k → Prop) [DecidablePred H] (s t : Vertex H) :
    Decidable (upper H s t) := inferInstanceAs (Decidable
      ((t=first H s ∨ t=second H s) ∨ optional H s t))

theorem tag_cases (e : Tag) : e=0 ∨ e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 := by
  revert e
  decide +kernel

theorem source_target_different (e : Tag) : sourceType e ≠ targetType e := by
  revert e
  decide +kernel

theorem upper_loopless {k : Nat} (H : Fin k → Prop) [DecidablePred H] : Loopless (upper H) := by
  intro s arrow
  rcases arrow with base | ⟨e,typ,_,same⟩
  · exact SixTypeGraph.loopless H s base
  · have types := congrArg (fun v : Vertex H => v.val.2) same
    exact source_target_different e (typ.symm.trans types)

theorem base_subset {k : Nat} (H : Fin k → Prop) [DecidablePred H] :
    Subgraph (edge H) (upper H) := fun _ _ h => Or.inl h

end Delivery.LowBandGraph
