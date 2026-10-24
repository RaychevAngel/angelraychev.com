import GraphPadding
import SmallSparseWitness11
import SmallSparseWitness12
import SmallSparseWitness13
import SmallSparseWitness14
import SmallSparseWitness15
import SmallSparseWitness16
import SmallSparseWitness17
import SmallSparseWitness18
import SmallSparseWitness19
import SmallSparseWitness20
import SmallSparseWitness21
import SparseWitness11
import SmallSparseWitness23

/-! Exact scores of prescribed small-budget witnesses, lifted by isolates.
No upper bound over competing graphs is asserted by this module. -/
namespace Delivery.SmallSparseWitnesses
open FiniteGame Extremal

def value (m : Nat) : Nat := match m with
  | 11 => 8
  | 12 => 9
  | 13 => 11
  | 14 => 13
  | 15 => 15
  | 16 => 19
  | 17 => 28
  | 18 => 33
  | 19 => 40
  | 20 => 53
  | 21 => 60
  | 22 => 79
  | 23 => 83
  | _ => 0

def support (m : Nat) : Nat := match m with
  | 11 => 7
  | 12 => 7
  | 13 => 8
  | 14 => 8
  | 15 => 8
  | 16 => 8
  | 17 => 10
  | 18 => 9
  | 19 => 11
  | 20 => 10
  | 21 => 12
  | 22 => 11
  | 23 => 12
  | _ => 0

theorem literal (m : Nat) (range : 11≤m ∧ m≤23) :
    ∃E : Graph (Fin (support m)),Loopless E ∧ arcCount E=m ∧ score E=value m := by
  have cases : m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 ∨ m=16 ∨ m=17 ∨ m=18 ∨ m=19 ∨ m=20 ∨ m=21 ∨ m=22 ∨ m=23 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨SmallSparseWitness11.edge,SmallSparseWitness11.loopless,SmallSparseWitness11.arrows,SmallSparseWitness11.exact_score⟩
  · exact ⟨SmallSparseWitness12.edge,SmallSparseWitness12.loopless,SmallSparseWitness12.arrows,SmallSparseWitness12.exact_score⟩
  · exact ⟨SmallSparseWitness13.edge,SmallSparseWitness13.loopless,SmallSparseWitness13.arrows,SmallSparseWitness13.exact_score⟩
  · exact ⟨SmallSparseWitness14.edge,SmallSparseWitness14.loopless,SmallSparseWitness14.arrows,SmallSparseWitness14.exact_score⟩
  · exact ⟨SmallSparseWitness15.edge,SmallSparseWitness15.loopless,SmallSparseWitness15.arrows,SmallSparseWitness15.exact_score⟩
  · exact ⟨SmallSparseWitness16.edge,SmallSparseWitness16.loopless,SmallSparseWitness16.arrows,SmallSparseWitness16.exact_score⟩
  · exact ⟨SmallSparseWitness17.edge,SmallSparseWitness17.loopless,SmallSparseWitness17.arrows,SmallSparseWitness17.exact_score⟩
  · exact ⟨SmallSparseWitness18.edge,SmallSparseWitness18.loopless,SmallSparseWitness18.arrows,SmallSparseWitness18.exact_score⟩
  · exact ⟨SmallSparseWitness19.edge,SmallSparseWitness19.loopless,SmallSparseWitness19.arrows,SmallSparseWitness19.exact_score⟩
  · exact ⟨SmallSparseWitness20.edge,SmallSparseWitness20.loopless,SmallSparseWitness20.arrows,SmallSparseWitness20.exact_score⟩
  · exact ⟨SmallSparseWitness21.edge,SmallSparseWitness21.loopless,SmallSparseWitness21.arrows,SmallSparseWitness21.exact_score⟩
  · exact ⟨SparseWitness11.edge,SparseWitness11.loopless,SparseWitness11.arcs,SparseWitness11.exact_score⟩
  · exact ⟨SmallSparseWitness23.edge,SmallSparseWitness23.loopless,SmallSparseWitness23.arrows,SmallSparseWitness23.exact_score⟩

theorem padded {n m : Nat} (range : 11≤m ∧ m≤23) (room : support m≤n) :
    ∃E : Graph (Fin n),Loopless E ∧ arcCount E=m ∧ score E=value m := by
  obtain ⟨E,loops,arcs,score⟩ := literal m range
  obtain ⟨F,fl,fa,fs⟩ := GraphPadding.pad_to_order E loops room
  exact ⟨F,fl,fa.trans arcs,fs.trans score⟩

theorem support_at_most_twelve (m : Nat) : support m≤12 := by
  unfold support
  split <;> omega

theorem host_twelve {n m : Nat} (order : 12≤n) (range : 11≤m ∧ m≤23) :
    ∃E : Graph (Fin n),Loopless E ∧ arcCount E=m ∧ score E=value m :=
  padded range (Nat.le_trans (support_at_most_twelve m) order)

#print axioms literal
#print axioms padded
#print axioms host_twelve
end Delivery.SmallSparseWitnesses
