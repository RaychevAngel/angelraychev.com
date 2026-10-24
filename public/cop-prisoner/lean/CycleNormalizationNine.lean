import CycleNormalization
import FiniteExclusionNine

/-! Every fixed-point-free permutation on nine vertices is conjugate to one
of the eight first-factor tables used by the finite exclusion certificates. -/
namespace Delivery.CycleNormalizationNine
open CycleNormalization FiniteExclusion

def lengths : Nine.CycleType → List Nat
  | .c2223 => [2,2,2,3]
  | .c225 => [2,2,5]
  | .c234 => [2,3,4]
  | .c27 => [2,7]
  | .c333 => [3,3,3]
  | .c36 => [3,6]
  | .c45 => [4,5]
  | .c9 => [9]

/-- The small table check compares all nine positions in each of eight cycle
forms. It proves only this finite arithmetic identity; coverage is generic. -/
theorem first_table (cycle : Nine.CycleType) :
    ∀ i : Fin 9, (Nine.first cycle i).val = blockNext (lengths cycle) i.val := by
  cases cycle <;> decide +kernel

/-- Complete cycle-type coverage, including explicit inverse maps and the
successor intertwining law needed to transport the second permutation. -/
theorem canonicalize (a : Fin 9 → Fin 9)
    (injective : ∀ x y, a x = a y → x = y) (fixed : ∀ x, a x ≠ x) :
    ∃ cycle : Nine.CycleType, Nonempty (Conjugacy a (Nine.first cycle)) := by
  obtain ⟨cs,nd,_,size,sorted⟩ := sorted_decomposition a injective
  have large : ∀ d, d ∈ cs.map Cycle.size → 2 ≤ d := by
    intro d hd
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hd
    exact c.size_two fixed
  have sortedLengths : (cs.map Cycle.size).Pairwise (· ≤ ·) :=
    List.pairwise_map.mpr sorted
  have total : (cs.map Cycle.size).sum = 9 := by
    simpa only [List.length_flatMap,Cycle.length_entries] using size
  have cases := nine_partitions (cs.map Cycle.size) large sortedLengths total
  have represented : ∃ cycle : Nine.CycleType, cs.map Cycle.size = lengths cycle := by
    rcases cases with h | h | h | h | h | h | h | h
    · exact ⟨.c2223,h⟩
    · exact ⟨.c225,h⟩
    · exact ⟨.c234,h⟩
    · exact ⟨.c27,h⟩
    · exact ⟨.c333,h⟩
    · exact ⟨.c36,h⟩
    · exact ⟨.c45,h⟩
    · exact ⟨.c9,h⟩
  obtain ⟨cycle,form⟩ := represented
  refine ⟨cycle,conjugacy_of_table a (Nine.first cycle) cs nd size ?_⟩
  intro i
  rw [form]
  exact first_table cycle i

#print axioms first_table
#print axioms canonicalize
end Delivery.CycleNormalizationNine
