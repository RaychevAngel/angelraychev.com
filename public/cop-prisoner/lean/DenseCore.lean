import DenseOddCore
import ExtremalExamples

/-! A single explicit two-move dense core at every order at least ten.
The only finite exception is the existing kernel-checked eleven-vertex graph;
all other orders use the proved two-type formulas. -/
namespace Delivery.DenseCore
open FiniteGame Extremal DenseCombinatorics

structure Core (n : Nat) where
  edge : Graph (Fin n)
  loopless : Loopless edge
  missing_count : missingCount edge = 2*n
  score_count : score edge = 2*n
  two_move : ∀ s t, Universal edge t 2 s
  positive_missing : ∀ c, ∃ u, c ≠ u ∧ ¬ edge c u

def evenCore (k : Nat) (hk : 5 ≤ k) : Core (2*k) where
  edge := DenseTwoType.graph k
  loopless := DenseTwoType.graph_loopless k
  missing_count := by have h := DenseTwoType.graph_missingCount hk; omega
  score_count := by have h := DenseTwoType.graph_score hk; omega
  two_move := DenseTwoType.graph_two_move hk
  positive_missing := by
    intro c
    let u := DenseTwoType.encode (DenseTwoType.first (DenseTwoType.decode c))
    exact ⟨u, (DenseTwoType.graph_missing_iff c u).mpr (Or.inl rfl)⟩

def oddCore (k : Nat) (hk : 6 ≤ k) : Core (2*k+1) where
  edge := DenseOddCore.graph k hk
  loopless := DenseOddCore.graph_loopless k hk
  missing_count := by have h := DenseOddCore.graph_missingCount hk; omega
  score_count := by have h := DenseOddCore.graph_score hk; omega
  two_move := DenseOddCore.graph_two_move hk
  positive_missing := by
    intro c
    let u := DenseOddCore.encode (DenseOddCore.first hk (DenseOddCore.decode c))
    exact ⟨u, (DenseOddCore.graph_missing_iff hk c u).mpr (Or.inl rfl)⟩

def elevenCore : Core 11 where
  edge := ElevenVertexDense.edge
  loopless := ExtremalExamples.eleven_loopless
  missing_count := by
    rw [missingCount_eq]
    exact ElevenVertexDense.indirect_count
  score_count := ExtremalExamples.eleven_score
  two_move := RobustTwoMove.envelope_universal (fun _ _ h => h) (fun _ _ h => h)
    ElevenVertexDense.witnesses
  positive_missing := by decide +kernel

/-- Adjacency is chosen by parity, with the literal graph at order eleven. -/
def core (n : Nat) (hn : 10 ≤ n) : Core n := by
  by_cases eleven : n = 11
  · exact eleven.symm ▸ elevenCore
  · by_cases even : n % 2 = 0
    · have order : 2*(n/2) = n := by omega
      exact order ▸ evenCore (n/2) (by omega)
    · have order : 2*(n/2)+1 = n := by omega
      exact order ▸ oddCore (n/2) (by omega)

def graph (n : Nat) (hn : 10 ≤ n) : Graph (Fin n) := (core n hn).edge

theorem graph_loopless {n : Nat} (hn : 10 ≤ n) : Loopless (graph n hn) :=
  (core n hn).loopless

theorem graph_missingCount {n : Nat} (hn : 10 ≤ n) :
    missingCount (graph n hn) = 2*n := (core n hn).missing_count

theorem graph_score {n : Nat} (hn : 10 ≤ n) : score (graph n hn) = 2*n :=
  (core n hn).score_count

theorem graph_two_move {n : Nat} (hn : 10 ≤ n) (s t : Fin n) :
    Universal (graph n hn) t 2 s := (core n hn).two_move s t

theorem graph_positive_missing {n : Nat} (hn : 10 ≤ n) (c : Fin n) :
    ∃ u, c ≠ u ∧ ¬ graph n hn c u := (core n hn).positive_missing c

theorem graph_arcCount {n : Nat} (hn : 10 ≤ n) :
    arcCount (graph n hn) = n*(n-3) := by
  have partition := arcCount_add_missingCount (graph n hn) (graph_loopless hn)
  rw [graph_missingCount hn] at partition
  have identity : n*(n-1) = n*(n-3)+2*n := by
    have subtract : n-1 = (n-3)+2 := by omega
    rw [subtract,Nat.mul_add,Nat.mul_comm n 2]
  omega

/-- Exact dense boundary, with explicit two-move attainment at every n≥10. -/
theorem maximum {n : Nat} (hn : 10 ≤ n) : IsMaximum n (n*(n-3)) (2*n) := by
  constructor
  · intro E loopless arrows
    have partition := arcCount_add_missingCount E loopless
    have bound := score_le_missing E
    have identity : n*(n-1) = n*(n-3)+2*n := by
      have subtract : n-1 = (n-3)+2 := by omega
      rw [subtract,Nat.mul_add,Nat.mul_comm n 2]
    omega
  · exact ⟨graph n hn,graph_loopless hn,graph_arcCount hn,graph_score hn⟩

#print axioms graph_two_move
#print axioms graph_positive_missing
#print axioms maximum
end Delivery.DenseCore
