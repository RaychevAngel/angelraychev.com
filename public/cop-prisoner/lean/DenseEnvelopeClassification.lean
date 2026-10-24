import DenseOddEnvelope
import FiniteDenseEnvelopes
import SmallDenseEnvelopeMaxima

/-! The complete one-optional-arc-per-vertex numerical interval for n≥16.
Finite literal repairs, even formulas, and odd formulas retain their exact
domains. Each branch invokes a proved, prescribed prefix construction. -/
namespace Delivery.DenseEnvelopeClassification
open FiniteGame Extremal

/-- Every budget between n(n−1)−3n and n(n−1)−2n attains every missing pair. -/
theorem maximum {n m : Nat} (hn : 16 ≤ n)
    (low : n*(n-1)-3*n ≤ m) (high : m ≤ n*(n-1)-2*n) :
    IsMaximum n m (n*(n-1)-m) := by
  by_cases small : n ≤ 21
  · let i : Fin 6 := ⟨n-16,by omega⟩
    have order : i.val+16 = n := by dsimp [i]; omega
    have result := SmallDenseEnvelopeMaxima.maximum i m
      (by simpa only [order] using low) (by simpa only [order] using high)
    simpa only [order] using result
  · have large : 22 ≤ n := by omega
    have capacity : 3*n ≤ n*(n-1) := by
      have mul := Nat.mul_le_mul_left n (show 3 ≤ n-1 by omega)
      omega
    let h := n*(n-1)-m
    have lowerMissing : 2*n ≤ h := by dsimp [h]; omega
    have upperMissing : h ≤ 3*n := by dsimp [h]; omega
    have budget : n*(n-1)-h = m := by dsimp [h]; omega
    by_cases even : n % 2 = 0
    · have order : 2*(n/2) = n := by omega
      have result := DenseEnvelope.maximum (k := n/2) (h := h) (by omega)
        (by omega) (by omega)
      simpa only [order,budget] using result
    · by_cases repaired : n = 23 ∨ n = 25 ∨ n = 27 ∨ n = 31
      · exact FiniteDenseEnvelopes.maximum n m repaired low high
      · have order : 2*(n/2)+1 = n := by omega
        have previous : 2*(n/2) = n-1 := by omega
        have hk : 14 ≤ n/2 := by omega
        have range : n/2 = 14 ∨ 16 ≤ n/2 := by omega
        have result := DenseOddEnvelope.maximum (k := n/2) (h := h) hk range
          (by omega) (by omega)
        rw [order,previous,budget] at result
        exact result

/-- Equivalent missing-budget form, retaining the exact all-orders domain. -/
theorem maximum_missing {n h : Nat} (hn : 16 ≤ n)
    (low : 2*n ≤ h) (high : h ≤ 3*n) :
    IsMaximum n (n*(n-1)-h) h := by
  have capacity : 3*n ≤ n*(n-1) := by
    have mul := Nat.mul_le_mul_left n (show 3 ≤ n-1 by omega)
    omega
  have result := maximum hn (m := n*(n-1)-h) (by omega) (by omega)
  have score : n*(n-1)-(n*(n-1)-h) = h := by omega
  simpa only [score] using result

#print axioms maximum
#print axioms maximum_missing
end Delivery.DenseEnvelopeClassification
