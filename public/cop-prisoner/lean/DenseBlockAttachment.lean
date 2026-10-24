import FunctionalEndpoint
import ComplementarySum

/-! Exact dense staircase values obtained by a functional block and a
two-move core. The all-order explicit core is instantiated separately. -/
namespace Delivery.DenseBlockAttachment
open FiniteGame Extremal DenseCombinatorics FunctionalEndpoint

def graph (r k : Nat) (hr : 2 ≤ r) (B : Graph (Fin k)) : Graph (Fin (r+k)) :=
  ComplementarySum.graph (edge (partner r hr)) B

theorem positive_functional {r : Nat} (hr : 2 ≤ r) (c : Fin r) :
    ∃ u, c ≠ u ∧ ¬ edge (partner r hr) c u :=
  ⟨partner r hr c,Ne.symm (partner_fixed hr c),fun h => h.2 rfl⟩

theorem two_functional {r : Nat} (hr : 2 ≤ r) (s t : Fin r)
    (pair : Indirect (edge (partner r hr)) s t) :
    Universal (edge (partner r hr)) t 2 s := by
  obtain ⟨rfl,root⟩ := (indirect_iff (partner_fixed hr) s t).mp pair
  exact root_two_move (partner_fixed hr) root

theorem score_lower {r k : Nat} (hr : 2 ≤ r) (B : Graph (Fin k))
    (positive : ∀ c, ∃ u, c ≠ u ∧ ¬ B c u)
    (missing : missingCount B = 2*k) (two : ∀ s t, Universal B t 2 s) :
    (r-2)/2+2*k ≤ score (graph r k hr B) := by
  have bound := ComplementarySum.score_lower (positive_functional hr) positive
    (two_functional hr) (fun s t _ => two s t)
  have coreScore : score B = 2*k := by
    rw [score_eq_missing B (fun s t _ _ => universal_guaranteed (two s t)),missing]
  rw [attaining_score hr,coreScore] at bound
  exact bound

theorem missing_count {r k : Nat} (hr : 2 ≤ r) (B : Graph (Fin k))
    (missing : missingCount B = 2*k) : missingCount (graph r k hr B) = r+2*k := by
  unfold graph
  rw [ComplementarySum.missing_count,FunctionalEndpoint.missing_count _ (partner_fixed hr),missing]

theorem arc_count {r k : Nat} (hr : 2 ≤ r) (hn : 3 ≤ r+k)
    (B : Graph (Fin k)) (noLoops : Loopless B) (missing : missingCount B = 2*k) :
    arcCount (graph r k hr B) = (r+k)*(r+k-3)+r := by
  have loops := ComplementarySum.loopless (FunctionalEndpoint.loopless (partner r hr)) noLoops
  have total := arcCount_add_missingCount (graph r k hr B) loops
  rw [missing_count hr B missing] at total
  have identity : (r+k)*(r+k-1) = (r+k)*(r+k-3)+2*(r+k) := by
    have eq : r+k-1 = (r+k-3)+2 := by omega
    rw [eq,Nat.mul_add,Nat.mul_comm (r+k) 2]
  omega

theorem score_exact {r k : Nat} (hr : 2 ≤ r) (hn : 3 ≤ r+k)
    (B : Graph (Fin k)) (noLoops : Loopless B)
    (positive : ∀ c, ∃ u, c ≠ u ∧ ¬ B c u)
    (missing : missingCount B = 2*k) (two : ∀ s t, Universal B t 2 s) :
    score (graph r k hr B) = (r-2)/2+2*k := by
  have lower := score_lower hr B positive missing two
  have upper := DenseStaircase.bound_at_offset (graph r k hr B)
    (ComplementarySum.loopless (FunctionalEndpoint.loopless (partner r hr)) noLoops)
    hn (by omega) (by omega) (arc_count hr hn B noLoops missing)
  unfold DenseCounting.ceilHalf at upper
  omega

theorem maximum_of_core {r k : Nat} (hr : 2 ≤ r) (hn : 3 ≤ r+k)
    (B : Graph (Fin k)) (noLoops : Loopless B)
    (positive : ∀ c, ∃ u, c ≠ u ∧ ¬ B c u)
    (missing : missingCount B = 2*k) (two : ∀ s t, Universal B t 2 s) :
    IsMaximum (r+k) ((r+k)*(r+k-3)+r) ((r-2)/2+2*k) := by
  constructor
  · intro E loops arrows
    have upper := DenseStaircase.bound_at_offset E loops hn (by omega) (by omega) arrows
    unfold DenseCounting.ceilHalf at upper
    omega
  · exact ⟨graph r k hr B,ComplementarySum.loopless (FunctionalEndpoint.loopless (partner r hr)) noLoops,
      arc_count hr hn B noLoops missing,score_exact hr hn B noLoops positive missing two⟩

#print axioms maximum_of_core
end Delivery.DenseBlockAttachment
