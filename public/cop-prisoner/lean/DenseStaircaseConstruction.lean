import DenseBlockAttachment
import DenseCore
import SmallRootAttachment

/-! Explicit attainment of every dense staircase offset r≥2 at order n≥20.
The recipe uses a functional block plus the explicit core when k=n-r≥10;
for the remaining k≤9 it uses the nine prescribed root pairs. -/
namespace Delivery.DenseStaircaseConstruction
open FiniteGame Extremal

def graph (r k : Nat) (hr : 2 ≤ r) (hn : 20 ≤ r+k) : Graph (Fin (r+k)) :=
  if hk : 10 ≤ k then
    DenseBlockAttachment.graph r k hr (DenseCore.graph k hk)
  else (SmallRootAttachment.data r k (by omega) (by omega)).edge

theorem loopless {r k : Nat} (hr : 2 ≤ r) (hn : 20 ≤ r+k) :
    Loopless (graph r k hr hn) := by
  unfold graph
  split
  · exact ComplementarySum.loopless (FunctionalEndpoint.loopless _)
      (DenseCore.graph_loopless _)
  · exact RootAttachment.Data.loopless _

theorem arc_count {r k : Nat} (hr : 2 ≤ r) (hn : 20 ≤ r+k) :
    arcCount (graph r k hr hn) = (r+k)*(r+k-3)+r := by
  unfold graph
  split
  · exact DenseBlockAttachment.arc_count hr (by omega) _
      (DenseCore.graph_loopless _) (DenseCore.graph_missingCount _)
  · exact SmallRootAttachment.arc_count _ _

theorem score_count {r k : Nat} (hr : 2 ≤ r) (hn : 20 ≤ r+k) :
    score (graph r k hr hn) = (r-2)/2+2*k := by
  unfold graph
  split
  · exact DenseBlockAttachment.score_exact hr (by omega) _
      (DenseCore.graph_loopless _) (DenseCore.graph_positive_missing _)
      (DenseCore.graph_missingCount _) (DenseCore.graph_two_move _)
  · exact SmallRootAttachment.score_exact _ _

theorem maximum_blocks {r k : Nat} (hr : 2 ≤ r) (hn : 20 ≤ r+k) :
    IsMaximum (r+k) ((r+k)*(r+k-3)+r) ((r-2)/2+2*k) := by
  constructor
  · intro E noLoops arrows
    have upper := DenseStaircase.bound_at_offset E noLoops (by omega)
      (by omega) (by omega) arrows
    unfold DenseCounting.ceilHalf at upper
    omega
  · exact ⟨graph r k hr hn,loopless hr hn,arc_count hr hn,score_count hr hn⟩

/-- Every offset except the first, with all construction premises discharged. -/
theorem maximum {n r : Nat} (hn : 20 ≤ n) (hr : 2 ≤ r) (hrn : r ≤ n) :
    IsMaximum n (n*(n-3)+r) (2*n-r-DenseCounting.ceilHalf r-1) := by
  have result := maximum_blocks (k := n-r) hr (by omega)
  have order : r+(n-r) = n := by omega
  have count : (r-2)/2+2*(n-r) = 2*n-r-DenseCounting.ceilHalf r-1 := by
    unfold DenseCounting.ceilHalf
    omega
  simpa only [order,count] using result

#print axioms graph
#print axioms maximum
end Delivery.DenseStaircaseConstruction
