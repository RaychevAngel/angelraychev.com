import SparseParity
import ExactScoreCertificates
import GraphPadding

/-! The sharp unrestricted six-arrow bound. The only numerical case above
 two pairs saturates a disjoint active-source/active-target cut; its arrows
 cannot be followed by another arrow, contradicting a live source. -/
namespace Delivery.SmallBudgetSix
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseDeletion

/-- A counted arrow witnesses positivity of the literal edge count. -/
theorem arc_positive_of_edge {n : Nat} {E : Graph (Fin n)} {s t : Fin n}
    (edge : E s t) : 0 < arcCount E := by
  classical
  apply List.length_pos_of_mem (a := (s,t))
  simp [allPairs,edge]

/-- If a cut already counts every arrow, every actual arrow lies in it. -/
theorem saturated_cut {n : Nat} (E : Graph (Fin n)) (A B : Fin n → Prop)
    (saturated : cut E A B=arcCount E) {s t : Fin n} (edge : E s t) : A s ∧ B t := by
  classical
  have partition := arcs_partition E (fun s t => A s ∧ B t)
  change cut E A B + arcCount (fun s t => E s t ∧ ¬(A s ∧ B t)) = arcCount E at partition
  apply Classical.byContradiction
  intro absent
  have positive := arc_positive_of_edge (E := fun s t => E s t ∧ ¬(A s ∧ B t)) ⟨edge,absent⟩
  omega

/-- A saturated cut with disjoint sides has no live indirect pair. -/
theorem score_zero_of_disjoint_saturated_cut {n : Nat} (E : Graph (Fin n))
    (loopless : Loopless E) (A B : Fin n → Prop)
    (saturated : cut E A B=arcCount E)
    (disjoint : card (fun x => A x ∧ B x)=0) : score E=0 := by
  apply score_eq_zero
  intro s t different missing guaranteed
  obtain ⟨a,b,ha,_,_⟩ := live_two_nonsink_successors loopless ⟨different,missing,guaranteed⟩
  obtain ⟨z,az⟩ := ha.2
  have head := (saturated_cut E A B saturated ha.1).2
  have tail := (saturated_cut E A B saturated az).1
  exact (card_eq_zero.mp disjoint) a ⟨tail,head⟩

private theorem six_scalar (q r b e I : Nat) (hq : q≤3) (hr : r≤3)
    (incidence : 2*q+2*r≤6+e) (rectangle : I+b+e≤q*r) :
    I≤2 ∨ (q=3 ∧ r=3 ∧ b=0) := by
  have qs : q=0 ∨ q=1 ∨ q=2 ∨ q=3 := by omega
  have rs : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases qs with rfl | rfl | rfl | rfl <;>
    rcases rs with rfl | rfl | rfl | rfl <;> simp_all <;> omega

/-- Every loopless finite graph with six arrows has at most two guaranteed
missing ordered pairs. No support-order or cardinality premise is supplied. -/
theorem upper {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (budget : arcCount E=6) : score E≤2 := by
  have sizes := active_card_bounds E
  have incidence := active_incidence E
  have rectangle := eligible_rectangle E loopless
  rw [budget] at sizes incidence
  obtain bound | ⟨q,r,disjoint⟩ := six_scalar (card (ActiveOut E)) (card (ActiveIn E))
    (card (fun x => ActiveOut E x ∧ ActiveIn E x))
    (cut E (ActiveOut E) (ActiveIn E)) (score E)
    (by omega) (by omega) incidence rectangle
  · exact bound
  · have subset := arcs_mono (E := fun s t => E s t ∧ ActiveOut E s ∧ ActiveIn E t)
      (F := E) (fun _ _ h => h.1)
    change cut E (ActiveOut E) (ActiveIn E)≤arcCount E at subset
    rw [q,r] at incidence
    have saturated : cut E (ActiveOut E) (ActiveIn E)=arcCount E := by omega
    have zero := score_zero_of_disjoint_saturated_cut E loopless _ _ saturated disjoint
    omega

/-- The existing literal four-vertex certificate attains the bound, and
isolate padding preserves both its six arrows and its exact score. -/
theorem maximum {n : Nat} (order : 4≤n) : IsMaximum n 6 2 := by
  constructor
  · exact fun E loopless budget => upper E loopless budget
  · obtain ⟨F,loopless,arcs,value⟩ := GraphPadding.pad_to_order
      ExactScoreCertificates.FourVertex.edge ExactScoreCertificates.FourVertex.loopless order
    exact ⟨F,loopless,arcs.trans ExactScoreCertificates.FourVertex.arcs_six,
      value.trans ExactScoreCertificates.FourVertex.score_two⟩

#print axioms upper
#print axioms maximum
end Delivery.SmallBudgetSix
