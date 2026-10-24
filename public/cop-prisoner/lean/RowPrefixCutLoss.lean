import RowPrefixLoss

/-! Prescribed-degree cut counting with certified permanent losing pairs.
The pairs proved losing are disjoint from direct arrows as well as the score. -/
namespace Delivery.RowPrefix
open FiniteGame Extremal DenseCombinatorics SparseSupport

def degreeSum (D : Fin n → Nat) : Nat := ((List.finRange n).map D).sum
def lowSum (D : Fin n → Nat) : Nat :=
  ((List.finRange n).map fun s => if 2 ≤ D s then 0 else D s).sum

def eligibleCount (D R : Fin n → Nat) : Nat :=
  ((allPairs n).filter fun st => decide (2 ≤ D st.1 ∧ 2 ≤ R st.2 ∧ st.1 ≠ st.2)).length

def cornerCount (D R : Fin n → Nat) (p : List Nat) : Nat :=
  ((allPairs n).filter fun st => decide (¬2 ≤ D st.1 ∧ ¬2 ≤ R st.2 ∧ known p st.1 st.2)).length

def LostOK (D R : Fin n → Nat) (lost : Rows n) (losses : List (Loss n)) : Prop :=
  ∀ s t, bit (lost s) t → 2 ≤ D s ∧ 2 ≤ R t ∧ s ≠ t ∧ LossExists losses s t
instance (D R : Fin n → Nat) (lost : Rows n) (losses : List (Loss n)) :
    Decidable (LostOK D R lost losses) := inferInstanceAs (Decidable (∀ _s _t : Fin n, _))

structure CutBound (n : Nat) where
  lost : Rows n
  upper : Rows n
  lower : Rows n
  losses : List (Loss n)

def CutBoundOK (D R : Fin n → Nat) (p : List Nat) (bound : Nat) (cert : CutBound n) : Prop :=
  EnvelopeOK R p cert.upper cert.lower ∧
  (∀ loss ∈ cert.losses, RegionOK cert.upper cert.lower loss.good loss.region loss.target) ∧
  LostOK D R cert.lost cert.losses ∧
  eligibleCount D R + lowSum D + lowSum R ≤
    bound + allowedCount cert.lost + degreeSum D + cornerCount D R p
instance (D R : Fin n → Nat) (p : List Nat) (bound : Nat) (cert : CutBound n) :
    Decidable (CutBoundOK D R p bound cert) := inferInstanceAs (Decidable (_ ∧ _))

theorem cut_complement_identity (E : Graph (Fin n)) (A B : Fin n → Prop) :
    arcCount E + cut E (fun s => ¬A s) (fun t => ¬B t) =
    cut E A B + cut E (fun s => ¬A s) (fun _ => True) +
      cut E (fun _ => True) (fun t => ¬B t) := by
  have p := cut_source_partition E A (fun _ => True)
  have q := cut_target_partition E A B
  have r := cut_source_partition E A (fun t => ¬B t)
  rw [cut_total] at p
  omega

theorem cut_count_sound (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (lostRows : Rows n)
    (eligible : ∀ s t, bit (lostRows s) t → 2 ≤ D s ∧ 2 ≤ R t ∧ s ≠ t)
    (losing : ∀ E, Prescribed D R E → Agrees p E → ∀ s t,
      bit (lostRows s) t → ¬Guaranteed E s t)
    (numeric : eligibleCount D R + lowSum D + lowSum R ≤
      bound + allowedCount lostRows + degreeSum D + cornerCount D R p) :
    Upper D R p bound := by
  intro E valid agrees
  let A := fun s => 2 ≤ D s
  let B := fun t => 2 ≤ R t
  let L : Graph (Fin n) := fun s t => bit (lostRows s) t
  let F := fun s t => E s t ∧ A s ∧ B t
  let U := fun s t => A s ∧ B t ∧ s ≠ t
  have lost (s t) (h : L s t) : ¬Guaranteed E s t := losing E valid agrees s t h
  have lost_edge (s t) (h : L s t) : ¬E s t := by
    intro edge
    apply lost s t h
    intro c different
    exact ⟨1,direct_delivery (Ne.symm different) edge⟩
  have first := arcs_union (E := Indirect E) (F := L)
    (fun s t hi hl => lost s t hl hi.2.2)
  have second := arcs_union (E := fun s t => Indirect E s t ∨ L s t) (F := F) (by
    intro s t h hf
    rcases h with hi | hl
    · exact hi.2.1 hf.1
    · exact lost_edge s t hl hf.1)
  have within := arcs_mono (E := fun s t => (Indirect E s t ∨ L s t) ∨ F s t) (F := U) (by
    intro s t h
    rcases h with (hi | hl) | hf
    · have ho := live_outdegree valid.1 hi
      have hr := live_indegree hi
      rw [valid.2.1] at ho
      rw [valid.2.2] at hr
      exact ⟨ho,hr,hi.1⟩
    · have h := eligible s t hl
      exact ⟨h.1,h.2.1,h.2.2⟩
    · exact ⟨hf.2.1,hf.2.2,fun same => valid.1 s (same ▸ hf.1)⟩)
  have countL : arcCount L = allowedCount lostRows := arcCount_eq _
  have countU : arcCount U = eligibleCount D R := arcCount_eq _
  have countF : arcCount F = cut E A B := rfl
  have success : arcCount (Indirect E) = score E := rfl
  have inside : score E + allowedCount lostRows + cut E A B ≤ eligibleCount D R := by omega
  have total : arcCount E = degreeSum D := by
    rw [arc_rows]
    change ((List.finRange n).map (outdegree E)).sum = degreeSum D
    rw [show outdegree E = D from funext valid.2.1]
    rfl
  have lowout : cut E (fun s => ¬A s) (fun _ => True) = lowSum D := by
    rw [cut_out_rows]
    simp only [lowSum,A,valid.2.1]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s _
    by_cases h : 2 ≤ D s <;> simp [h]
  have lowin : cut E (fun _ => True) (fun t => ¬B t) = lowSum R := by
    rw [cut_in_columns]
    simp only [lowSum,B,valid.2.2]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    by_cases h : 2 ≤ R t <;> simp [h]
  have identity := cut_complement_identity E A B
  have corner : cornerCount D R p ≤ cut E (fun s => ¬A s) (fun t => ¬B t) := by
    have eqn : cornerCount D R p = cut (known p) (fun s => ¬A s) (fun t => ¬B t) := by
      calc
        _ = arcCount (fun s t => ¬2 ≤ D s ∧ ¬2 ≤ R t ∧ known p s t) := (arcCount_eq _).symm
        _ = _ := arcs_congr (fun _ _ => ⟨fun h => ⟨h.2.2,h.1,h.2.1⟩,
          fun h => ⟨h.2.1,h.2.2,h.1⟩⟩)
    rw [eqn]
    exact arcs_mono (fun s t h => ⟨(sandwich valid.1 agrees).1 s t h.1,h.2⟩)
  omega

theorem cut_bound_sound (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (cert : CutBound n) (checked : CutBoundOK D R p bound cert) : Upper D R p bound := by
  apply cut_count_sound D R p bound cert.lost
  · intro s t h
    have yes := checked.2.2.1 s t h
    exact ⟨yes.1,yes.2.1,yes.2.2.1⟩
  · intro E valid agrees s t h
    exact loss_sound valid agrees cert.upper cert.lower cert.losses checked.1 checked.2.1
      (checked.2.2.1 s t h).2.2.2
  · exact checked.2.2.2

#print axioms cut_bound_sound
end Delivery.RowPrefix
