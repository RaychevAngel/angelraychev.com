import PathCohorts
import PathRankLower

/-! Arbitrary physical schedules on even paths dominate the exact affine
counter. The history bit records a zero-growth proper neighborhood, whose
missing endpoints force growth on the following surviving turn. -/
namespace Princess.PathEvenRank
open Princess.PathGeometry Princess.PathSweep Princess.PathLowerGeometry
open Princess.PathCohorts Princess.LadderCardinality Princess.CaptureRecurrence

noncomputable def newMark {n : Nat} (R : Region (Fin n)) : Nat := by
  classical
  exact if 0 < card (Princess.move adj R) ∧ card (Princess.move adj R) = card R ∧
      card R < n / 2 then 1 else 0

def Valid {n : Nat} (B : Region (Fin n)) (z : Nat) : Prop :=
  z ≤ 1 ∧ (card B = 0 → z = 0) ∧ (z = 1 → endpointless B)

theorem valid_zero {n : Nat} (B : Region (Fin n)) : Valid B 0 := by
  exact ⟨by omega, fun _ => rfl, by intro h; omega⟩

theorem newMark_valid {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (R : Region (Fin n)) : Valid (Princess.move adj R) (newMark R) := by
  classical
  unfold newMark
  split
  · rename_i h
    exact ⟨by omega, by intro hz; omega,
      fun _ => even_zero_endpointless hn he R h.2.1 h.2.2⟩
  · exact valid_zero _

theorem physical_step {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (B S : Region (Fin n)) (z : Nat) (hz : Valid B z) :
    PathRankLower.step n (2 * card B + z) (card S) ≤
      2 * card (next adj B S) + newMark (fun v => B v ∧ ¬ S v) := by
  classical
  let R : Region (Fin n) := fun v => B v ∧ ¬ S v
  have remove := probes_remove_at_most B S
  have grow := even_neighborhood_nonshrinking he R
  change card B ≤ card R + card S at remove
  change PathRankLower.step n (2 * card B + z) (card S) ≤
      2 * card (Princess.move adj R) + newMark R
  unfold PathRankLower.step
  split
  · omega
  · rename_i survive
    have positive : 0 < card R := by have := hz.1; omega
    have floor : card B = (2 * card B + z) / 2 := by have := hz.1; omega
    by_cases marked : z = 1
    · have hend : endpointless R := fun v hv => hz.2.2 marked v hv.1
      have strict := even_endpointless_expands hn he R positive hend
      have hmin := Nat.min_le_right n (2 * card B + z - 2 * card S + 1)
      omega
    · have zero : z = 0 := by have := hz.1; omega
      by_cases equal : card (Princess.move adj R) = card R
      · by_cases proper : card R < n / 2
        · have mark : newMark R = 1 := by simp [newMark, equal, positive, proper]
          rw [mark]
          have hmin := Nat.min_le_right n (2 * card B + z - 2 * card S + 1)
          omega
        · have hmin := Nat.min_le_left n (2 * card B + z - 2 * card S + 1)
          omega
      · have hmin := Nat.min_le_right n (2 * card B + z - 2 * card S + 1)
        omega

noncomputable def mark {n : Nat} (probes : Nat → Region (Fin n)) (p : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => newMark (fun v => belief probes p t v ∧ ¬ shots probes p t v)

noncomputable def rank {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat) : Nat :=
  2 * card (belief probes p t) + mark probes p t

noncomputable def allocation {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat) : Nat :=
  card (shots probes p t)

theorem mark_valid {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2) :
    Valid (belief probes p t) (mark probes p t) := by
  cases t with
  | zero => exact valid_zero _
  | succ t =>
      rw [belief_step probes p t hp]
      exact newMark_valid hn he _

theorem rank_initial {n : Nat} (he : n % 2 = 0)
    (probes : Nat → Region (Fin n)) (p : Nat) (hp : p < 2) : rank probes p 0 = n := by
  change 2 * card (fullParity (n := n) p) + 0 = n
  rw [full_parity_card n p hp]
  omega

theorem rank_step {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2) :
    PathRankLower.step n (rank probes p t) (allocation probes p t) ≤
      rank probes p (t + 1) := by
  have h := physical_step hn he (belief probes p t) (shots probes p t)
    (mark probes p t) (mark_valid hn he probes p t hp)
  simpa only [rank, allocation, mark, belief_step probes p t hp] using h

theorem counter_below_rank {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2) :
    PathRankLower.counter n (allocation probes p) t ≤ rank probes p t := by
  apply PathRankLower.counter_dominated n (allocation probes p) (rank probes p)
  · rw [rank_initial he probes p hp]
    exact Nat.le_refl n
  · exact fun k => rank_step hn he probes p k hp

theorem empty_counter {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2)
    (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    PathRankLower.counter n (allocation probes p) t = 0 := by
  have cohort := full_empty_implies_cohort probes p t empty
  have hc := empty_card (belief probes p t) cohort
  have hz := (mark_valid hn he probes p t hp).2.1 hc
  have bound := counter_below_rank hn he probes p t hp
  simp only [rank, hc, hz] at bound
  omega

/-- Every actual schedule clearing an even path takes at least the historical
closed-form number of days; no restriction to sweeps is assumed. -/
theorem path_even_lower (n m : Nat) (hn : 2 ≤ n) (hm : 1 ≤ m) (he : n % 2 = 0)
    (probes : Nat → Region (Fin n)) (budget : ∀ t, card (probes t) ≤ m)
    (t : Nat) (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    PathUpper.turns n m ≤ t := by
  have left := empty_counter hn he probes 0 t (by omega) empty
  have right := empty_counter hn he probes 1 t (by omega) empty
  have alloc : ∀ k, allocation probes 0 k + allocation probes 1 k ≤ m := by
    intro k
    simpa only [allocation, shots_partition] using budget k
  unfold PathUpper.turns
  split
  · exact PathRankLower.captured_positive n (allocation probes 0) t (by omega) left
  · rename_i hnm
    split
    · rename_i hm1
      subst m
      split
      · rename_i hn2
        subst n
        exact PathRankLower.captured_single_edge _ _ t alloc left right
      · exact PathRankLower.captured_one_probe n _ _ t (by omega) alloc left right
    · exact PathRankLower.captured_even_formula n m _ _ t (by omega) (by omega)
        he alloc left right

end Princess.PathEvenRank
#print axioms Princess.PathEvenRank.path_even_lower
