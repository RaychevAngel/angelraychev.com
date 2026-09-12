import PathOddGeometry
import PathRankLower

/-! Physical odd-path cohorts and exact alternating-cap affine ranks. -/
namespace Princess.PathOddRank
open Princess.PathGeometry Princess.PathSweep Princess.PathLowerGeometry
open Princess.PathOddGeometry Princess.PathCohorts
open Princess.LadderCardinality Princess.CaptureRecurrence

noncomputable def stateRank {n : Nat} (p : Nat) (B : Region (Fin n)) : Nat :=
  if card B = 0 then 0 else 2 * card B + if p % 2 = 0 then 1 else 0

theorem stateRank_floor {n : Nat} (p : Nat) (B : Region (Fin n)) :
    stateRank p B / 2 = card B := by
  unfold stateRank
  split <;> (try split) <;> omega

theorem move_positive {n : Nat} (hn : 2 ≤ n) (R : Region (Fin n))
    (hne : 0 < card R) : 0 < card (Princess.move adj R) := by
  obtain ⟨v, hv⟩ := (card_pos R).mp hne
  obtain ⟨w, he⟩ := no_dead_ends hn v
  exact (card_pos _).mpr ⟨w, v, hv, he⟩

theorem physical_step {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (B S : Region (Fin n)) (p : Nat) (hp : p < 2)
    (parity : ∀ v, B v → (v.val + 1) % 2 = p) :
    PathRankLower.step (n + (p + 1) % 2) (stateRank p B) (card S) ≤
      stateRank (p + 1) (next adj B S) := by
  let R : Region (Fin n) := fun v => B v ∧ ¬ S v
  have remove := probes_remove_at_most B S
  change card B ≤ card R + card S at remove
  change PathRankLower.step (n + (p + 1) % 2) (stateRank p B) (card S) ≤
    stateRank (p + 1) (Princess.move adj R)
  unfold PathRankLower.step
  split
  · omega
  · rename_i survive
    rw [stateRank_floor] at survive
    have positive : 0 < card R := by omega
    have nextpos := move_positive hn R positive
    have bpos : card B ≠ 0 := by omega
    simp only [stateRank, bpos, Nat.ne_of_gt nextpos, if_false]
    by_cases hp0 : p = 0
    · subst p
      have small : ∀ v, R v → v.val % 2 = 1 := by
        intro v hv
        have h := parity v hv.1
        omega
      have grow := odd_small_expands hn ho R small positive
      simp only [Nat.zero_mod, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ite_true, ite_false]
      have minle := Nat.min_le_right (n + 1) (2 * card B + 1 - 2 * card S + 1)
      omega
    · have hp1 : p = 1 := by omega
      subst p
      have grow := odd_neighborhood_lower hn ho R
      simp only [Nat.reduceMod, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero]
      have minl := Nat.min_le_left n (2 * card B - 2 * card S + 1)
      have minr := Nat.min_le_right n (2 * card B - 2 * card S + 1)
      simp only [Nat.min_def] at grow
      split at grow <;> omega

noncomputable def rank {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat) : Nat :=
  stateRank (p + t) (belief probes p t)

noncomputable def allocation {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat) : Nat :=
  card (shots probes p t)

theorem rank_initial {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (p : Nat) (hp : p < 2) :
    rank probes p 0 = n + p := by
  change stateRank (p + 0) (fullParity (n := n) p) = n + p
  unfold stateRank
  rw [full_parity_card n p hp]
  split <;> (try split) <;> omega

theorem rank_step {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2) :
    PathRankLower.step (n + (p + t + 1) % 2) (rank probes p t) (allocation probes p t) ≤
      rank probes p (t + 1) := by
  have h := physical_step hn ho (belief probes p t) (shots probes p t)
    ((p + t) % 2) (by omega) (belief_parity probes p t hp)
  have stateEq : stateRank ((p + t) % 2) (belief probes p t) = rank probes p t := by
    simp only [stateRank, rank, Nat.mod_mod]
  have nextEq : stateRank ((p + t) % 2 + 1)
      (next adj (belief probes p t) (shots probes p t)) = rank probes p (t + 1) := by
    rw [← belief_step probes p t hp]
    simp only [stateRank, rank]
    have par : ((p + t) % 2 + 1) % 2 = (p + (t + 1)) % 2 := by omega
    rw [par]
  rw [stateEq, nextEq] at h
  have par : ((p + t) % 2 + 1) % 2 = (p + t + 1) % 2 := by omega
  simpa only [par, allocation] using h

theorem step_cap_mono (c d u p : Nat) (h : c ≤ d) :
    PathRankLower.step c u p ≤ PathRankLower.step d u p := by
  unfold PathRankLower.step
  split
  · omega
  · simp only [Nat.min_def]
    split <;> split <;> omega

theorem rank_step_constant {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2) :
    PathRankLower.step n (rank probes p t) (allocation probes p t) ≤
      rank probes p (t + 1) :=
  Nat.le_trans (step_cap_mono _ _ _ _ (by omega)) (rank_step hn ho probes p t hp)

theorem counter_below_rank {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2) :
    PathRankLower.counter n (allocation probes p) t ≤ rank probes p t := by
  apply PathRankLower.counter_dominated n (allocation probes p) (rank probes p)
  · rw [rank_initial hn ho probes p hp]; omega
  · exact fun k => rank_step_constant hn ho probes p k hp

theorem empty_rank {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat)
    (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    rank probes p t = 0 := by
  have hc := empty_card (belief probes p t) (full_empty_implies_cohort probes p t empty)
  simp only [rank, stateRank, hc, if_true]

theorem empty_counter {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (p t : Nat) (hp : p < 2)
    (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    PathRankLower.counter n (allocation probes p) t = 0 := by
  have bound := counter_below_rank hn ho probes p t hp
  rw [empty_rank probes p t empty] at bound
  omega

/-- The ordinary potential gives the exact formula outside its single equality
slice: odd n, even m, and positive residue m-1. -/
theorem nonexceptional_formula (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hnm : m < n) (ho : n % 2 = 1)
    (ordinary : m % 2 ≠ 0 ∨ (n - 3) % (2 * m - 1) + 1 ≠ m - 1)
    (probes : Nat → Region (Fin n)) (budget : ∀ t, card (probes t) ≤ m)
    (t : Nat) (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    PathUpperArithmetic.correctedCeiling n m ≤ t := by
  have left := empty_counter hn ho probes 0 t (by omega) empty
  have right := empty_counter hn ho probes 1 t (by omega) empty
  have alloc : ∀ k, allocation probes 0 k + allocation probes 1 k ≤ m := by
    intro k
    simpa only [allocation, shots_partition] using budget k
  obtain ⟨hr, hrd, hnq⟩ := PathUpperArithmetic.canonical_parameters n m hm hnm
  have ammo := PathRankLower.captured_ammunition n m _ _ (by omega) alloc t left right
  have lower := PathRankLower.residue_lower n m (2 * m - 1)
    ((n - 3) / (2 * m - 1)) ((n - 3) % (2 * m - 1) + 1) t hm
    (by omega) hr hrd hnq ammo
  have counts : PathRankLower.lowerCount m ((n - 3) / (2 * m - 1))
      ((n - 3) % (2 * m - 1) + 1) =
      PathUpperArithmetic.sweepCount n m ((n - 3) / (2 * m - 1))
      ((n - 3) % (2 * m - 1) + 1) := by
    unfold PathRankLower.lowerCount PathUpperArithmetic.sweepCount PathUpperArithmetic.bothEven
    split <;> split <;> omega
  rw [counts, PathUpperArithmetic.canonical_sweepCount_eq_correctedCeiling n m hm hnm] at lower
  exact lower


end Princess.PathOddRank
#print axioms Princess.PathOddRank.physical_step
#print axioms Princess.PathOddRank.empty_counter
