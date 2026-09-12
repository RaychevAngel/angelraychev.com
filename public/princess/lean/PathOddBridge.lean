import PathOddRank
import PathOddRankLower

/-! The phase-counter lower game is a relaxation of every physical schedule on
an odd path. Phase zero starts in the larger parity class. -/
namespace Princess.PathOddBridge
open Princess.PathGeometry Princess.PathCohorts Princess.PathOddRank
open Princess.LadderCardinality Princess.CaptureRecurrence

/-- The physical parity label p and the abstract phase label add to one. -/
theorem cap_parity (n phase p t : Nat) (hphase : phase + p = 1) :
    PathOddRankLower.phaseCap n phase t = n + (p + t) % 2 := by
  unfold PathOddRankLower.phaseCap
  split <;> omega

theorem phase_counter_below {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (phase p t : Nat) (hphase : phase + p = 1) :
    PathOddRankLower.phaseCounter n phase (allocation probes p) t ≤ rank probes p t := by
  have hp : p < 2 := by omega
  induction t with
  | zero =>
      rw [PathOddRankLower.phaseCounter, cap_parity n phase p 0 hphase,
        rank_initial hn ho probes p hp]
      omega
  | succ t ih =>
      rw [PathOddRankLower.phaseCounter, cap_parity n phase p (t + 1) hphase]
      exact Nat.le_trans (PathRankLower.step_mono ih)
        (by simpa only [Nat.add_assoc] using rank_step hn ho probes p t hp)

theorem empty_phase_counter {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (phase p t : Nat) (hphase : phase + p = 1)
    (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    PathOddRankLower.phaseCounter n phase (allocation probes p) t = 0 := by
  have bound := phase_counter_below hn ho probes phase p t hphase
  rw [empty_rank probes p t empty] at bound
  omega

theorem exceptional_formula (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hnm : m < n) (ho : n % 2 = 1) (hme : m % 2 = 0)
    (hre : (n - 3) % (2 * m - 1) + 1 = m - 1)
    (probes : Nat → Region (Fin n)) (budget : ∀ t, card (probes t) ≤ m)
    (t : Nat) (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    PathUpperArithmetic.correctedCeiling n m ≤ t := by
  let blocks := (n - 3) / (2 * m - 1)
  obtain ⟨hr, hrd, hnq⟩ := PathUpperArithmetic.canonical_parameters n m hm hnm
  have hnshape : n = blocks * (2 * m - 1) + m + 1 := by
    dsimp [blocks]
    omega
  have hb : blocks % 2 = 0 := by
    have hmod := congrArg (fun x => x % 2) hnshape
    have hdmod : (2 * m - 1) % 2 = 1 := by omega
    simp only [Nat.add_mod, Nat.mul_mod, ho, hme, hdmod, Nat.mul_one,
      Nat.mod_mod, Nat.add_zero] at hmod
    omega
  have alloc : ∀ k, allocation probes 1 k + allocation probes 0 k ≤ m := by
    intro k
    have h := shots_partition probes k
    have b := budget k
    change card (shots probes 1 k) + card (shots probes 0 k) ≤ m
    omega
  have left := PathOddRank.empty_counter hn ho probes 1 t (by omega) empty
  have right := PathOddRank.empty_counter hn ho probes 0 t (by omega) empty
  have ammo := PathRankLower.captured_ammunition n m _ _ (by omega) alloc t left right
  have lower := PathRankLower.residue_lower n m (2 * m - 1)
    blocks ((n - 3) % (2 * m - 1) + 1) t hm
    (by omega) hr hrd hnq ammo
  have weak : 2 * blocks + 1 ≤ t := by
    unfold PathRankLower.lowerCount at lower
    split at lower <;> omega
  have strong : 2 * blocks + 2 ≤ t := by
    by_cases h : 2 * blocks + 2 ≤ t
    · exact h
    have ht : t = 2 * blocks + 1 := by omega
    have lc := empty_phase_counter hn ho probes 0 1 t (by omega) empty
    have rc := empty_phase_counter hn ho probes 1 0 t (by omega) empty
    rw [ht] at lc rc
    exact False.elim (PathOddRankLower.odd_exception_impossible m blocks
      (2 * m - 1) n _ _ hm hme hb (by omega) hnshape alloc lc rc)
  have formula : PathUpperArithmetic.correctedCeiling n m = 2 * blocks + 2 := by
    rw [← PathUpperArithmetic.canonical_sweepCount_eq_correctedCeiling n m hm hnm]
    unfold PathUpperArithmetic.sweepCount PathUpperArithmetic.bothEven
    split <;> omega
  rw [formula]
  exact strong

theorem path_odd_lower (n m : Nat) (hn : 2 ≤ n) (hm : 1 ≤ m) (ho : n % 2 = 1)
    (probes : Nat → Region (Fin n)) (budget : ∀ t, card (probes t) ≤ m)
    (t : Nat) (empty : Empty (Princess.possible adj (fun _ => True) probes t)) :
    PathUpper.turns n m ≤ t := by
  have left := PathOddRank.empty_counter hn ho probes 0 t (by omega) empty
  have right := PathOddRank.empty_counter hn ho probes 1 t (by omega) empty
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
      have hn3 : 3 ≤ n := by omega
      simp only [show n ≠ 2 by omega, if_false]
      exact PathRankLower.captured_one_probe n _ _ t hn3 alloc left right
    · rename_i hm1
      by_cases ordinary : m % 2 ≠ 0 ∨ (n - 3) % (2 * m - 1) + 1 ≠ m - 1
      · exact nonexceptional_formula n m hn (by omega) (by omega) ho
          ordinary probes budget t empty
      · exact exceptional_formula n m hn (by omega) (by omega) ho
          (by omega) (by omega) probes budget t empty

end Princess.PathOddBridge
#print axioms Princess.PathOddBridge.empty_phase_counter

#print axioms Princess.PathOddBridge.path_odd_lower
