import ThreeCubeTimeColors
import ThreeCubeTimeCounter
import ThreeCubeTimeIsoperimetry

namespace Princess.ThreeCubeTimeClassification
open Princess.ThreeCubeTrap Princess.ThreeCubeLower Princess.LadderCardinality
open Princess.CaptureRecurrence


theorem profile_same : ∀ p : Fin 2, ∀ k : Fin 15,
    ThreeCubeTimeProfiles.profile p.val k.val = ThreeCubeTimeCounter.profile p.val k.val := by
  decide

theorem next_profile (B S : Region Room) (p : Nat) (hp : p < 2) :
    ThreeCubeTimeCounter.profile p (card (slice B p) - card (slice S p)) ≤
      card (slice (next adj B S) (1 - p)) := by
  let R : Region Room := fun v => slice B p v ∧ ¬ slice S p v
  have remove := probes_remove_at_most (slice B p) (slice S p)
  change card (slice B p) ≤ card R + card (slice S p) at remove
  have cap : card R ≤ if p = 0 then 14 else 13 := by
    have sub := card_mono R (slice B p) (fun _ hv => hv.1)
    by_cases hp0 : p = 0
    · subst p; have := even_le B; simp only [ite_true]; omega
    · have hp1 : p = 1 := by omega
      subst p; have := odd_le B; simp only [ite_false, Nat.reduceEqDiff]; omega
  have grow := ThreeCubeTimeProfiles.profile_lower p hp R (fun _ hv => hv.1.2)
  have monotone := ThreeCubeTimeProfiles.profile_monotone p
    (card (slice B p) - card (slice S p)) (card R) hp (by omega) cap
  have kbound : card (slice B p) - card (slice S p) < 15 := by
    split at cap <;> omega
  have same := profile_same ⟨p, hp⟩ ⟨card (slice B p) - card (slice S p), kbound⟩
  change ThreeCubeTimeProfiles.profile p (card (slice B p) - card (slice S p)) =
    ThreeCubeTimeCounter.profile p (card (slice B p) - card (slice S p)) at same
  rw [same] at monotone
  have result := Nat.le_trans monotone grow
  rw [next_slice B S p hp]
  exact result

noncomputable def stateRank (c : Fin 5) (B : Region Room) : Nat :=
  ThreeCubeTimeCounter.rank c (card (slice B 0)) (card (slice B 1))

theorem stateRank_step (c : Fin 5) (B S : Region Room)
    (budget : atMost (ThreeCubeTimeCounter.budget c) S) :
    stateRank c B ≤ 1 + stateRank c (next adj B S) := by
  have na := next_profile B S 1 (by decide)
  have nb := next_profile B S 0 (by decide)
  simp only [Nat.reduceSub] at na nb
  have splitS := slice_partition S
  exact ThreeCubeTimeCounter.physical_step c _ _ _ _ _ _
    (even_le B) (odd_le B) (even_le _) (odd_le _)
    (by change card S ≤ _ at budget; omega) na nb

theorem stateRank_initial (c : Fin 5) :
    stateRank c (fun _ => True) = ThreeCubeTimeCounter.expected c := by
  unfold stateRank
  rw [full_even, full_odd, ThreeCubeTimeCounter.rank_initial]

theorem stateRank_empty (c : Fin 5) (B : Region Room) (h : Empty B) :
    stateRank c B = 0 := by
  unfold stateRank
  rw [empty_card (slice B 0) (fun v hv => h v hv.1),
    empty_card (slice B 1) (fun v hv => h v hv.1), ThreeCubeTimeCounter.rank_empty]

theorem rank_schedule (c : Fin 5) (probes : Nat → Region Room)
    (budget : ∀ i, atMost (ThreeCubeTimeCounter.budget c) (probes i)) (t : Nat) :
    ThreeCubeTimeCounter.expected c ≤
      t + stateRank c (Princess.possible adj (fun _ => True) probes t) := by
  induction t with
  | zero => simp only [Princess.possible, stateRank_initial, Nat.zero_add]; omega
  | succ t ih =>
      have hs := stateRank_step c (Princess.possible adj (fun _ => True) probes t)
        (probes t) (budget t)
      change ThreeCubeTimeCounter.expected c ≤
        t + 1 + stateRank c (next adj (Princess.possible adj (fun _ => True) probes t) (probes t))
      omega

theorem actual_case_lower (c : Fin 5) (probes : Nat → Region Room)
    (budget : ∀ i, atMost (ThreeCubeTimeCounter.budget c) (probes i))
    (t : Nat) (capture : Princess.GuaranteesAt adj (fun _ => True) probes t) :
    ThreeCubeTimeCounter.expected c ≤ t + 1 := by
  have empty := (Princess.guarantees_iff_next_empty adj (fun _ => True) probes
    no_dead_ends t).mp capture
  have bound := rank_schedule c probes budget (t + 1)
  rw [stateRank_empty c _ empty] at bound
  omega

theorem two_day_lower (m : Nat) (hm : m < 27) (probes : Nat → Region Room)
    (budget : ∀ i, atMost m (probes i)) (t : Nat)
    (capture : Princess.GuaranteesAt adj (fun _ => True) probes t) : 2 ≤ t + 1 := by
  by_cases hz : t = 0
  · subst t
    have covers := (Princess.guarantees_iff_belief_covered adj (fun _ => True) probes 0).mp capture
    have sub : Subset (fun _ : Room => True) (probes 0) := fun v _ => covers v True.intro
    have count := card_mono _ _ sub
    rw [full_card] at count
    have b := budget 0
    change card (probes 0) ≤ m at b
    omega
  · omega

theorem actual_lower (m : Nat) (hm : 5 ≤ m) (probes : Nat → Region Room)
    (budget : ∀ i, atMost m (probes i)) (t : Nat)
    (capture : Princess.GuaranteesAt adj (fun _ => True) probes t) :
    ThreeCubeTimeUpper.turns m ≤ t + 1 := by
  unfold ThreeCubeTimeUpper.turns
  split
  · omega
  · split
    · have h := actual_case_lower (0 : Fin 5) probes (by
        intro i; have h := budget i; change card (probes i) ≤ m at h
        change card (probes i) ≤ 5; omega)
        t capture
      exact h
    · split
      · have h := actual_case_lower (1 : Fin 5) probes (by
          intro i; have h := budget i; change card (probes i) ≤ m at h
          change card (probes i) ≤ 6; omega) t capture
        exact h
      · split
        · have h := actual_case_lower (2 : Fin 5) probes (by
            intro i; have h := budget i; change card (probes i) ≤ m at h
            change card (probes i) ≤ 8; omega) t capture
          exact h
        · split
          · have h := actual_case_lower (3 : Fin 5) probes (by
              intro i; have h := budget i; change card (probes i) ≤ m at h
              change card (probes i) ≤ 11; omega) t capture
            exact h
          · split
            · have h := actual_case_lower (4 : Fin 5) probes (by
                intro i; have h := budget i; change card (probes i) ≤ m at h
                change card (probes i) ≤ 12; omega) t capture
              exact h
            · split
              · exact two_day_lower m (by omega) probes budget t capture
              · omega

theorem exact_minimum (m : Nat) (hm : 5 ≤ m) :
    (∃ probes : Nat → Region Room, (∀ i, atMost m (probes i)) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes (ThreeCubeTimeUpper.turns m - 1)) ∧
    (∀ probes : Nat → Region Room, (∀ i, atMost m (probes i)) → ∀ t,
      Princess.GuaranteesAt adj (fun _ => True) probes t →
        ThreeCubeTimeUpper.turns m ≤ t + 1) :=
  ⟨ThreeCubeTimeUpper.actual_upper m hm, actual_lower m hm⟩


theorem winning_later (m t : Nat) (B : Region Room)
    (hw : winning adj (atMost m) t B) (extra : Nat) :
    winning adj (atMost m) (t + extra) B := by
  induction extra with
  | zero => exact hw
  | succ extra ih =>
      have inhabited : ∃ S : Region Room, atMost m S := by
        refine ⟨fun _ => False, ?_⟩
        change card (fun _ : Room => False) ≤ m
        classical
        simp [card, cardOn]
      exact winning_succ adj (atMost m) inhabited (t + extra) B ih

/-- Complete feasibility and minimum-time statement for every natural budget.
The returned schedule respects the budget on every round, not just before capture. -/
theorem can_capture_iff (m t : Nat) :
    (∃ probes : Nat → Region Room, (∀ i, atMost m (probes i)) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes t) ↔
    5 ≤ m ∧ ThreeCubeTimeUpper.turns m ≤ t + 1 := by
  constructor
  · rintro ⟨probes, budget, capture⟩
    have feasible : 5 ≤ m := (feasible_iff_five_le m).mp
      ⟨t, probes, fun i _ => budget i, capture⟩
    exact ⟨feasible, actual_lower m feasible probes budget t capture⟩
  · rintro ⟨hm, bound⟩
    have hw := winning_later m (ThreeCubeTimeUpper.turns m) (fun _ : Room => True)
      (ThreeCubeTimeUpper.winning_upper m hm) (t + 1 - ThreeCubeTimeUpper.turns m)
    have heq : ThreeCubeTimeUpper.turns m + (t + 1 - ThreeCubeTimeUpper.turns m) = t + 1 := by omega
    rw [heq] at hw
    obtain ⟨probes, budget, empty⟩ := ThreeCubeTimeUpper.winning_schedule_all m (t + 1) _ hw
    exact ⟨probes, budget,
      (Princess.guarantees_iff_next_empty adj (fun _ => True) probes no_dead_ends t).mpr empty⟩

end Princess.ThreeCubeTimeClassification

#print axioms Princess.ThreeCubeTimeClassification.actual_lower
#print axioms Princess.ThreeCubeTimeClassification.exact_minimum

#print axioms Princess.ThreeCubeTimeClassification.can_capture_iff
