import ThreeCubeTimeProfiles

/-! Interpretation of the finite subset profile certificates as lower bounds
for the neighborhoods of arbitrary physical same-parity room sets. -/
namespace Princess.ThreeCubeTimeProfiles
open Princess.ThreeCubeTrap Princess.ThreeCubeLower
open Princess.LadderCardinality Princess.CaptureRecurrence
open Princess.FiniteSubsetProfiles

theorem rooms_eq_filter : ∀ p : Fin 2,
    rooms p.val = (List.finRange 27).filter (fun v => decide (color v = p.val)) := by decide

theorem supported_count (p : Nat) (hp : p < 2) (B : Region Room)
    (mono : ∀ v, B v → color v = p) : cardOn (rooms p) B = card B := by
  classical
  rw [rooms_eq_filter ⟨p, hp⟩]
  unfold cardOn card
  rw [List.countP_filter]
  apply List.countP_congr
  intro v _
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨And.left, fun h => ⟨h, mono v h⟩⟩

theorem supported_mask (p : Nat) (hp : p < 2) (B : Region Room)
    (mono : ∀ v, B v → color v = p) :
    maskCard 27 (selectedMask neighborMask (fun v => @decide (B v) (Classical.propDecidable _))
      (rooms p)) = card (Princess.move adj B) := by
  classical
  unfold maskCard card cardOn
  apply List.countP_congr
  intro v _
  rw [selectedMask_bit]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨u, _, hu, hadj⟩
    exact ⟨u, hu, (mask_adjacency u v).mp hadj⟩
  · rintro ⟨u, hu, hadj⟩
    exact ⟨u, (rooms_membership ⟨p, hp⟩ u).mpr (mono u hu), hu,
      (mask_adjacency u v).mpr hadj⟩

theorem profile_lower (p : Nat) (hp : p < 2) (B : Region Room)
    (mono : ∀ v, B v → color v = p) :
    profile p (card B) ≤ card (Princess.move adj B) := by
  classical
  have checked : checkAll 27 neighborMask (profile p) (rooms p) 0 0 = true := by
    by_cases h : p = 0
    · subst p; exact even_profile_checked
    · have h : p = 1 := by omega
      subst p; exact odd_profile_checked
  have h := checkAll_sound 27 neighborMask (profile p) (rooms p) 0 0
    (fun v => decide (B v)) checked
  rw [Nat.zero_add, Nat.zero_or, selectedCount_eq, supported_count p hp B mono,
    supported_mask p hp B mono] at h
  exact h

theorem profile_monotone_checked : ∀ p : Fin 2, ∀ a b : Fin 15,
    a.val ≤ b.val → b.val ≤ (if p.val = 0 then 14 else 13) →
    profile p.val a.val ≤ profile p.val b.val := by decide

theorem profile_monotone (p a b : Nat) (hp : p < 2) (hab : a ≤ b)
    (hb : b ≤ if p = 0 then 14 else 13) : profile p a ≤ profile p b := by
  have hb15 : b < 15 := by split at hb <;> omega
  exact profile_monotone_checked ⟨p, hp⟩ ⟨a, by omega⟩ ⟨b, hb15⟩ hab hb

end Princess.ThreeCubeTimeProfiles
#print axioms Princess.ThreeCubeTimeProfiles.profile_lower
