import SquareCompressionFourEnergyData

namespace Princess.SquareCompressionFour
open Princess.ProductCompression Princess.LadderCardinality Princess.FiniteSubsetProfiles

noncomputable def energy (pair : Fin 3) (A : Region Room) : Nat :=
  weightedOn (List.finRange 16) (pairWeight pair) A

theorem weightedBits_correct (pair : Fin 3) (mask : Nat) :
    weightedBits pair mask = energy pair (decoded mask) := by
  classical
  unfold weightedBits energy weightedOn decoded
  congr 1
  apply List.map_congr_left
  intro v _
  by_cases h : mask.testBit v.val = true <;> simp [h]

theorem checked_energy (dir p : Bool) (pair : Fin 3) (A : Region Room)
    (support : ∀ v, A v → color v = (if p then 1 else 0)) :
    energy pair (cmap dir A) ≤ energy pair A ∧
    (energy pair (cmap dir A) = energy pair A → cmap dir A = A) := by
  classical
  have h := checkSubsets_sound (energyCheck dir) (rooms p) 0
    (fun v => decide (A v)) (energy_checked dir p)
  change energyCheck dir (0 ||| encode p A) = true at h
  rw [Nat.zero_or] at h
  have properties : ∀ pair : Fin 3,
      weightedBits pair (cBits dir (encode p A)) ≤ weightedBits pair (encode p A) ∧
      (weightedBits pair (cBits dir (encode p A)) = weightedBits pair (encode p A) →
        cBits dir (encode p A) = encode p A) := by
    simpa only [energyCheck,decide_eq_true_eq] using h
  have hp := properties pair
  have represent := encode_correct p A support
  simp only [weightedBits_correct,cBits_correct,represent] at hp
  constructor
  · exact hp.1
  · intro he
    have heq := congrArg decoded (hp.2 he)
    simpa only [cBits_correct,represent] using heq

theorem energy_slices (pair : Fin 3) (A : Region Room) :
    energy pair A = energy pair (slice A false) + energy pair (slice A true) := by
  have h := weightedOn_split (List.finRange 16) (pairWeight pair) A (fun v => color v = 0)
  have other : weightedOn (List.finRange 16) (pairWeight pair)
      (fun v => A v ∧ ¬ color v = 0) = energy pair (slice A true) := by
    apply weightedOn_congr
    intro v _
    have hc := color_bound v
    change (A v ∧ ¬ color v = 0) ↔ (A v ∧ color v = 1)
    constructor
    · intro hv; exact ⟨hv.1,by omega⟩
    · intro hv; exact ⟨hv.1,by omega⟩
  change energy pair A = energy pair (slice A false) + _ at h
  rwa [other] at h

theorem cmap_energy (dir : Bool) (pair : Fin 3) :
    EnergyGood (ofCompression (compression dir)) (energy pair) := by
  intro A
  have h0 := checked_energy dir false pair (slice A false) (fun _ h => h.2)
  have h1 := checked_energy dir true pair (slice A true) (fun _ h => h.2)
  have e0 := energy_slices pair A
  have e1 := energy_slices pair (cmap dir A)
  rw [← cmap_slice,← cmap_slice] at e1
  constructor
  · change energy pair (cmap dir A) ≤ energy pair A
    omega
  · intro he
    change energy pair (cmap dir A) = energy pair A at he
    have fix0 := h0.2 (by omega)
    have fix1 := h1.2 (by omega)
    rw [cmap_slice] at fix0 fix1
    funext v
    apply propext
    have hc := color_bound v
    by_cases hv : color v = 0
    · have h := congrFun fix0 v
      simpa [slice,hv,ofCompression,compression] using Eq.to_iff h
    · have hv1 : color v = 1 := by omega
      have h := congrFun fix1 v
      simpa [slice,hv1,ofCompression,compression] using Eq.to_iff h

end Princess.SquareCompressionFour
#print axioms Princess.SquareCompressionFour.cmap_energy
