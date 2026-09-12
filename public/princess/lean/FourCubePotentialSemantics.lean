import FourCubePotentialCertificate

namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality Princess.FiniteSubsetProfiles
open Princess.FiniteIdealCertificates

attribute [local irreducible] Princess.ProductCompression.iterateMap

def BoundedMask (mask : Nat) : Prop := ∀ j, mask.testBit j=true → j<64

theorem encoded_bounded (p : Bool) (A : Region Room) : BoundedMask (encodeColor p A) := by
  intro j hj
  unfold encodeColor at hj
  rw [selectedMask_bit] at hj
  obtain ⟨v,_,_,h⟩ := hj
  simp only [Nat.testBit_two_pow,decide_eq_true_eq] at h
  rw [← h]
  exact v.isLt

theorem cap_bounded (mask : Nat) : BoundedMask (mask &&& 18446744073709551615) := by
  intro j hj
  rw [Nat.testBit_and,Bool.and_eq_true] at hj
  have h : (2^64-1).testBit j=true := hj.2
  simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using h

theorem rawHood_bounded (mask : Nat) : BoundedMask (rawHood mask) := by
  intro j hj
  unfold rawHood at hj
  rw [selectedMask_bit] at hj
  obtain ⟨v,_,_,h⟩ := hj
  exact cap_bounded _ j h

theorem decoded_injective (a b : Nat) (ha : BoundedMask a) (hb : BoundedMask b)
    (eq : decoded a=decoded b) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j<64
  · have hp := congrFun eq ⟨j,h⟩
    change (a.testBit j=true)=(b.testBit j=true) at hp
    cases hab : a.testBit j <;> cases hbb : b.testBit j <;> simp_all
  · have hfa : a.testBit j=false := by
      cases hj : a.testBit j
      · rfl
      · exact False.elim (h (ha j hj))
    have hfb : b.testBit j=false := by
      cases hj : b.testBit j
      · rfl
      · exact False.elim (h (hb j hj))
    rw [hfa,hfb]

theorem reencode (p : Bool) (mask : Nat) (bounded : BoundedMask mask)
    (support : ∀ v, decoded mask v → color v=(if p then 1 else 0)) :
    encodeColor p (decoded mask)=mask :=
  decoded_injective _ _ (encoded_bounded _ _) bounded (encodeColor_correct p _ support)

theorem decoded_card (mask : Nat) : card (decoded mask)=countBits 64 mask := by
  rw [countBits_eq_maskCard]
  unfold card cardOn maskCard decoded
  apply List.countP_congr
  intro v _
  simp

theorem rawHood_correct (mask : Nat) : decoded (rawHood mask)=move adj (decoded mask) := by
  funext v
  apply propext
  unfold decoded rawHood
  rw [selectedMask_bit]
  simp only [List.mem_finRange,true_and]
  constructor
  · rintro ⟨u,hu,he⟩; exact ⟨u,hu,(neighbor_mask_correct u v).mp he⟩
  · rintro ⟨u,hu,he⟩; exact ⟨u,hu,(neighbor_mask_correct u v).mpr he⟩

def Closed (A : Region Room) : Prop :=
  ∀ u v : Room, (downMask v).testBit u.val=true → A v → A u

theorem tables_correct (p : Bool) (A : Region Room)
    (support : ∀ v, A v → color v=(if p then 1 else 0)) (closed : Closed A) :
    sizeTable (encodeColor p A)=card A ∧
      hoodTable (encodeColor p A)=rawHood (encodeColor p A) := by
  have checked : check down factsCheck ((colorRooms p).map Fin.val) 0=true := by
    cases p
    · exact facts_even_checked
    · exact facts_odd_checked
  have h := checker_sound p A factsCheck support closed checked
  have hpair : sizeTable (encodeColor p A)=countBits 64 (encodeColor p A) ∧
      hoodTable (encodeColor p A)=rawHood (encodeColor p A) := by
    simpa only [factsCheck,decide_eq_true_eq] using h
  rw [← decoded_card,encodeColor_correct p A support] at hpair
  exact hpair

theorem mask_subset (a b : Nat) (ha : BoundedMask a) (_hb : BoundedMask b)
    (subset : Subset (decoded a) (decoded b)) : a &&& b=a := by
  apply bitSubset_antisymm
  · intro j hj
    rw [Nat.testBit_and,Bool.and_eq_true] at hj
    exact hj.1
  · intro j hj
    have bound := ha j hj
    have next := subset ⟨j,bound⟩ hj
    simpa only [Nat.testBit_and,Bool.and_eq_true,decoded] using And.intro hj next

theorem encoded_transition (p : Bool) (A R : Region Room)
    (asupport : ∀ v, A v → color v=(if p then 1 else 0))
    (rsupport : ∀ v, R v → color v=(if p then 1 else 0))
    (aclosed : Closed A) (rclosed : Closed R) (subset : Subset R A)
    (budget : card A-card R≤8) :
    potential (encodeColor p A) ≤ charge (card A-card R) +
      potential (rawHood (encodeColor p R)) := by
  have checked : check down (sourceCheck p) ((colorRooms p).map Fin.val) 0=true := by
    cases p
    · exact transitions_even_checked
    · exact transitions_odd_checked
  have sources := checker_sound p A (sourceCheck p) asupport aclosed checked
  have transition := checker_sound p R (transitionCheck (encodeColor p A)) rsupport rclosed sources
  have sub : encodeColor p R &&& encodeColor p A=encodeColor p R := by
    apply mask_subset _ _ (encoded_bounded _ _) (encoded_bounded _ _)
    rw [encodeColor_correct p R rsupport,encodeColor_correct p A asupport]
    exact subset
  have h : encodeColor p R &&& encodeColor p A=encodeColor p R →
      sizeTable (encodeColor p A)-sizeTable (encodeColor p R)≤8 →
      potential (encodeColor p A) ≤ charge (sizeTable (encodeColor p A)-sizeTable (encodeColor p R)) +
        potential (hoodTable (encodeColor p R)) := by
    simpa only [transitionCheck,decide_eq_true_eq] using transition
  rw [(tables_correct p A asupport aclosed).1,(tables_correct p R rsupport rclosed).1,
    (tables_correct p R rsupport rclosed).2] at h
  exact h sub budget

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.encoded_transition
