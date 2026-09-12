import SquareCompressionFourData

namespace Princess.SquareCompressionFour
open Princess.LadderCardinality Princess.CaptureRecurrence
open Princess.FiniteSubsetProfiles

theorem checked_properties (dir p : Bool) (A : Region Room)
    (support : ∀ v, A v → color v = (if p then 1 else 0)) :
    card (cmap dir A) = card A ∧
    Subset (move adj (cmap dir A)) (cmap dir (move adj A)) ∧
    cmap dir (cmap dir A) = cmap dir A := by
  classical
  have h := checkSubsets_sound (localCheck dir) (rooms p) 0
    (fun v => decide (A v)) (checked dir p)
  change localCheck dir (0 ||| encode p A) = true at h
  rw [Nat.zero_or] at h
  have properties : countBits 16 (cBits dir (encode p A)) = countBits 16 (encode p A) ∧
      (hood (cBits dir (encode p A)) &&& cBits dir (hood (encode p A))) =
        hood (cBits dir (encode p A)) ∧
      cBits dir (cBits dir (encode p A)) = cBits dir (encode p A) := by
    simpa only [localCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
  have represent := encode_correct p A support
  constructor
  · have hc := properties.1
    rw [← decoded_card,← decoded_card,cBits_correct,represent] at hc
    exact hc
  constructor
  · intro v hv
    have hin := congrArg (fun mask : Nat => mask.testBit v.val) properties.2.1
    rw [Nat.testBit_and] at hin
    have left : (hood (cBits dir (encode p A))).testBit v.val = true := by
      change decoded (hood (cBits dir (encode p A))) v
      rw [hood_correct,cBits_correct,represent]
      exact hv
    rw [left] at hin
    have right : (cBits dir (hood (encode p A))).testBit v.val = true := by
      simpa using hin
    change decoded (cBits dir (hood (encode p A))) v at right
    rw [cBits_correct,hood_correct,represent] at right
    exact right
  · have heq := congrArg decoded properties.2.2
    simp only [cBits_correct,represent] at heq
    exact heq

def slice (A : Region Room) (p : Bool) : Region Room :=
  fun v => A v ∧ color v = (if p then 1 else 0)

theorem cmap_support (dir p : Bool) (A : Region Room)
    (support : ∀ v, A v → color v = (if p then 1 else 0)) :
    ∀ v, cmap dir A v → color v = (if p then 1 else 0) := by
  intro v hv
  have pos : 0 < card (fun u => key dir u = key dir v ∧ A u) := Nat.zero_lt_of_lt hv
  obtain ⟨u,heq,hu⟩ := (card_pos _).mp pos
  exact (key_color dir u v heq).symm.trans (support u hu)

theorem cmap_slice (dir p : Bool) (A : Region Room) :
    cmap dir (slice A p) = slice (cmap dir A) p := by
  classical
  funext v
  apply propext
  constructor
  · intro hv
    exact ⟨cmap_mono dir _ _ (fun _ h => h.1) v hv,
      cmap_support dir p (slice A p) (fun _ h => h.2) v hv⟩
  · rintro ⟨hv,hp⟩
    have counts : card (fun u => key dir u = key dir v ∧ slice A p u) =
        card (fun u => key dir u = key dir v ∧ A u) := by
      apply cardOn_congr
      intro u _
      constructor
      · exact fun h => ⟨h.1,h.2.1⟩
      · intro h
        exact ⟨h.1,h.2,(key_color dir u v h.1).trans hp⟩
    change rank dir v < _
    rw [counts]
    exact hv

theorem card_slices (A : Region Room) : card A = card (slice A false) + card (slice A true) := by
  have h := cardOn_split (List.finRange 16) A (fun v => color v = 0)
  have other : card (fun v => A v ∧ ¬ color v = 0) = card (slice A true) := by
    apply cardOn_congr
    intro v _
    have hc := color_bound v
    change (A v ∧ ¬ color v = 0) ↔ (A v ∧ color v = 1)
    constructor
    · intro hv; exact ⟨hv.1,by omega⟩
    · intro hv; exact ⟨hv.1,by omega⟩
  change card A = card (slice A false) + card (fun v => A v ∧ ¬ color v = 0) at h
  rwa [other] at h

theorem cmap_size (dir : Bool) (A : Region Room) : card (cmap dir A) = card A := by
  rw [card_slices (cmap dir A),← cmap_slice,← cmap_slice]
  rw [(checked_properties dir false (slice A false) (fun _ h => h.2)).1]
  rw [(checked_properties dir true (slice A true) (fun _ h => h.2)).1]
  exact (card_slices A).symm

theorem cmap_neighbors (dir : Bool) (A : Region Room) :
    Subset (move adj (cmap dir A)) (cmap dir (move adj A)) := by
  classical
  rintro v ⟨u,hu,hedge⟩
  let p : Bool := decide (color u = 1)
  have hp : color u = (if p then 1 else 0) := by
    have hc := color_bound u
    simp only [p]
    split <;> simp_all <;> omega
  have hlocal : cmap dir (slice A p) u := by
    rw [cmap_slice]
    exact ⟨hu,hp⟩
  have hn := (checked_properties dir p (slice A p) (fun _ h => h.2)).2.1
    v ⟨u,hlocal,hedge⟩
  apply cmap_mono dir (move adj (slice A p)) (move adj A) _ v hn
  rintro w ⟨z,hz,hzw⟩
  exact ⟨z,hz.1,hzw⟩

theorem cmap_idempotent (dir : Bool) (A : Region Room) :
    cmap dir (cmap dir A) = cmap dir A := by
  classical
  funext v
  apply propext
  let p : Bool := decide (color v = 1)
  have hp : color v = (if p then 1 else 0) := by
    have hc := color_bound v
    simp only [p]
    split <;> simp_all <;> omega
  have heq := (checked_properties dir p (slice A p) (fun _ h => h.2)).2.2
  simp only [cmap_slice] at heq
  have hv := congrFun heq v
  change (cmap dir (cmap dir A) v ∧ color v = (if p then 1 else 0)) =
    (cmap dir A v ∧ color v = (if p then 1 else 0)) at hv
  simpa only [hp,and_true] using (Eq.to_iff hv)

def compression (dir : Bool) : Princess.StrategyCompression.Compression adj where
  map := cmap dir
  mono := cmap_mono dir
  size := cmap_size dir
  neighbors := cmap_neighbors dir

#print axioms Princess.SquareCompressionFour.cmap_size
#print axioms Princess.SquareCompressionFour.cmap_neighbors
#print axioms Princess.SquareCompressionFour.cmap_idempotent

end Princess.SquareCompressionFour
