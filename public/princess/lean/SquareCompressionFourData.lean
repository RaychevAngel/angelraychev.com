import ProductCompression
import FiniteSubsetProfiles

/-! The two diagonal prefix compressions on the physical 4 by 4 square.
Finite certificates inspect every subset of each checkerboard color. -/
namespace Princess.SquareCompressionFour
open Princess.LadderCardinality Princess.CaptureRecurrence
open Princess.FiniteSubsetProfiles

abbrev Room := Fin 16
def x (v : Room) : Nat := v.val / 4
def y (v : Room) : Nat := v.val % 4
def color (v : Room) : Nat := (x v + y v) % 2
def adj (u v : Room) : Prop :=
  (x u = x v ∧ (y u + 1 = y v ∨ y v + 1 = y u)) ∨
  (y u = y v ∧ (x u + 1 = x v ∨ x v + 1 = x u))
instance (u v : Room) : Decidable (adj u v) := inferInstanceAs (Decidable (_ ∨ _))
def key (dir : Bool) (v : Room) : Nat := if dir then x v + y v else x v + 3 - y v
def fiberMask (dir : Bool) (v : Room) : Nat :=
  ((if dir then 57896541548238994656882095250359191406141815324543731204793764258554890551297 else 59764057916222216136048871085071015419518673126303510783487208377905420862497) >>> (16*v.val)) &&& 65535
def rank (dir : Bool) (v : Room) : Nat :=
  ((if dir then 5547236 else 3835974656) >>> (2*v.val)) &&& 3
def neighborMask (v : Room) : Nat :=
  (32567656993031714564366547016634013292082280239018560905309628457854148345874 >>> (16*v.val)) &&& 65535

def cmap (dir : Bool) (A : Region Room) : Region Room :=
  fun v => rank dir v < card (fun u => key dir u = key dir v ∧ A u)

def cBits (dir : Bool) (mask : Nat) : Nat := selectedMask (fun v : Room => 2^v.val)
  (fun v => decide (rank dir v < countBits 16 (mask &&& fiberMask dir v))) (List.finRange 16)

def hood (mask : Nat) : Nat := selectedMask neighborMask
  (fun v : Room => mask.testBit v.val) (List.finRange 16)

def rooms (p : Bool) : List Room := if p then [1,3,4,6,9,11,12,14] else [0,2,5,7,8,10,13,15]

theorem fiber_mask_correct : ∀ dir : Bool, ∀ u v : Room,
    (fiberMask dir v).testBit u.val = true ↔ key dir u = key dir v := by decide

theorem neighbor_mask_correct : ∀ u v : Room,
    (neighborMask u).testBit v.val = true ↔ adj u v := by decide

theorem rank_correct : ∀ dir : Bool, ∀ v : Room,
    rank dir v = (List.finRange 16).countP (fun u =>
      decide (key dir u = key dir v ∧ y u < y v)) := by decide

theorem key_color : ∀ dir : Bool, ∀ u v : Room,
    key dir u = key dir v → color u = color v := by decide

theorem color_bound : ∀ v : Room, color v < 2 := by decide

theorem rooms_membership : ∀ p : Bool, ∀ v : Room,
    v ∈ rooms p ↔ color v = (if p then 1 else 0) := by decide

theorem cmap_mono (dir : Bool) (A B : Region Room) (h : Subset A B) :
    Subset (cmap dir A) (cmap dir B) := by
  intro v hv
  exact Nat.lt_of_lt_of_le hv (card_mono _ _ (fun u hu => ⟨hu.1,h u hu.2⟩))

def checkSubsets (P : Nat → Bool) : List Room → Nat → Bool
  | [], mask => P mask
  | v :: vs, mask => checkSubsets P vs mask && checkSubsets P vs (mask ||| 2^v.val)

theorem checkSubsets_sound (P : Nat → Bool) (vs : List Room) (mask : Nat)
    (pick : Room → Bool) (h : checkSubsets P vs mask = true) :
    P (mask ||| selectedMask (fun v => 2^v.val) pick vs) = true := by
  induction vs generalizing mask with
  | nil => simpa [checkSubsets,selectedMask] using h
  | cons v vs ih =>
      have both : checkSubsets P vs mask = true ∧
          checkSubsets P vs (mask ||| 2^v.val) = true := by
        simpa only [checkSubsets,Bool.and_eq_true] using h
      by_cases hp : pick v = true
      · simpa only [selectedMask,hp,ite_true,← Nat.or_assoc] using ih _ both.2
      · simpa [selectedMask,hp] using ih _ both.1

def decoded (mask : Nat) : Region Room := fun v => mask.testBit v.val = true

noncomputable def encode (p : Bool) (A : Region Room) : Nat :=
  selectedMask (fun v => 2^v.val) (fun v => @decide (A v) (Classical.propDecidable _)) (rooms p)

theorem encode_correct (p : Bool) (A : Region Room)
    (support : ∀ v, A v → color v = (if p then 1 else 0)) : decoded (encode p A) = A := by
  classical
  funext v
  apply propext
  unfold decoded encode
  rw [selectedMask_bit]
  simp only [Nat.testBit_two_pow,decide_eq_true_eq]
  constructor
  · rintro ⟨u,_,hu,heq⟩
    have huv : u = v := Fin.ext heq
    simpa [huv] using hu
  · intro hv
    exact ⟨v,(rooms_membership p v).mpr (support v hv),hv,rfl⟩

theorem decoded_card (mask : Nat) : card (decoded mask) = countBits 16 mask := by
  rw [countBits_eq_maskCard]
  unfold card cardOn maskCard decoded
  apply List.countP_congr
  intro v _
  simp

theorem cBits_correct (dir : Bool) (mask : Nat) :
    decoded (cBits dir mask) = cmap dir (decoded mask) := by
  classical
  funext v
  apply propext
  unfold decoded cBits
  rw [selectedMask_bit]
  simp only [Nat.testBit_two_pow,decide_eq_true_eq]
  have hc : countBits 16 (mask &&& fiberMask dir v) =
      card (fun u => key dir u = key dir v ∧ decoded mask u) := by
    rw [countBits_eq_maskCard]
    unfold maskCard card cardOn
    apply List.countP_congr
    intro u _
    simp only [Nat.testBit_and,Bool.and_eq_true,decide_eq_true_eq]
    rw [fiber_mask_correct]
    exact and_comm
  constructor
  · rintro ⟨u,_,hu,heq⟩
    have huv : u = v := Fin.ext heq
    subst u
    simpa only [hc,cmap,decoded] using hu
  · intro hv
    refine ⟨v,List.mem_finRange v,?_,rfl⟩
    change rank dir v < _ at hv
    rwa [hc]

theorem hood_correct (mask : Nat) : decoded (hood mask) = move adj (decoded mask) := by
  funext v
  apply propext
  unfold decoded hood
  rw [selectedMask_bit]
  simp only [List.mem_finRange,true_and]
  constructor
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(neighbor_mask_correct u v).mp he⟩
  · rintro ⟨u,hu,he⟩
    exact ⟨u,hu,(neighbor_mask_correct u v).mpr he⟩

def localCheck (dir : Bool) (mask : Nat) : Bool :=
  decide (countBits 16 (cBits dir mask) = countBits 16 mask) &&
  decide ((hood (cBits dir mask) &&& cBits dir (hood mask)) = hood (cBits dir mask)) &&
  decide (cBits dir (cBits dir mask) = cBits dir mask)

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem batch_false_false_0 : checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 0 = true := by
  decide +kernel

theorem batch_false_false_1 : checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 4 = true := by
  decide +kernel

theorem batch_false_false_2 : checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 1 = true := by
  decide +kernel

theorem batch_false_false_3 : checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 5 = true := by
  decide +kernel

theorem checked_false_false : checkSubsets (localCheck false) (rooms false) 0 = true := by
  change ((checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 0 && checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 4) && (checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 1 && checkSubsets (localCheck false) [5, 7, 8, 10, 13, 15] 5)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨batch_false_false_0,batch_false_false_1⟩,⟨batch_false_false_2,batch_false_false_3⟩⟩

theorem batch_false_true_0 : checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 0 = true := by
  decide +kernel

theorem batch_false_true_1 : checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 8 = true := by
  decide +kernel

theorem batch_false_true_2 : checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 2 = true := by
  decide +kernel

theorem batch_false_true_3 : checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 10 = true := by
  decide +kernel

theorem checked_false_true : checkSubsets (localCheck false) (rooms true) 0 = true := by
  change ((checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 0 && checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 8) && (checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 2 && checkSubsets (localCheck false) [4, 6, 9, 11, 12, 14] 10)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨batch_false_true_0,batch_false_true_1⟩,⟨batch_false_true_2,batch_false_true_3⟩⟩

theorem batch_true_false_0 : checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 0 = true := by
  decide +kernel

theorem batch_true_false_1 : checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 4 = true := by
  decide +kernel

theorem batch_true_false_2 : checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 1 = true := by
  decide +kernel

theorem batch_true_false_3 : checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 5 = true := by
  decide +kernel

theorem checked_true_false : checkSubsets (localCheck true) (rooms false) 0 = true := by
  change ((checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 0 && checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 4) && (checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 1 && checkSubsets (localCheck true) [5, 7, 8, 10, 13, 15] 5)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨batch_true_false_0,batch_true_false_1⟩,⟨batch_true_false_2,batch_true_false_3⟩⟩

theorem batch_true_true_0 : checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 0 = true := by
  decide +kernel

theorem batch_true_true_1 : checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 8 = true := by
  decide +kernel

theorem batch_true_true_2 : checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 2 = true := by
  decide +kernel

theorem batch_true_true_3 : checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 10 = true := by
  decide +kernel

theorem checked_true_true : checkSubsets (localCheck true) (rooms true) 0 = true := by
  change ((checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 0 && checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 8) && (checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 2 && checkSubsets (localCheck true) [4, 6, 9, 11, 12, 14] 10)) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨batch_true_true_0,batch_true_true_1⟩,⟨batch_true_true_2,batch_true_true_3⟩⟩

theorem checked : ∀ dir p : Bool, checkSubsets (localCheck dir) (rooms p) 0 = true := by
  intro dir p
  cases dir <;> cases p
  · exact checked_false_false
  · exact checked_false_true
  · exact checked_true_false
  · exact checked_true_true

end Princess.SquareCompressionFour
