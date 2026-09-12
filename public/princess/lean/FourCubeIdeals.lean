import FourCubeIdealData

namespace Princess.FourCubeCompression
open Princess.ProductCompression Princess.CaptureRecurrence Princess.LadderCardinality
open Princess.SurvivorEnvelope Princess.FiniteSubsetProfiles Princess.FiniteIdealCertificates

attribute [local irreducible] iterateMap

theorem every_op_mem (pair : Fin 3) (dir : Bool) : op pair dir ∈ operators := by
  have h : ∀ pair : Fin 3, ∀ dir : Bool, op pair dir ∈ operators := by
    intro pair dir
    have hp : pair=0 ∨ pair=1 ∨ pair=2 := by
      have := pair.isLt
      omega
    rcases hp with hp | hp | hp <;> subst pair <;> cases dir <;> simp [operators]
  exact h pair dir

theorem op_down_step (pair : Fin 3) (dir : Bool) (A : Region Room)
    (fixed : (op pair dir).map A=A) (u v : Room)
    (step : downStep pair dir u v) (present : A v) : A u := by
  have hv : (op pair dir).map A v := by rwa [fixed]
  have hc : SquareCompressionFour.rank dir (toPair pair v).1 <
      card (fun q : Fin 16 => SquareCompressionFour.key dir q =
        SquareCompressionFour.key dir (toPair pair v).1 ∧ A (fromPair pair (q,(toPair pair v).2))) := hv
  have hu : (op pair dir).map A u := by
    change SquareCompressionFour.rank dir (toPair pair u).1 <
      card (fun q : Fin 16 => SquareCompressionFour.key dir q =
        SquareCompressionFour.key dir (toPair pair u).1 ∧ A (fromPair pair (q,(toPair pair u).2)))
    rw [step.1,step.2.1]
    exact Nat.lt_of_le_of_lt step.2.2 hc
  rwa [fixed] at hu

theorem fixed_down_mask (A : Region Room) (fixed : normalizer.map A=A)
    (u v : Room) (member : (downMask v).testBit u.val=true) (present : A v) : A u := by
  have common := fixed_common A fixed
  have all : ∀ k : Nat, ∀ v : Room, weight v=k → ∀ u : Room,
      (downMask v).testBit u.val=true → A v → A u := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro v hk u hu hv
      by_cases heq : u=v
      · simpa only [heq] using hv
      · have routefacts := route_valid u v hu heq
        have hroute : A (route u v) := op_down_step (routePair u v) (routeDir u v) A
          (common _ (every_op_mem _ _)) (route u v) v routefacts.2.2 hv
        exact ih (weight (route u v)) (by omega) (route u v) rfl u routefacts.2.1 hroute
  exact all (weight v) v rfl u member present

def colorRooms (p : Bool) : List Room :=
  if p then [63, 31, 43, 55, 46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] else [47, 59, 62, 15, 27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0]

noncomputable def encodeColor (p : Bool) (A : Region Room) : Nat :=
  selectedMask (fun v => 2^v.val) (fun v => @decide (A v) (Classical.propDecidable _)) (colorRooms p)

def decoded (mask : Nat) : Region Room := fun v => mask.testBit v.val=true

theorem colorRooms_mem (p : Bool) (v : Room) : v∈colorRooms p ↔ color v=(if p then 1 else 0) := by
  have h : ∀ p : Bool, ∀ v : Room, v∈colorRooms p ↔ color v=(if p then 1 else 0) := by decide
  exact h p v

theorem encodeColor_correct (p : Bool) (A : Region Room)
    (support : ∀ v, A v → color v=(if p then 1 else 0)) : decoded (encodeColor p A)=A := by
  classical
  funext v
  apply propext
  unfold decoded encodeColor
  rw [selectedMask_bit]
  simp only [Nat.testBit_two_pow,decide_eq_true_eq]
  constructor
  · rintro ⟨u,_,hu,heq⟩
    have huv : u=v := Fin.ext heq
    simpa only [huv] using hu
  · intro hv
    exact ⟨v,(colorRooms_mem p v).mpr (support v hv),hv,rfl⟩

def down (j : Nat) : Nat := if h : j<64 then downMask ⟨j,h⟩ else 0

theorem down_eq (v : Room) : down v.val=downMask v := by simp [down,v.isLt]

theorem checker_sound (p : Bool) (A : Region Room) (P : Nat → Bool)
    (support : ∀ v, A v → color v=(if p then 1 else 0))
    (closed : ∀ u v : Room, (downMask v).testBit u.val=true → A v → A u)
    (checked : check down P ((colorRooms p).map Fin.val) 0=true) :
    P (encodeColor p A)=true := by
  classical
  have represent := encodeColor_correct p A support
  apply check_sound down P ((colorRooms p).map Fin.val) (encodeColor p A) 0 _ _ _ _ checked
  · intro j hj; simp at hj
  · intro j hj
    right
    unfold encodeColor at hj
    rw [selectedMask_bit] at hj
    obtain ⟨v,hv,_,hbit⟩ := hj
    simp only [Nat.testBit_two_pow,decide_eq_true_eq] at hbit
    exact List.mem_map.mpr ⟨v,hv,hbit⟩
  · intro j hj
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hj
    rw [down_eq]
    exact down_self v
  · intro j hj present k hk
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hj
    rw [down_eq] at hk
    have hkv : k<64 := by
      have bits := hk
      unfold downMask at bits
      rw [Nat.testBit_and,Bool.and_eq_true] at bits
      have h : (2^64-1).testBit k=true := bits.2
      simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using h
    have av : A v := by
      change decoded (encodeColor p A) v at present
      rwa [represent] at present
    have au : A ⟨k,hkv⟩ := closed ⟨k,hkv⟩ v hk av
    have enc : decoded (encodeColor p A) ⟨k,hkv⟩ := by rwa [represent]
    exact enc

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.fixed_down_mask
#print axioms Princess.FourCubeCompression.checker_sound
