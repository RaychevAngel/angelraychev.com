import LadderCardinality

/-! Kernel-checkable certificates for neighborhood profiles. A binary decision
recursion ranges over all subsets of a finite room list. It retains only the
selected cardinality and the union of encoded neighborhoods. -/
namespace Princess.FiniteSubsetProfiles
open Princess.LadderCardinality

def maskCard (n mask : Nat) : Nat :=
  (List.finRange n).countP (fun v => mask.testBit v.val)

def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, mask => mask % 2 + countBits n (mask / 2)

theorem countBits_eq_maskCard (n mask : Nat) : countBits n mask = maskCard n mask := by
  induction n generalizing mask with
  | zero => rfl
  | succ n ih =>
      unfold maskCard
      rw [List.finRange_succ, List.countP_cons, List.countP_map]
      change mask % 2 + countBits n (mask / 2) =
        (List.finRange n).countP (fun v => mask.testBit (v.val + 1)) +
          (if mask.testBit 0 then 1 else 0)
      have first : (if mask.testBit 0 then 1 else 0) = mask % 2 := by
        rw [Nat.testBit_zero]
        by_cases h : mask % 2 = 1 <;> simp [h] <;> omega
      rw [first, ih, Nat.add_comm]
      congr 1
      apply List.countP_congr
      intro v _
      rw [Nat.testBit_add_one]

def selectedCount {V : Type} (pick : V → Bool) : List V → Nat
  | [] => 0
  | v :: vs => selectedCount pick vs + if pick v then 1 else 0

def selectedMask {V : Type} (neighbors : V → Nat) (pick : V → Bool) : List V → Nat
  | [] => 0
  | v :: vs => if pick v then neighbors v ||| selectedMask neighbors pick vs
      else selectedMask neighbors pick vs

def checkAll {V : Type} (n : Nat) (neighbors : V → Nat) (profile : Nat → Nat) :
    List V → Nat → Nat → Bool
  | [], k, mask => decide (profile k ≤ countBits n mask)
  | v :: vs, k, mask => checkAll n neighbors profile vs k mask &&
      checkAll n neighbors profile vs (k + 1) (mask ||| neighbors v)

theorem checkAll_sound {V : Type} (n : Nat) (neighbors : V → Nat)
    (profile : Nat → Nat) (vs : List V) (k mask : Nat) (pick : V → Bool)
    (checked : checkAll n neighbors profile vs k mask = true) :
    profile (k + selectedCount pick vs) ≤
      maskCard n (mask ||| selectedMask neighbors pick vs) := by
  induction vs generalizing k mask with
  | nil => simpa only [checkAll, countBits_eq_maskCard, selectedCount, selectedMask, Nat.add_zero,
      Nat.or_zero, decide_eq_true_eq] using checked
  | cons v vs ih =>
      have both : checkAll n neighbors profile vs k mask = true ∧
          checkAll n neighbors profile vs (k + 1) (mask ||| neighbors v) = true := by
        simpa only [checkAll, Bool.and_eq_true] using checked
      by_cases hp : pick v = true
      · have h := ih (k + 1) (mask ||| neighbors v) both.2
        simp only [selectedCount, selectedMask, hp, ite_true]
        have sum : k + (selectedCount pick vs + 1) = k + 1 + selectedCount pick vs := by omega
        rw [sum, ← Nat.or_assoc]
        exact h
      · have h := ih k mask both.1
        simpa [selectedCount, selectedMask, hp] using h

theorem selectedCount_eq {n : Nat} (vs : List (Fin n)) (B : Fin n → Prop) [DecidablePred B] :
    selectedCount (fun v => decide (B v)) vs = cardOn vs B := by
  classical
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [selectedCount, cardOn_cons, ih]
      by_cases h : B v <;> simp [h]

theorem selectedMask_bit {V : Type} (neighbors : V → Nat) (pick : V → Bool)
    (vs : List V) (j : Nat) :
    (selectedMask neighbors pick vs).testBit j = true ↔
      ∃ v, v ∈ vs ∧ pick v = true ∧ (neighbors v).testBit j = true := by
  induction vs with
  | nil => simp [selectedMask]
  | cons v vs ih =>
      simp only [selectedMask]
      by_cases hp : pick v = true
      · simp only [hp, ite_true, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
        constructor
        · rintro (hv | ⟨u, hu, hpu, hn⟩)
          · exact ⟨v, Or.inl rfl, hp, hv⟩
          · exact ⟨u, Or.inr hu, hpu, hn⟩
        · rintro ⟨u, (hu | hu), hpu, hn⟩
          · subst u; exact Or.inl hn
          · exact Or.inr ⟨u, hu, hpu, hn⟩
      · simp only [hp, Bool.false_eq_true, ite_false, ih, List.mem_cons]
        constructor
        · rintro ⟨u, hu, hpu, hn⟩
          exact ⟨u, Or.inr hu, hpu, hn⟩
        · rintro ⟨u, (hu | hu), hpu, hn⟩
          · subst u; exact False.elim (hp hpu)
          · exact ⟨u, hu, hpu, hn⟩

end Princess.FiniteSubsetProfiles
