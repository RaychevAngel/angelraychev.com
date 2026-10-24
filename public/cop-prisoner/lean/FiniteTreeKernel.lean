import FiniteExclusionKernel

/-! A reflected version of the exclusion tree checker. The certificate is
data; one soundness proof accounts for complete branching and every pruning
rule. No external execution or native-decide result is trusted. -/
namespace Delivery.FiniteExclusion.TreeKernel
open FiniteGame Extremal

inductive Tree where
  | invalid
  | source (s t c : Fin 9)
  | predecessor (s t c u : Fin 9)
  | losing (s t c : Fin 9) (mask : Nat)
  | branch (children : Fin 9 → Tree)

def assignment (p : List (Fin 9)) : Assignment 9 := fun i => p.getD i.val 0

def LeafOK (a b : Assignment 9) (s t c : Fin 9) (mask : Nat) : Prop :=
  (s ≠ t ∧ ¬ edgeOf a b s t ∧ c ≠ s ∧ maskRegion mask s c) ∧
  (∀ r c : Fin 9, maskRegion mask r c → r ≠ t) ∧
  (∀ r c : Fin 9, maskRegion mask r c → r ≠ c →
    ∀ z, Legal (edgeOf a b) r z → z ≠ t ∧
      (z = c ∨ ∃ c', Legal (edgeOf a b) c c' ∧ (z = c' ∨ maskRegion mask z c')))

instance (a b : Assignment 9) (s t c : Fin 9) (mask : Nat) :
    Decidable (LeafOK a b s t c mask) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def check (a : Assignment 9) (p : List (Fin 9)) : Tree → Bool
  | .invalid => decide (¬ PrefixOK a p)
  | .source s t c =>
    if hs : s.val < p.length then
      decide (s ≠ t ∧ c ≠ s ∧ t ≠ a s ∧ t ≠ p[s.val] ∧
        lowerLegal a p c (a s) ∧ lowerLegal a p c p[s.val])
    else false
  | .predecessor s t c u =>
    if hu : u.val < p.length then
      decide (s ≠ t ∧ c ≠ s ∧ t ≠ a s ∧ s ≠ u ∧ p[u.val] = t ∧
        (∀ z, a z = t → lowerLegal a p c z) ∧ lowerLegal a p c u)
    else false
  | .losing s t c mask =>
    decide (p.length = 9) && decide (LeafOK a (assignment p) s t c mask)
  | .branch children =>
    decide (p.length < 9) && (List.finRange 9).all (fun v => check a (p++[v]) (children v))

theorem sound (a : Assignment 9) (p : List (Fin 9)) (tree : Tree)
    (checked : check a p tree = true) : Excluded a p := by
  induction tree generalizing p with
  | invalid => exact invalid_excluded a p (of_decide_eq_true checked)
  | source s t c =>
    unfold check at checked
    split at checked
    · exact source_excluded a p s t c ‹_› (of_decide_eq_true checked)
    · contradiction
  | predecessor s t c u =>
    unfold check at checked
    split at checked
    · exact predecessor_excluded a p s t c u ‹_› (of_decide_eq_true checked)
    · contradiction
  | losing s t c mask =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at checked
    have ok := checked.2
    exact losing_excluded a p checked.1 (assignment p)
      (fun i => by simp [assignment,show i.val < p.length by have := i.isLt; omega])
      s t c (losingMask a (assignment p) t mask ok.2.1 ok.2.2) ok.1
  | branch children ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
    exact branch_excluded a p checked.1
      (fun v => ih v (p++[v]) (checked.2 v (List.mem_finRange v)))

theorem every_second_factor_blocked (a : Assignment 9) (tree : Tree)
    (checked : check a [] tree = true) (b : Assignment 9) (valid : Valid a b) : Blocked a b :=
  sound a [] tree checked b valid (by intro i h; simp at h)

#print axioms sound
#print axioms every_second_factor_blocked
end Delivery.FiniteExclusion.TreeKernel
