import PathGeometry
import PathUpperArithmetic

/-! Actual-room descending sweeps. These lemmas construct legal finite probe
sequences; they are not merely arithmetic identities about proposed lengths.
-/

namespace Princess.PathSweep

open Princess.PathGeometry
open Princess.LadderCardinality
open Princess.CaptureRecurrence

def legal {n : Nat} (m : Nat) (S : Region (Fin n)) : Prop := card S ≤ m

theorem card_empty (n : Nat) : card (fun _ : Fin n => False) = 0 := by
  classical
  simp [card, cardOn]

theorem empty_winning {n : Nat} (m t : Nat) (B : Region (Fin n)) (hB : Empty B) :
    winning adj (legal m) t B := by
  induction t with
  | zero => exact hB
  | succ t ih =>
      exact winning_succ adj (legal m) ⟨fun _ => False, by
        change card (fun _ : Fin n => False) ≤ m
        rw [card_empty]; omega⟩ t B ih

theorem winning_reflected {n : Nat} (m t : Nat) (B : Region (Fin n))
    (hB : winning adj (legal m) t B) :
    winning adj (legal m) t (reflected B) := by
  induction t generalizing B with
  | zero =>
      intro v hv
      exact hB v.rev hv
  | succ t ih =>
      obtain ⟨S, hS, hW⟩ := hB
      refine ⟨reflected S, ?_, ?_⟩
      · change card (reflected S) ≤ m
        rw [card_reflected]
        exact hS
      · rw [next_reflected]
        exact ih (next adj B S) hW

/-- A parity prefix can be cleared in L rounds when the frontier satisfies the
linear sweep bound. The proof explicitly constructs each top-m inspection. -/
theorem prefix_sweep {n m L R : Nat} (hm : 1 ≤ m) (hL : 1 ≤ L)
    (hRn : R ≤ n) (hR : R ≤ L * (2 * m - 1) + 1) :
    winning adj (legal m) L (parityPrefix (n := n) R) := by
  induction L generalizing R with
  | zero => omega
  | succ L ih =>
      refine ⟨top R m, card_top R m hRn, ?_⟩
      by_cases done : R ≤ 2 * m
      · exact empty_winning m L _ (next_top_finishes done)
      · rw [next_top_survives hRn hm (by omega)]
        apply ih
        · have he : (L + 1) * (2 * m - 1) =
              L * (2 * m - 1) + (2 * m - 1) := by rw [Nat.succ_mul]
          rw [he] at hR
          by_cases hz : L = 0
          · subst L; simp at hR; omega
          · omega
        · omega
        · rw [Nat.succ_mul] at hR
          omega

/-- A smaller first allocation, followed by L ordinary full-budget rounds. -/
theorem prefix_prelude {n m b L R : Nat} (hm : 1 ≤ m) (hb : 1 ≤ b)
    (hL : 1 ≤ L) (hRn : R ≤ n) (hR : R ≤ L * (2 * m - 1) + 2 * b) :
    ∃ S : Region (Fin n), card S ≤ b ∧
      winning adj (legal m) L (next adj (parityPrefix R) S) := by
  refine ⟨top R b, card_top R b hRn, ?_⟩
  by_cases done : R ≤ 2 * b
  · exact empty_winning m L _ (next_top_finishes done)
  · rw [next_top_survives hRn hb (by omega)]
    exact prefix_sweep hm hL (by omega) (by omega)

def fullParity {n : Nat} (p : Nat) : Region (Fin n) :=
  fun v => (v.val + 1) % 2 = p

theorem full_parity_prefix {n : Nat} (_hn : 1 ≤ n) :
    fullParity (n := n) (n % 2) = parityPrefix n := by
  funext v
  apply propext
  exact ⟨fun h => ⟨v.isLt, h⟩, And.right⟩

theorem move_full_parity {n : Nat} (hn : 2 ≤ n) (p : Nat) (hp : p < 2) :
    Princess.move adj (fullParity (n := n) p) = fullParity ((p + 1) % 2) := by
  funext v
  apply propext
  constructor
  · rintro ⟨u, hu, hadj⟩
    have opp := adj_parity u v hadj
    change (u.val + 1) % 2 = p at hu
    change (v.val + 1) % 2 = (p + 1) % 2
    omega
  · intro hv
    obtain ⟨u, hadj⟩ := no_dead_ends hn v
    have opp := adj_parity v u hadj
    refine ⟨u, ?_, (adj_symm v u).mp hadj⟩
    change (v.val + 1) % 2 = (p + 1) % 2 at hv
    change (u.val + 1) % 2 = p
    omega

theorem next_union_passive {n : Nat} (A B S : Region (Fin n))
    (unshot : ∀ v, B v → ¬ S v) :
    next adj (fun v => A v ∨ B v) S =
      (fun v => next adj A S v ∨ Princess.move adj B v) := by
  funext v
  apply propext
  constructor
  · rintro ⟨u, ⟨hu, hs⟩, hadj⟩
    rcases hu with hA | hB
    · exact Or.inl ⟨u, ⟨hA, hs⟩, hadj⟩
    · exact Or.inr ⟨u, hB, hadj⟩
  · rintro (hA | hB)
    · obtain ⟨u, ⟨hu, hs⟩, hadj⟩ := hA
      exact ⟨u, ⟨Or.inl hu, hs⟩, hadj⟩
    · obtain ⟨u, hu, hadj⟩ := hB
      exact ⟨u, ⟨Or.inr hu, unshot u hu⟩, hadj⟩

inductive Run {n : Nat} (m : Nat) : Nat → Region (Fin n) → Region (Fin n) → Prop
  | nil (B) : Run m 0 B B
  | cons {k B C} (S) : legal m S → Run m k (next adj B S) C → Run m (k + 1) B C

theorem Run.then_winning {n m k L : Nat} {B C : Region (Fin n)}
    (hRun : Run m k B C) (hW : winning adj (legal m) L C) :
    winning adj (legal m) (k + L) B := by
  induction hRun with
  | nil B => simpa using hW
  | @cons k B C S hS tail ih =>
      have h : winning adj (legal m) (k + L + 1) B := ⟨S, hS, ih hW⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1 L] using h

/-- q nonterminal first-cohort batches; the other cohort remains its full
alternating parity throughout. -/
theorem first_batches {n m q R p : Nat} (hn : 2 ≤ n) (hm : 1 ≤ m)
    (hp : p < 2) (hopp : p ≠ R % 2) (hRn : R ≤ n)
    (hR : q * (2 * m - 1) + 2 ≤ R) :
    Run m q
      (fun v : Fin n => parityPrefix R v ∨ fullParity p v)
      (fun v => parityPrefix (R - q * (2 * m - 1)) v ∨ fullParity ((p + q) % 2) v) := by
  induction q generalizing R p with
  | zero =>
      have hpmod : p % 2 = p := Nat.mod_eq_of_lt hp
      simpa only [Nat.zero_mul, Nat.sub_zero, Nat.add_zero, hpmod] using
        Run.nil (m := m) (fun v : Fin n => parityPrefix R v ∨ fullParity p v)
  | succ q ih =>
      have hR' := hR
      rw [Nat.succ_mul] at hR'
      have hsurv : 2 * m < R := by omega
      apply Run.cons (top R m) (card_top R m hRn)
      rw [next_union_passive _ _ _ (by
        intro v hv hs
        exact hopp ((hs.1.2).symm.trans hv).symm)]
      rw [next_top_survives hRn hm hsurv, move_full_parity hn p hp]
      have htbound : q * (2 * m - 1) + 2 ≤ R - 2 * m + 1 := by omega
      have tail := ih (R := R - 2 * m + 1) (p := (p + 1) % 2)
        (by omega) (by omega) (by omega) htbound
      have hrend : R - 2 * m + 1 - q * (2 * m - 1) =
          R - (q + 1) * (2 * m - 1) := by
        rw [Nat.succ_mul q (2 * m - 1)]
        omega
      have hpend : ((p + 1) % 2 + q) % 2 = (p + (q + 1)) % 2 := by omega
      rw [hrend, hpend] at tail
      exact tail

theorem card_union_le {n : Nat} (A B : Region (Fin n)) :
    card (fun v => A v ∨ B v) ≤ card A + card B := by
  have split := cardOn_split (List.finRange n) (fun v => A v ∨ B v) A
  have left : (fun v => (A v ∨ B v) ∧ A v) = A := by
    funext v; exact propext ⟨And.right, fun h => ⟨Or.inl h, h⟩⟩
  have right := card_mono (fun v => (A v ∨ B v) ∧ ¬ A v) B
    (fun v h => h.1.resolve_left h.2)
  change card (fun v => A v ∨ B v) =
    card (fun v => (A v ∨ B v) ∧ A v) + card (fun v => (A v ∨ B v) ∧ ¬ A v) at split
  rw [left] at split
  omega

/-- On the joining day all remaining A rooms are inspected, together with a
first allocation for B. Any incidental extra captures only improve the bound. -/
theorem finish_first {n m L : Nat} (A B S : Region (Fin n))
    (budget : card A + card S ≤ m)
    (tail : winning adj (legal m) L (next adj B S)) :
    winning adj (legal m) (L + 1) (fun v => A v ∨ B v) := by
  refine ⟨fun v => A v ∨ S v, Nat.le_trans (card_union_le A S) budget, ?_⟩
  apply winning_downward adj (legal m) L _ (next adj B S) _ tail
  rintro v ⟨u, ⟨hu, hs⟩, hadj⟩
  exact ⟨u, ⟨hu.resolve_left (fun ha => hs (Or.inl ha)),
    fun hS => hs (Or.inr hS)⟩, hadj⟩

def bestFrontier (n p : Nat) : Nat := if n % 2 = 0 then n - 1 else n - 1 + p

theorem best_frontier_bounds {n p : Nat} (hn : 2 ≤ n) (hp : p < 2) :
    1 ≤ bestFrontier n p ∧ bestFrontier n p ≤ n := by
  unfold bestFrontier
  split <;> omega

theorem orient_full {n p : Nat} (hn : 2 ≤ n) (hp : p < 2) :
    fullParity (n := n) p = parityPrefix (bestFrontier n p) ∨
      fullParity (n := n) p = reflected (parityPrefix (bestFrontier n p)) := by
  by_cases he : n % 2 = 0
  · by_cases hz : p = 0
    · right
      funext v
      apply propext
      have hv := v.isLt
      simp only [fullParity, reflected, parityPrefix, Fin.val_rev,
        bestFrontier, if_pos he, hz]
      omega
    · left
      funext v
      apply propext
      have hv := v.isLt
      simp only [fullParity, parityPrefix, bestFrontier, if_pos he]
      omega
  · left
    funext v
    apply propext
    have hv := v.isLt
    simp only [fullParity, parityPrefix, bestFrontier, if_neg he]
    omega

theorem full_sweep {n m L p : Nat} (hn : 2 ≤ n) (hm : 1 ≤ m) (hp : p < 2)
    (hL : 1 ≤ L) (bound : bestFrontier n p ≤ L * (2 * m - 1) + 1) :
    winning adj (legal m) L (fullParity (n := n) p) := by
  have w := prefix_sweep hm hL (best_frontier_bounds hn hp).2 bound
  rcases orient_full hn hp with h | h
  · rw [h]; exact w
  · rw [h]; exact winning_reflected m L _ w

theorem full_prelude {n m b L p : Nat} (hn : 2 ≤ n) (hm : 1 ≤ m)
    (hb : 1 ≤ b) (hp : p < 2) (hL : 1 ≤ L)
    (bound : bestFrontier n p ≤ L * (2 * m - 1) + 2 * b) :
    ∃ S : Region (Fin n), card S ≤ b ∧ winning adj (legal m) L
      (next adj (fullParity p) S) := by
  obtain ⟨S, budget, win⟩ := prefix_prelude hm hb hL (best_frontier_bounds hn hp).2 bound
  rcases orient_full hn hp with h | h
  · rw [h]; exact ⟨S, budget, win⟩
  · refine ⟨reflected S, ?_, ?_⟩
    · rw [card_reflected]; exact budget
    · rw [h, next_reflected]
      exact winning_reflected m L _ win

def fast (n m r : Nat) : Prop :=
  r ≤ m - 2 ∨ (r = m - 1 ∧ PathUpperArithmetic.bothEven n m)

instance (n m r : Nat) : Decidable (fast n m r) :=
  inferInstanceAs (Decidable (_ ∨ _))

def remaining (n m q r : Nat) := if fast n m r then q else q + 1

theorem join_arithmetic (n m q r : Nat) (hm : 2 ≤ m) (hmn : m < n)
    (hr : 1 ≤ r) (hrd : r ≤ 2 * m - 1) (hn : n = q * (2 * m - 1) + r + 2) :
    let c := r / 2 + 1
    let b := m - c
    let L := remaining n m q r
    c ≤ m ∧ 1 ≤ L ∧
      (0 < b → bestFrontier n (r % 2) ≤ L * (2 * m - 1) + 2 * b) ∧
      (b = 0 → bestFrontier n ((r % 2 + 1) % 2) ≤ L * (2 * m - 1) + 1) := by
  dsimp
  have hc : r / 2 + 1 ≤ m := by omega
  refine ⟨hc, ?_, ?_, ?_⟩
  · unfold remaining
    split
    · rename_i hf
      unfold fast PathUpperArithmetic.bothEven at hf
      by_cases hq : q = 0
      · subst q; simp only [Nat.zero_mul, Nat.zero_add] at hn; omega
      · omega
    · omega
  · intro hb
    unfold remaining
    split
    · rename_i hf
      unfold fast PathUpperArithmetic.bothEven at hf
      unfold bestFrontier
      split <;> omega
    · rw [Nat.succ_mul q (2 * m - 1)]
      unfold bestFrontier
      split <;> omega
  · intro hb
    have hslow : ¬ fast n m r := by
      unfold fast PathUpperArithmetic.bothEven
      omega
    rw [remaining, if_neg hslow, Nat.succ_mul q (2 * m - 1)]
    unfold bestFrontier
    split <;> omega

theorem joining_phase (n m q r : Nat) (hm : 2 ≤ m) (hmn : m < n)
    (hr : 1 ≤ r) (hrd : r ≤ 2 * m - 1) (hn : n = q * (2 * m - 1) + r + 2) :
    winning adj (legal m) (remaining n m q r + 1)
      (fun v : Fin n => parityPrefix (r + 1) v ∨ fullParity (r % 2) v) := by
  obtain ⟨hc, hL, hshared, hseparate⟩ := join_arithmetic n m q r hm hmn hr hrd hn
  have cardA : card (parityPrefix (n := n) (r + 1)) = r / 2 + 1 := by
    rw [card_prefix (r + 1) (by omega)]
    omega
  by_cases shared : 0 < m - (r / 2 + 1)
  · obtain ⟨S, budget, win⟩ := full_prelude (n := n) (m := m)
      (by omega) (by omega) shared (by omega) hL (hshared shared)
    apply finish_first _ _ S
    · rw [cardA]; omega
    · exact win
  · apply finish_first _ _ (fun _ => False)
    · rw [cardA, card_empty]; omega
    · have heq : next adj (fullParity (n := n) (r % 2)) (fun _ => False) =
          fullParity ((r % 2 + 1) % 2) := by
        unfold next
        simp only [not_false_eq_true, and_true]
        exact move_full_parity (by omega) (r % 2) (by omega)
      rw [heq]
      exact full_sweep (by omega) (by omega) (by omega) hL (hseparate (by omega))

/-- The full physical two-cohort construction, in the canonical positive
remainder parameters. The ordinary proof's exceptional parity case is explicit. -/
theorem sweep_upper (n m q r : Nat) (hm : 2 ≤ m) (hmn : m < n)
    (hr : 1 ≤ r) (hrd : r ≤ 2 * m - 1) (hn : n = q * (2 * m - 1) + r + 2) :
    winning adj (legal m) (PathUpperArithmetic.sweepCount n m q r)
      (fun _ : Fin n => True) := by
  have hprod : (q * (2 * m - 1)) % 2 = q % 2 := by
    rw [Nat.mul_mod]
    have hd : (2 * m - 1) % 2 = 1 := by omega
    rw [hd, Nat.mul_one, Nat.mod_mod]
  have hpar : (n % 2 + q) % 2 = r % 2 := by omega
  have run := first_batches (n := n) (m := m) (q := q) (R := n - 1) (p := n % 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hrend : n - 1 - q * (2 * m - 1) = r + 1 := by omega
  rw [hrend, hpar] at run
  have start : (fun v : Fin n => parityPrefix (n - 1) v ∨ fullParity (n % 2) v) =
      (fun _ => True) := by
    rw [full_parity_prefix (by omega)]
    exact full_prefix_union (by omega)
  rw [start] at run
  have win := run.then_winning (joining_phase n m q r hm hmn hr hrd hn)
  have count : q + (remaining n m q r + 1) =
      PathUpperArithmetic.sweepCount n m q r := by
    change q + ((if fast n m r then q else q + 1) + 1) =
      if fast n m r then 2 * q + 1 else 2 * q + 2
    by_cases hf : fast n m r <;> simp only [hf, ↓reduceIte] <;> omega
  rw [count] at win
  exact win

theorem corrected_ceiling_upper (n m : Nat) (hm : 2 ≤ m) (hmn : m < n) :
    winning adj (legal m) (PathUpperArithmetic.correctedCeiling n m)
      (fun _ : Fin n => True) := by
  obtain ⟨hr, hrd, hn⟩ := PathUpperArithmetic.canonical_parameters n m hm hmn
  have hw := sweep_upper n m ((n - 3) / (2 * m - 1))
    ((n - 3) % (2 * m - 1) + 1) hm hmn hr hrd hn
  rw [PathUpperArithmetic.canonical_sweepCount_eq_correctedCeiling n m hm hmn] at hw
  exact hw

end Princess.PathSweep

#print axioms Princess.PathSweep.prefix_sweep
#print axioms Princess.PathSweep.first_batches
#print axioms Princess.PathSweep.finish_first
#print axioms Princess.PathSweep.sweep_upper
#print axioms Princess.PathSweep.corrected_ceiling_upper
