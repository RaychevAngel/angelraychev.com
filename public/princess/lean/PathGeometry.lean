import CaptureRecurrence
import LadderCardinality

/-! Physical open-path geometry. Rooms are zero-based Fin n; parity prefixes
use the ordinary proof's one-based frontier r. No optimality formula is assumed.
-/

namespace Princess.PathGeometry

open Princess.LadderCardinality
open Princess.CaptureRecurrence

def adj {n : Nat} (u v : Fin n) : Prop :=
  u.val + 1 = v.val ∨ v.val + 1 = u.val

instance {n : Nat} (u v : Fin n) : Decidable (adj u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

def parityPrefix {n : Nat} (r : Nat) : Region (Fin n) :=
  fun v => v.val < r ∧ (v.val + 1) % 2 = r % 2

def reflected {n : Nat} (B : Region (Fin n)) : Region (Fin n) := fun v => B v.rev

theorem adj_symm {n : Nat} (u v : Fin n) : adj u v ↔ adj v u := by
  exact Or.comm

theorem no_dead_ends {n : Nat} (hn : 2 ≤ n) (v : Fin n) : ∃ w, adj v w := by
  by_cases h : v.val + 1 < n
  · exact ⟨⟨v.val + 1, h⟩, Or.inl rfl⟩
  · refine ⟨⟨v.val - 1, by have := v.isLt; omega⟩, Or.inr ?_⟩
    have := v.isLt
    change v.val - 1 + 1 = v.val
    omega

theorem adj_parity {n : Nat} (u v : Fin n) (h : adj u v) :
    (u.val + 1) % 2 ≠ (v.val + 1) % 2 := by
  rcases h with h | h <;> omega

theorem adj_reflection {n : Nat} (u v : Fin n) : adj u.rev v.rev ↔ adj u v := by
  have hu := u.isLt
  have hv := v.isLt
  simp only [adj, Fin.val_rev]
  omega

theorem prefix_zero {n : Nat} : parityPrefix (n := n) 0 = (fun _ => False) := by
  funext v
  exact propext (by simp [parityPrefix])

theorem prefix_subset {n r s : Nat} (hrs : r ≤ s) (hpar : r % 2 = s % 2) :
    Subset (parityPrefix (n := n) r) (parityPrefix s) := by
  rintro v ⟨hv, hp⟩
  exact ⟨Nat.lt_of_lt_of_le hv hrs, hp.trans hpar⟩

theorem move_prefix {n r : Nat} (hr : 1 ≤ r) (hrn : r < n) :
    Princess.move adj (parityPrefix (n := n) r) = parityPrefix (r + 1) := by
  funext v
  apply propext
  constructor
  · rintro ⟨u, ⟨hu, hp⟩, hadj⟩
    change v.val < r + 1 ∧ (v.val + 1) % 2 = (r + 1) % 2
    rcases hadj with he | he <;> omega
  · rintro ⟨hv, hp⟩
    by_cases hzero : v.val = 0
    · have hr2 : 2 ≤ r := by omega
      refine ⟨⟨1, by omega⟩, ?_, Or.inr ?_⟩
      · change 1 < r ∧ (1 + 1) % 2 = r % 2
        omega
      · change v.val + 1 = 1
        omega
    · refine ⟨⟨v.val - 1, by have := v.isLt; omega⟩, ?_, Or.inl ?_⟩
      · change v.val - 1 < r ∧ (v.val - 1 + 1) % 2 = r % 2
        omega
      · change v.val - 1 + 1 = v.val
        omega

theorem move_full_prefix {n : Nat} (hn : 2 ≤ n) :
    Princess.move adj (parityPrefix (n := n) n) = parityPrefix (n - 1) := by
  funext v
  apply propext
  constructor
  · rintro ⟨u, ⟨hu, hp⟩, hadj⟩
    have hv := v.isLt
    change v.val < n - 1 ∧ (v.val + 1) % 2 = (n - 1) % 2
    rcases hadj with he | he <;> omega
  · rintro ⟨hv, hp⟩
    refine ⟨⟨v.val + 1, by omega⟩, ?_, Or.inr rfl⟩
    change v.val + 1 < n ∧ (v.val + 1 + 1) % 2 = n % 2
    omega

theorem full_prefix_union {n : Nat} (hn : 1 ≤ n) :
    (fun v : Fin n => parityPrefix (n - 1) v ∨ parityPrefix n v) = (fun _ => True) := by
  funext v
  apply propext
  constructor
  · exact fun _ => True.intro
  · intro _
    have hv := v.isLt
    simp only [parityPrefix]
    omega

theorem full_prefix_disjoint {n : Nat} (hn : 1 ≤ n) (v : Fin n) :
    ¬ (parityPrefix (n - 1) v ∧ parityPrefix n v) := by
  simp only [parityPrefix]
  omega

theorem card_parity (n p : Nat) (hp : p < 2) :
    card (fun v : Fin n => v.val % 2 = p) = (n + 1 - p) / 2 := by
  classical
  induction n with
  | zero => simp [card, cardOn]; omega
  | succ n ih =>
      unfold card
      rw [List.finRange_succ_last, cardOn_append, cardOn_map, cardOn_cons]
      have same : cardOn (List.finRange n) (fun v => v.castSucc.val % 2 = p) =
          card (fun v : Fin n => v.val % 2 = p) := rfl
      rw [same, ih]
      simp only [cardOn, List.countP_nil, Fin.val_last]
      split <;> omega

theorem card_full_prefix (n : Nat) :
    card (parityPrefix (n := n) n) = (n + 1) / 2 := by
  have hEq : parityPrefix (n := n) n = (fun v : Fin n => v.val % 2 = (n + 1) % 2) := by
    funext v
    apply propext
    have hv := v.isLt
    simp only [parityPrefix]
    omega
  rw [hEq, card_parity n ((n + 1) % 2) (by omega)]
  omega

theorem card_prefix {n : Nat} (r : Nat) (hrn : r ≤ n) :
    card (parityPrefix (n := n) r) = (r + 1) / 2 := by
  classical
  induction n with
  | zero =>
      have : r = 0 := by omega
      subst r
      simp [card, cardOn]
  | succ n ih =>
      by_cases h : r ≤ n
      · unfold card
        rw [List.finRange_succ_last, cardOn_append, cardOn_map, cardOn_cons]
        have same : cardOn (List.finRange n) (fun v => parityPrefix r v.castSucc) =
            card (parityPrefix (n := n) r) := rfl
        rw [same, ih h]
        simp only [parityPrefix, Fin.val_last, cardOn, List.countP_nil]
        have hnot : ¬ n < r := by omega
        simp [hnot]
      · have hr : r = n + 1 := by omega
        subst r
        exact card_full_prefix (n + 1)

def top {n : Nat} (r b : Nat) : Region (Fin n) :=
  fun v => parityPrefix r v ∧ ¬ parityPrefix (r - 2 * b) v

theorem cut_prefix {n r b : Nat} :
    (fun v : Fin n => parityPrefix r v ∧ ¬ top r b v) = parityPrefix (r - 2 * b) := by
  funext v
  apply propext
  constructor
  · rintro ⟨hp, ht⟩
    exact Classical.byContradiction (fun h => ht ⟨hp, h⟩)
  · intro hp
    have sub : parityPrefix r v := by
      have hv := hp.1
      have hpar := hp.2
      change v.val < r ∧ (v.val + 1) % 2 = r % 2
      omega
    exact ⟨sub, fun h => h.2 hp⟩

theorem card_top {n : Nat} (r b : Nat) (hrn : r ≤ n) :
    card (top (n := n) r b) ≤ b := by
  have split := cardOn_split (List.finRange n) (parityPrefix r) (parityPrefix (r - 2 * b))
  have sub : (fun v : Fin n => parityPrefix r v ∧ parityPrefix (r - 2 * b) v) =
      parityPrefix (r - 2 * b) := by
    funext v
    apply propext
    constructor
    · exact And.right
    · intro hp
      have hv := hp.1
      have hpar := hp.2
      exact ⟨⟨by omega, by omega⟩, hp⟩
  change card (parityPrefix (n := n) r) =
    card (fun v => parityPrefix r v ∧ parityPrefix (r - 2 * b) v) + card (top r b) at split
  rw [sub, card_prefix r hrn, card_prefix (r - 2 * b) (by omega)] at split
  omega

theorem next_top_survives {n r b : Nat} (hrn : r ≤ n) (hb : 1 ≤ b)
    (hsurv : 2 * b < r) :
    next adj (parityPrefix (n := n) r) (top r b) = parityPrefix (r - 2 * b + 1) := by
  unfold next
  rw [cut_prefix]
  exact move_prefix (by omega) (by omega)

theorem next_top_finishes {n r b : Nat} (hfinish : r ≤ 2 * b) :
    Empty (next adj (parityPrefix (n := n) r) (top r b)) := by
  unfold next
  rw [cut_prefix]
  have hz : r - 2 * b = 0 := by omega
  rw [hz, prefix_zero]
  rintro v ⟨u, hu, _⟩
  exact hu

theorem next_reflected {n : Nat} (B S : Region (Fin n)) :
    next adj (reflected B) (reflected S) = reflected (next adj B S) := by
  funext v
  apply propext
  constructor
  · rintro ⟨u, ⟨hu, hs⟩, hadj⟩
    exact ⟨u.rev, ⟨hu, hs⟩, (adj_reflection u v).mpr hadj⟩
  · rintro ⟨u, ⟨hu, hs⟩, hadj⟩
    refine ⟨u.rev, ?_, ?_⟩
    · simpa only [reflected, Fin.rev_rev] using And.intro hu hs
    · have := (adj_reflection u v.rev).mpr hadj
      simpa only [Fin.rev_rev] using this

theorem card_reflected {n : Nat} (B : Region (Fin n)) :
    card (reflected B) = card B := by
  classical
  have nd : ((List.finRange n).map Fin.rev).Nodup := by
    apply List.Pairwise.map (R := fun a b : Fin n => a ≠ b) Fin.rev
      (fun a b hab heq => hab (by simpa only [Fin.rev_rev] using congrArg Fin.rev heq))
    exact List.nodup_finRange n
  have perm : ((List.finRange n).map Fin.rev).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup nd (List.nodup_finRange n)).mpr
    intro v
    simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
    exact ⟨v.rev, Fin.rev_rev v⟩
  change cardOn (List.finRange n) (fun v => B v.rev) = cardOn (List.finRange n) B
  rw [← cardOn_map (List.finRange n) Fin.rev B]
  exact perm.countP_eq _

end Princess.PathGeometry

#print axioms Princess.PathGeometry.move_prefix
#print axioms Princess.PathGeometry.card_prefix
#print axioms Princess.PathGeometry.next_top_survives
#print axioms Princess.PathGeometry.card_top
#print axioms Princess.PathGeometry.card_reflected
