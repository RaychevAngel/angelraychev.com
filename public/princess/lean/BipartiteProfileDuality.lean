import LadderCardinality
import ProfileInverse

/-! Actual finite bipartite neighborhood profiles, complement duality, and
the one-unit difference of maximum surpluses for part sizes m+1 and m.
The graph is an arbitrary relation between the two finite parts. No profile
optimality certificate, nesting hypothesis, or hunter-number axiom is assumed. -/
namespace Princess.BipartiteProfileDuality
open Princess.LadderCardinality
open Princess.ProfileInverse

theorem card_empty (n : Nat) : card (fun _ : Fin n => False) = 0 := by
  classical
  simp [card, cardOn]

theorem card_complement {n : Nat} (P : Fin n → Prop) :
    card (fun x => ¬ P x) = n - card P := by
  have h := cardOn_split (List.finRange n) (fun _ => True) P
  have full : card (fun _ : Fin n => True) = n := (card_full_iff _).mpr (by simp)
  have first : cardOn (List.finRange n) (fun x => True ∧ P x) = card P := by
    apply cardOn_congr
    simp
  have second : cardOn (List.finRange n) (fun x => True ∧ ¬ P x) =
      card (fun x => ¬ P x) := by
    apply cardOn_congr
    simp
  change card (fun _ : Fin n => True) = _ at h
  rw [full, first, second] at h
  omega

theorem card_succ {n : Nat} (P : Fin (n+1) → Prop) [Decidable (P 0)] :
    card P = card (fun x : Fin n => P x.succ) + if P 0 then 1 else 0 := by
  classical
  unfold card
  rw [List.finRange_succ, cardOn_cons, cardOn_map]

/-- Every finite set contains a subset of each smaller cardinality. -/
theorem subset_of_card {n : Nat} (P : Fin n → Prop) (k : Nat)
    (hk : k ≤ card P) :
    ∃ Q : Fin n → Prop, (∀ x, Q x → P x) ∧ card Q = k := by
  classical
  induction n with
  | zero =>
      have hc := card_le P
      have : k = 0 := by omega
      exact ⟨P, fun _ h => h, by omega⟩
  | succ n ih =>
      let tail : Fin n → Prop := fun x => P x.succ
      have count := card_succ P
      change card P = card tail + if P 0 then 1 else 0 at count
      by_cases htail : k ≤ card tail
      · obtain ⟨Q, hsub, hcard⟩ := ih tail htail
        let Q' : Fin (n+1) → Prop := Fin.cases False Q
        refine ⟨Q', ?_, ?_⟩
        · intro x
          refine Fin.cases ?_ (fun y => ?_) x
          · exact False.elim
          · exact hsub y
        · rw [card_succ Q']
          simpa [Q'] using hcard
      · exact ⟨P, fun _ h => h, by split at count <;> omega⟩

def hood {e m : Nat} (R : Fin e → Fin m → Prop) (S : Fin e → Prop) :
    Fin m → Prop := fun y => ∃ x, S x ∧ R x y

def reverse {e m : Nat} (R : Fin e → Fin m → Prop) : Fin m → Fin e → Prop :=
  fun y x => R x y

theorem hood_mono {e m : Nat} (R : Fin e → Fin m → Prop)
    (P Q : Fin e → Prop) (h : ∀ x, P x → Q x) :
    ∀ y, hood R P y → hood R Q y := by
  rintro y ⟨x, hx, he⟩
  exact ⟨x, h x hx, he⟩

private theorem least_exists (P : Nat → Prop) (hex : ∃ n, P n) :
    ∃ n, P n ∧ ∀ k, P k → n ≤ k := by
  classical
  have h : ∀ n, P n → ∃ a, P a ∧ ∀ k, P k → a ≤ k := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro hn
        by_cases smaller : ∃ k, k < n ∧ P k
        · obtain ⟨k, hk, hp⟩ := smaller
          exact ih k hk hp
        · refine ⟨n, hn, ?_⟩
          intro k hk
          by_cases hkn : n ≤ k
          · exact hkn
          · exact False.elim (smaller ⟨k, by omega, hk⟩)
  obtain ⟨n, hn⟩ := hex
  exact h n hn

private theorem profile_exists {e m : Nat} (R : Fin e → Fin m → Prop)
    (k : Nat) (hk : k ≤ e) :
    ∃ q, (∃ S, card S = k ∧ card (hood R S) = q) ∧
      ∀ v, (∃ S, card S = k ∧ card (hood R S) = v) → q ≤ v := by
  apply least_exists
  exact ⟨card (hood R (suffix (n := e) k)), suffix k, suffix_card hk, rfl⟩

noncomputable def profile {e m : Nat} (R : Fin e → Fin m → Prop) (k : Nat) : Nat :=
  if hk : k ≤ e then Classical.choose (profile_exists R k hk) else 0

theorem profile_attained {e m : Nat} (R : Fin e → Fin m → Prop)
    (k : Nat) (hk : k ≤ e) :
    ∃ S, card S = k ∧ card (hood R S) = profile R k := by
  unfold profile
  rw [dif_pos hk]
  exact (Classical.choose_spec (profile_exists R k hk)).1

theorem profile_lower {e m : Nat} (R : Fin e → Fin m → Prop)
    (S : Fin e → Prop) : profile R (card S) ≤ card (hood R S) := by
  have hk := card_le S
  unfold profile
  rw [dif_pos hk]
  exact (Classical.choose_spec (profile_exists R (card S) hk)).2 _ ⟨S, rfl, rfl⟩

theorem profile_bound {e m : Nat} (R : Fin e → Fin m → Prop)
    (k : Nat) (hk : k ≤ e) : profile R k ≤ m := by
  obtain ⟨S, _, h⟩ := profile_attained R k hk
  rw [← h]
  exact card_le _

theorem profile_zero {e m : Nat} (R : Fin e → Fin m → Prop) : profile R 0 = 0 := by
  have h := profile_lower R (fun _ => False)
  rw [card_empty] at h
  have hc : card (hood R (fun _ => False)) = 0 := by
    classical
    simp [hood, card, cardOn]
  omega

theorem profile_monotone {e m : Nat} (R : Fin e → Fin m → Prop)
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ e) : profile R a ≤ profile R b := by
  obtain ⟨S, hc, hn⟩ := profile_attained R b hb
  obtain ⟨Q, hsub, hq⟩ := subset_of_card S a (by omega)
  have hl := profile_lower R Q
  have hm := card_mono (hood R Q) (hood R S) (hood_mono R Q S hsub)
  rw [hq] at hl
  omega

theorem profile_positive {e m : Nat} (R : Fin e → Fin m → Prop)
    (noIsolates : ∀ x, ∃ y, R x y) (k : Nat) (hk : 0 < k) (hke : k ≤ e) :
    0 < profile R k := by
  obtain ⟨S, hc, hn⟩ := profile_attained R k hke
  obtain ⟨x, hx⟩ := (card_pos S).mp (by omega)
  obtain ⟨y, hy⟩ := noIsolates x
  have hpos := (card_pos (hood R S)).mpr ⟨y, x, hx, hy⟩
  omega

theorem profile_full {e m : Nat} (R : Fin e → Fin m → Prop)
    (noIsolates : ∀ y, ∃ x, R x y) : profile R e = m := by
  obtain ⟨S, hc, hn⟩ := profile_attained R e (Nat.le_refl _)
  have full := (card_full_iff S).mp hc
  have nh : ∀ y, hood R S y := by
    intro y
    obtain ⟨x, hx⟩ := noIsolates y
    exact ⟨x, full x, hx⟩
  have hcard := (card_full_iff (hood R S)).mpr nh
  omega

/-- Exact duality for the actual minimum-neighborhood profiles of an arbitrary
finite bipartite relation. Isolated vertices are permitted in this identity. -/
theorem profile_duality {e m : Nat} (R : Fin e → Fin m → Prop)
    (y : Nat) (hy : y ≤ m) :
    profile (reverse R) y = e - inverse e (profile R) (m-y) := by
  classical
  let j := inverse e (profile R) (m-y)
  have hj : j ≤ e := inverse_le e (profile R) (m-y)
  have feasible : profile R j ≤ m-y :=
    inverse_feasible e (profile R) (m-y) (profile_zero R)
  apply Nat.le_antisymm
  · obtain ⟨X, hx, hn⟩ := profile_attained R j hj
    have comp := card_complement (hood R X)
    have room : y ≤ card (fun v => ¬ hood R X v) := by omega
    obtain ⟨Y, hsub, hycard⟩ := subset_of_card (fun v => ¬ hood R X v) y room
    have disjoint : ∀ v, hood (reverse R) Y v → ¬ X v := by
      rintro v ⟨w, hw, he⟩ hv
      exact hsub w hw ⟨v, hv, he⟩
    have lower := profile_lower (reverse R) Y
    rw [hycard] at lower
    have bound := card_mono (hood (reverse R) Y) (fun v => ¬ X v) disjoint
    have compX := card_complement X
    change profile (reverse R) y ≤ e-j
    omega
  · obtain ⟨Y, hycard, hn⟩ := profile_attained (reverse R) y hy
    let X : Fin e → Prop := fun v => ¬ hood (reverse R) Y v
    have hx : card X = e-profile (reverse R) y := by
      have h := card_complement (hood (reverse R) Y)
      change card X = _ at h
      omega
    have disjoint : ∀ v, hood R X v → ¬ Y v := by
      rintro v ⟨w, hw, he⟩ hv
      exact hw ⟨v, hv, he⟩
    have lower := profile_lower R X
    have bound := card_mono (hood R X) (fun v => ¬ Y v) disjoint
    have compY := card_complement Y
    have feas : profile R (card X) ≤ m-y := by omega
    have hjlarge := le_inverse e (profile R) (m-y) (card X) (card_le X) feas
    have hb := profile_bound (reverse R) y hy
    change e-j ≤ profile (reverse R) y
    change card X ≤ j at hjlarge
    omega

/-- Actual no-isolate bipartite graphs with part sizes m+1 and m have maximum
minority neighborhood surplus exactly one greater than the majority surplus. -/
theorem graph_surplus_difference (m : Nat)
    (R : Fin (m+1) → Fin m → Prop) (hm : 0 < m)
    (leftNoIsolates : ∀ x, ∃ y, R x y)
    (rightNoIsolates : ∀ y, ∃ x, R x y) :
    surplus m (profile (reverse R)) = surplus (m+1) (profile R) + 1 := by
  apply dual_surplus m (profile R) (profile (reverse R)) hm
  · exact profile_zero R
  · exact profile_full R rightNoIsolates
  · exact profile_positive R leftNoIsolates
  · exact profile_bound R
  · exact profile_monotone R
  · exact profile_duality R

end Princess.BipartiteProfileDuality
#print axioms Princess.BipartiteProfileDuality.profile_duality
#print axioms Princess.BipartiteProfileDuality.graph_surplus_difference
