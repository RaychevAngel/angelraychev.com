import PathUpper

/-! Arbitrary-support lower geometry for paths. The matching arguments here
make no prefix assumption about the unknown target's possible locations.
-/

namespace Princess.PathLowerGeometry

open Princess.PathGeometry
open Princess.PathSweep
open Princess.LadderCardinality
open Princess.CaptureRecurrence

theorem card_involution {n : Nat} (f : Fin n → Fin n)
    (hinv : ∀ v, f (f v) = v) (B : Region (Fin n)) :
    card (fun v => B (f v)) = card B := by
  classical
  have nd : ((List.finRange n).map f).Nodup := by
    apply List.Pairwise.map (R := fun a b : Fin n => a ≠ b) f
      (fun a b hab heq => hab (by simpa only [hinv] using congrArg f heq))
    exact List.nodup_finRange n
  have perm : ((List.finRange n).map f).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup nd (List.nodup_finRange n)).mpr
    intro v
    simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
    exact ⟨f v, hinv v⟩
  change cardOn (List.finRange n) (fun v => B (f v)) = cardOn (List.finRange n) B
  rw [← cardOn_map (List.finRange n) f B]
  exact perm.countP_eq _

theorem card_subset_equality {n : Nat} (A B : Region (Fin n))
    (sub : Subset A B) (equal : card A = card B) : Subset B A := by
  intro v hv
  apply Classical.byContradiction
  intro hnot
  have strict := cardOn_strict (List.finRange n) A B
    (fun u _ hu => sub u hu) ⟨v, List.mem_finRange v, hv, hnot⟩
  change card A < card B at strict
  omega

theorem matching_lower {n : Nat} (f : Fin n → Fin n)
    (hinv : ∀ v, f (f v) = v) (R : Region (Fin n))
    (edge : ∀ v, R v → adj v (f v)) :
    card R ≤ card (Princess.move adj R) := by
  have included : Subset (fun v => R (f v)) (Princess.move adj R) := by
    intro v hv
    refine ⟨f v, hv, ?_⟩
    simpa only [hinv] using edge (f v) hv
  have h := card_mono _ _ included
  rw [card_involution f hinv R] at h
  exact h

theorem matching_equality_closed {n : Nat} (f : Fin n → Fin n)
    (hinv : ∀ v, f (f v) = v) (R : Region (Fin n))
    (edge : ∀ v, R v → adj v (f v))
    (equal : card (Princess.move adj R) = card R) :
    ∀ u v, R u → adj u v → R (f v) := by
  have included : Subset (fun v => R (f v)) (Princess.move adj R) := by
    intro v hv
    refine ⟨f v, hv, ?_⟩
    simpa only [hinv] using edge (f v) hv
  have eqcard : card (fun v => R (f v)) = card (Princess.move adj R) := by
    rw [card_involution f hinv R, equal]
  have reverse := card_subset_equality _ _ included eqcard
  exact fun u v hu he => reverse v ⟨u, hu, he⟩

def evenMate {n : Nat} (he : n % 2 = 0) (v : Fin n) : Fin n :=
  if hz : v.val % 2 = 0 then ⟨v.val + 1, by have := v.isLt; omega⟩
  else ⟨v.val - 1, by have := v.isLt; omega⟩

theorem evenMate_edge {n : Nat} (he : n % 2 = 0) (v : Fin n) :
    adj v (evenMate he v) := by
  unfold evenMate
  split
  · exact Or.inl rfl
  · right
    change v.val - 1 + 1 = v.val
    omega

theorem evenMate_involutive {n : Nat} (he : n % 2 = 0) (v : Fin n) :
    evenMate he (evenMate he v) = v := by
  apply Fin.ext
  unfold evenMate
  split
  · rename_i hz
    have ho : (v.val + 1) % 2 ≠ 0 := by omega
    simp only [ho, ↓reduceDIte]
    omega
  · rename_i ho
    have hz : (v.val - 1) % 2 = 0 := by omega
    simp only [hz, ↓reduceDIte]
    omega

theorem even_neighborhood_nonshrinking {n : Nat} (he : n % 2 = 0)
    (R : Region (Fin n)) : card R ≤ card (Princess.move adj R) :=
  matching_lower (evenMate he) (evenMate_involutive he) R (fun v _ => evenMate_edge he v)

theorem even_equality_closed {n : Nat} (he : n % 2 = 0) (R : Region (Fin n))
    (equal : card (Princess.move adj R) = card R) :
    ∀ u v, R u → adj u v → R (evenMate he v) :=
  matching_equality_closed (evenMate he) (evenMate_involutive he) R
    (fun v _ => evenMate_edge he v) equal

/-- If equality holds, occupation of an odd-indexed room propagates upward by
two. This is the endpoint-anchored structure forced by a zero surplus. -/
theorem even_equality_step_up {n : Nat} (he : n % 2 = 0) (R : Region (Fin n))
    (equal : card (Princess.move adj R) = card R) (u : Fin n)
    (hu : R u) (hodd : u.val % 2 = 1) (hbound : u.val + 2 < n) :
    R ⟨u.val + 2, hbound⟩ := by
  let v : Fin n := ⟨u.val + 1, by omega⟩
  have h := even_equality_closed he R equal u v hu (Or.inl rfl)
  have eq : evenMate he v = ⟨u.val + 2, hbound⟩ := by
    apply Fin.ext
    have hp : v.val % 2 = 0 := by dsimp [v]; omega
    simp only [evenMate, hp, ↓reduceDIte]
    rfl
  rw [eq] at h
  exact h

/-- At equality, a next support containing the left endpoint forces the
entire odd-indexed starting parity. No assumed interval form is used. -/
theorem even_equality_left_full {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (R : Region (Fin n)) (equal : card (Princess.move adj R) = card R)
    (left : Princess.move adj R ⟨0, by omega⟩) :
    ∀ v : Fin n, v.val % 2 = 1 → R v := by
  obtain ⟨a, ha, hadj⟩ := left
  change a.val + 1 = 0 ∨ 0 + 1 = a.val at hadj
  have ha1 : a.val = 1 := by rcases hadj with h | h <;> omega
  have base : R ⟨1, by omega⟩ := by
    have eq : a = ⟨1, by omega⟩ := Fin.ext ha1
    simpa only [eq] using ha
  have all : ∀ k, ∀ hk : 2 * k + 1 < n, R ⟨2 * k + 1, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using base
    | succ k ih =>
        intro hk
        have hbound : 2 * k + 1 < n := by omega
        have prev := ih hbound
        have hstep : 2 * k + 1 + 2 < n := by omega
        have next := even_equality_step_up he R equal ⟨2 * k + 1, hbound⟩
          prev (by change (2 * k + 1) % 2 = 1; omega) hstep
        have eq : (⟨2 * k + 1 + 2, hstep⟩ : Fin n) =
            ⟨2 * (k + 1) + 1, hk⟩ := Fin.ext (by
              change 2 * k + 1 + 2 = 2 * (k + 1) + 1
              omega)
        change R ⟨2 * k + 1 + 2, hstep⟩ at next
        rw [eq] at next
        exact next
  intro v hv
  have hval : 2 * (v.val / 2) + 1 = v.val := by omega
  have h := all (v.val / 2) (by have := v.isLt; omega)
  have eq : (⟨2 * (v.val / 2) + 1, by have := v.isLt; omega⟩ : Fin n) = v :=
    Fin.ext hval
  simpa only [eq] using h

theorem move_reflected {n : Nat} (R : Region (Fin n)) :
    Princess.move adj (reflected R) = reflected (Princess.move adj R) := by
  funext v
  apply propext
  constructor
  · rintro ⟨u, hu, hadj⟩
    exact ⟨u.rev, hu, (adj_reflection u v).mpr hadj⟩
  · rintro ⟨u, hu, hadj⟩
    refine ⟨u.rev, ?_, ?_⟩
    · simpa only [reflected, Fin.rev_rev] using hu
    · have h := (adj_reflection u v.rev).mpr hadj
      simpa only [Fin.rev_rev] using h

theorem even_equality_right_full {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (R : Region (Fin n)) (equal : card (Princess.move adj R) = card R)
    (right : Princess.move adj R ⟨n - 1, by omega⟩) :
    ∀ v : Fin n, v.val % 2 = 0 → R v := by
  have eqRef : card (Princess.move adj (reflected R)) = card (reflected R) := by
    rw [move_reflected, card_reflected, card_reflected, equal]
  have left : Princess.move adj (reflected R) ⟨0, by omega⟩ := by
    rw [move_reflected]
    change Princess.move adj R (Fin.rev ⟨0, by omega⟩)
    have e : Fin.rev (⟨0, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
    rw [e]; exact right
  have all := even_equality_left_full hn he (reflected R) eqRef left
  intro v hv
  have h := all v.rev (by simp only [Fin.val_rev]; have := v.isLt; omega)
  simpa only [reflected, Fin.rev_rev] using h

theorem even_zero_avoids_ends {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (R : Region (Fin n)) (equal : card (Princess.move adj R) = card R)
    (small : card R < n / 2) :
    ¬ Princess.move adj R ⟨0, by omega⟩ ∧
      ¬ Princess.move adj R ⟨n - 1, by omega⟩ := by
  constructor
  · intro hleft
    have incl := card_mono (fun v : Fin n => v.val % 2 = 1) R
      (even_equality_left_full hn he R equal hleft)
    rw [card_parity n 1 (by decide)] at incl
    omega
  · intro hright
    have incl := card_mono (fun v : Fin n => v.val % 2 = 0) R
      (even_equality_right_full hn he R equal hright)
    rw [card_parity n 0 (by decide)] at incl
    omega

theorem even_equality_odd_terminal {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (R : Region (Fin n)) (equal : card (Princess.move adj R) = card R)
    (u : Fin n) (hu : R u) (hodd : u.val % 2 = 1) :
    R ⟨n - 1, by omega⟩ := by
  have reach : ∀ k, ∀ hk : u.val + 2 * k < n, R ⟨u.val + 2 * k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using hu
    | succ k ih =>
        intro hk
        have hprev : u.val + 2 * k < n := by omega
        have hstep : u.val + 2 * k + 2 < n := by omega
        have h := even_equality_step_up he R equal ⟨u.val + 2 * k, hprev⟩
          (ih hprev) (by change (u.val + 2 * k) % 2 = 1; omega) hstep
        have e : (⟨u.val + 2 * k + 2, hstep⟩ : Fin n) =
            ⟨u.val + 2 * (k + 1), hk⟩ := Fin.ext (by
              change u.val + 2 * k + 2 = u.val + 2 * (k + 1)
              omega)
        change R ⟨u.val + 2 * k + 2, hstep⟩ at h
        rw [e] at h
        exact h
  have hv := u.isLt
  have heq : u.val + 2 * ((n - 1 - u.val) / 2) = n - 1 := by omega
  have h := reach ((n - 1 - u.val) / 2) (by omega)
  have e : (⟨u.val + 2 * ((n - 1 - u.val) / 2), by omega⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := Fin.ext heq
  simpa only [e] using h

def endpointless {n : Nat} (R : Region (Fin n)) : Prop :=
  ∀ v, R v → 0 < v.val ∧ v.val + 1 < n

theorem even_endpointless_expands {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (R : Region (Fin n)) (hne : 0 < card R) (hend : endpointless R) :
    card R + 1 ≤ card (Princess.move adj R) := by
  have lower := even_neighborhood_nonshrinking he R
  suffices hnot : card (Princess.move adj R) ≠ card R by omega
  intro eq
  obtain ⟨u, hu⟩ := (card_pos R).mp hne
  by_cases hodd : u.val % 2 = 1
  · have hlast := even_equality_odd_terminal hn he R eq u hu hodd
    have h := hend ⟨n - 1, by omega⟩ hlast
    change 0 < n - 1 ∧ n - 1 + 1 < n at h
    omega
  · have eqRef : card (Princess.move adj (reflected R)) = card (reflected R) := by
      rw [move_reflected, card_reflected, card_reflected, eq]
    have hoddRef : u.rev.val % 2 = 1 := by
      simp only [Fin.val_rev]
      have := u.isLt
      omega
    have huRef : reflected R u.rev := by simpa only [reflected, Fin.rev_rev] using hu
    have last := even_equality_odd_terminal hn he (reflected R) eqRef u.rev huRef hoddRef
    have hv : (Fin.rev (⟨n - 1, by omega⟩ : Fin n)).val = 0 := by
      simp only [Fin.val_rev]; omega
    have h := hend _ last
    rw [hv] at h
    omega

theorem even_zero_endpointless {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0)
    (R : Region (Fin n)) (equal : card (Princess.move adj R) = card R)
    (small : card R < n / 2) : endpointless (Princess.move adj R) := by
  obtain ⟨left, right⟩ := even_zero_avoids_ends hn he R equal small
  intro v hv
  have bound := v.isLt
  have hzero : v.val ≠ 0 := by
    intro h
    have e : v = ⟨0, by omega⟩ := Fin.ext h
    exact left (e ▸ hv)
  have hlast : v.val ≠ n - 1 := by
    intro h
    have e : v = ⟨n - 1, by omega⟩ := Fin.ext h
    exact right (e ▸ hv)
  omega

end Princess.PathLowerGeometry

#print axioms Princess.PathLowerGeometry.even_neighborhood_nonshrinking
#print axioms Princess.PathLowerGeometry.even_equality_left_full
#print axioms Princess.PathLowerGeometry.even_zero_endpointless
#print axioms Princess.PathLowerGeometry.even_endpointless_expands
