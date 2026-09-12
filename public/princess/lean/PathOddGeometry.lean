import PathCohorts

/-! Odd path neighborhood bounds from matchings with one exposed room.
The support is arbitrary; no sweep or interval hypothesis is used. -/
namespace Princess.PathOddGeometry
open Princess.PathGeometry Princess.PathSweep Princess.PathLowerGeometry
open Princess.PathCohorts Princess.LadderCardinality Princess.CaptureRecurrence

def mateVal (g x : Nat) : Nat :=
  if x < g then if x % 2 = 0 then x + 1 else x - 1
  else if g < x then if x % 2 = 0 then x - 1 else x + 1
  else x

theorem mateVal_bound {n : Nat} (ho : n % 2 = 1) (g x : Nat)
    (hg : g < n) (he : g % 2 = 0) (hx : x < n) : mateVal g x < n := by
  unfold mateVal
  split <;> split <;> (try split) <;> omega

theorem mateVal_involutive (g x : Nat) (he : g % 2 = 0) :
    mateVal g (mateVal g x) = x := by
  unfold mateVal
  split
  · rename_i lt
    split
    · rename_i par
      have lt' : x + 1 < g := by omega
      have par' : (x + 1) % 2 ≠ 0 := by omega
      simp only [lt', par', ite_true, ite_false]
      omega
    · rename_i par
      have lt' : x - 1 < g := by omega
      have par' : (x - 1) % 2 = 0 := by omega
      simp only [lt', par', ite_true, ite_false]
      omega
  · rename_i nlt
    split
    · rename_i gt
      split
      · rename_i par
        have nlt' : ¬ x - 1 < g := by omega
        have gt' : g < x - 1 := by omega
        have par' : (x - 1) % 2 ≠ 0 := by omega
        simp only [nlt', gt', par', ite_true, ite_false]
        omega
      · rename_i par
        have nlt' : ¬ x + 1 < g := by omega
        have gt' : g < x + 1 := by omega
        have par' : (x + 1) % 2 = 0 := by omega
        simp only [nlt', gt', par', ite_true, ite_false]
        omega
    · have eq : x = g := by omega
      subst x
      simp

def oddMate {n : Nat} (ho : n % 2 = 1) (g : Fin n) (he : g.val % 2 = 0)
    (v : Fin n) : Fin n := ⟨mateVal g.val v.val,
      mateVal_bound ho g.val v.val g.isLt he v.isLt⟩

theorem oddMate_involutive {n : Nat} (ho : n % 2 = 1) (g : Fin n)
    (he : g.val % 2 = 0) (v : Fin n) : oddMate ho g he (oddMate ho g he v) = v :=
  Fin.ext (mateVal_involutive g.val v.val he)

theorem oddMate_edge {n : Nat} (ho : n % 2 = 1) (g : Fin n)
    (he : g.val % 2 = 0) (v : Fin n) (hne : v ≠ g) : adj v (oddMate ho g he v) := by
  have diff : v.val ≠ g.val := fun h => hne (Fin.ext h)
  change v.val + 1 = mateVal g.val v.val ∨ mateVal g.val v.val + 1 = v.val
  unfold mateVal
  split <;> split <;> (try split) <;> omega

theorem odd_missing_matching {n : Nat} (ho : n % 2 = 1) (R : Region (Fin n))
    (g : Fin n) (he : g.val % 2 = 0) (missing : ¬ R g) :
    card R ≤ card (Princess.move adj R) := by
  apply matching_lower (oddMate ho g he) (oddMate_involutive ho g he) R
  intro v hv
  exact oddMate_edge ho g he v (by intro eq; exact missing (eq ▸ hv))

theorem odd_neighborhood_lower {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (R : Region (Fin n)) : min (card R) (n / 2) ≤ card (Princess.move adj R) := by
  classical
  by_cases missing : ∃ g : Fin n, g.val % 2 = 0 ∧ ¬ R g
  · obtain ⟨g, he, hmiss⟩ := missing
    exact Nat.le_trans (Nat.min_le_left _ _) (odd_missing_matching ho R g he hmiss)
  · have all : ∀ g : Fin n, g.val % 2 = 0 → R g := by
      intro g he
      apply Classical.byContradiction
      exact fun h => missing ⟨g, he, h⟩
    have sub : Subset (fullParity (n := n) 0) (Princess.move adj R) := by
      intro v hv
      obtain ⟨u, hadj⟩ := no_dead_ends hn v
      have hp := adj_parity v u hadj
      have hu : u.val % 2 = 0 := by change (v.val + 1) % 2 = 0 at hv; omega
      exact ⟨u, all u hu, (adj_symm v u).mp hadj⟩
    have bound := card_mono _ _ sub
    rw [full_parity_card n 0 (by omega)] at bound
    exact Nat.le_trans (Nat.min_le_right _ _) (by simpa using bound)

/-- Any nonempty set in the smaller color class has strictly more neighbors. -/
theorem odd_small_expands {n : Nat} (hn : 2 ≤ n) (ho : n % 2 = 1)
    (R : Region (Fin n)) (small : ∀ v, R v → v.val % 2 = 1) (hne : 0 < card R) :
    card R + 1 ≤ card (Princess.move adj R) := by
  let g : Fin n := ⟨0, by omega⟩
  have he : g.val % 2 = 0 := rfl
  have missing : ¬ R g := by intro h; have := small g h; change 0 % 2 = 1 at this; omega
  have lower := odd_missing_matching ho R g he missing
  suffices neq : card (Princess.move adj R) ≠ card R by omega
  intro equal
  have closed := matching_equality_closed (oddMate ho g he)
    (oddMate_involutive ho g he) R
    (fun v hv => oddMate_edge ho g he v (by intro e; exact missing (e ▸ hv))) equal
  have impossible : ∀ k, ∀ v : Fin n, v.val = k → ¬ R v := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro v eq hv
        have hp := small v hv
        have hv0 : 0 < v.val := by omega
        let u : Fin n := ⟨v.val - 1, by have := v.isLt; omega⟩
        have hadj : adj v u := Or.inr (by change v.val - 1 + 1 = v.val; omega)
        have next := closed v u hv hadj
        have lt : (oddMate ho g he u).val < v.val := by
          change mateVal 0 (v.val - 1) < v.val
          unfold mateVal
          split <;> split <;> (try split) <;> omega
        exact ih _ (by omega) _ rfl next
  obtain ⟨v, hv⟩ := (card_pos R).mp hne
  exact impossible v.val v rfl hv

end Princess.PathOddGeometry
#print axioms Princess.PathOddGeometry.odd_neighborhood_lower
#print axioms Princess.PathOddGeometry.odd_small_expands
