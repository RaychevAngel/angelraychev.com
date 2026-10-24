import ExclusionCertificates

/-! Proof-producing finite exclusions. Every branch covers all vertex values;
invalid prefixes, source/predecessor camping and closed losing leaves are
separately justified from the actual game. The external producer is untrusted. -/
namespace Delivery.FiniteExclusion
open FiniteGame Extremal

abbrev Assignment (n : Nat) := Fin n → Fin n

def edgeOf {n} (a b : Assignment n) : Graph (Fin n) :=
  fun s t => t = a s ∨ t = b s
instance {n} (a b : Assignment n) : DecidableRel (edgeOf a b) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

instance {n} (a b : Assignment n) (s t : Fin n) : Decidable (Legal (edgeOf a b) s t) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Valid {n} (a b : Assignment n) : Prop :=
  (∀ i j, b i = b j → i = j) ∧ ∀ i, b i ≠ i ∧ b i ≠ a i

def Agrees {n} (p : List (Fin n)) (b : Assignment n) : Prop :=
  ∀ i : Fin n, ∀ h : i.val < p.length, b i = p[i.val]

def Blocked {n} (a b : Assignment n) : Prop :=
  ∃ s t, s ≠ t ∧ ¬ edgeOf a b s t ∧ ¬ Guaranteed (edgeOf a b) s t

def Excluded {n} (a : Assignment n) (p : List (Fin n)) : Prop :=
  ∀ b, Valid a b → Agrees p b → Blocked a b

def PrefixOK {n} (a : Assignment n) (p : List (Fin n)) : Prop :=
  ∀ i : Fin n, ∀ h : i.val < p.length,
    p[i.val] ≠ i ∧ p[i.val] ≠ a i ∧
    ∀ j : Fin n, ∀ hj : j.val < p.length, p[i.val] = p[j.val] → i = j
instance {n} (a : Assignment n) (p : List (Fin n)) : Decidable (PrefixOK a p) :=
  inferInstanceAs (Decidable (∀ i : Fin n, ∀ h : i.val < p.length, _))

theorem prefix_ok {n} {a b : Assignment n} {p : List (Fin n)}
    (valid : Valid a b) (agrees : Agrees p b) : PrefixOK a p := by
  intro i hi
  rw [← agrees i hi]
  refine ⟨(valid.2 i).1, (valid.2 i).2, ?_⟩
  intro j hj same
  apply valid.1 i j
  rw [agrees j hj]
  exact same

theorem invalid_excluded {n} (a : Assignment n) (p : List (Fin n))
    (bad : ¬ PrefixOK a p) : Excluded a p := by
  intro b valid agrees
  exact False.elim (bad (prefix_ok valid agrees))

theorem agrees_append {n} {p : List (Fin n)} {b : Assignment n}
    (h : p.length < n) (agrees : Agrees p b) :
    Agrees (p ++ [b ⟨p.length, h⟩]) b := by
  intro i hi
  by_cases before : i.val < p.length
  · simpa [List.getElem_append, before] using agrees i before
  · have same : i = ⟨p.length, h⟩ := by apply Fin.ext; simp only [Fin.val_mk]; simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simp

theorem branch_excluded {n} (a : Assignment n) (p : List (Fin n))
    (h : p.length < n) (children : ∀ v : Fin n, Excluded a (p ++ [v])) :
    Excluded a p := by
  intro b valid agrees
  exact children (b ⟨p.length,h⟩) b valid (agrees_append h agrees)

/-- A stationary cop covering the complete source row captures the first
non-waiting departure; waiting forever does not produce a finite win. -/
theorem source_camping_not_winning {V : Type} {E : Graph V} {s t c : V}
    (distinct : s ≠ t) (missing : ¬ E s t)
    (covers : ∀ z, E s z → Legal E c z) :
    ∀ k, ¬ Winning E t k s c := by
  intro k
  induction k generalizing c with
  | zero =>
      intro win
      cases win
      exact distinct rfl
  | succ k ih =>
      intro win
      cases win with
      | delivered => exact distinct rfl
      | finish _ legal => exact legal.elim distinct missing
      | @step _ _ _ z _ legal _ safe next =>
          rcases legal with same | edge
          · subst z
            exact ih covers (next c (legal_wait E c))
          · exact safe z (covers z edge) rfl

def lowerLegal {n} (a : Assignment n) (p : List (Fin n)) (c z : Fin n) : Prop :=
  c = z ∨ z = a c ∨ ∃ h : c.val < p.length, z = p[c.val]
instance {n} (a : Assignment n) (p : List (Fin n)) (c z : Fin n) :
    Decidable (lowerLegal a p c z) := inferInstanceAs (Decidable (_ ∨ _))

theorem lower_legal {n} {a b : Assignment n} {p : List (Fin n)}
    (agrees : Agrees p b) {c z : Fin n} (h : lowerLegal a p c z) :
    Legal (edgeOf a b) c z := by
  rcases h with same | first | ⟨h,second⟩
  · exact Or.inl same
  · exact Or.inr (Or.inl first)
  · exact Or.inr (Or.inr (second.trans (agrees c h).symm))

theorem source_excluded {n} (a : Assignment n) (p : List (Fin n))
    (s t c : Fin n) (hs : s.val < p.length)
    (check : s ≠ t ∧ c ≠ s ∧ t ≠ a s ∧ t ≠ p[s.val] ∧
      lowerLegal a p c (a s) ∧ lowerLegal a p c p[s.val]) : Excluded a p := by
  intro b _ agrees
  refine ⟨s,t,check.1,?_,?_⟩
  · intro edge
    exact edge.elim check.2.2.1 (fun hb => check.2.2.2.1 (hb.trans (agrees s hs)))
  · intro guaranteed
    obtain ⟨k,win⟩ := guaranteed c check.2.1
    apply source_camping_not_winning check.1 ?_ ?_ k win
    · intro edge
      exact edge.elim check.2.2.1 (fun hb => check.2.2.2.1 (hb.trans (agrees s hs)))
    · intro z edge
      rcases edge with rfl | rfl
      · exact lower_legal agrees check.2.2.2.2.1
      · rw [agrees s hs]
        exact lower_legal agrees check.2.2.2.2.2

theorem predecessor_excluded {n} (a : Assignment n) (p : List (Fin n))
    (s t c u : Fin n) (hu : u.val < p.length)
    (check : s ≠ t ∧ c ≠ s ∧ t ≠ a s ∧ s ≠ u ∧ p[u.val] = t ∧
      (∀ z, a z = t → lowerLegal a p c z) ∧ lowerLegal a p c u) : Excluded a p := by
  intro b valid agrees
  have missing : ¬ edgeOf a b s t := by
    intro edge
    rcases edge with first | second
    · exact check.2.2.1 first
    · apply check.2.2.2.1
      exact valid.1 s u (second.symm.trans ((agrees u hu).trans check.2.2.2.2.1).symm)
  refine ⟨s,t,check.1,missing,?_⟩
  apply ExclusionCertificates.camping_not_guaranteed check.1 missing check.2.1
  intro z edge
  rcases edge with first | second
  · exact lower_legal agrees (check.2.2.2.2.2.1 z first.symm)
  · have same : z = u := valid.1 z u (second.symm.trans ((agrees u hu).trans check.2.2.2.2.1).symm)
    subst z
    exact lower_legal agrees check.2.2.2.2.2.2

/-- A full-prefix leaf uses a closed losing region, never an external score. -/
theorem losing_excluded {n} (a : Assignment n) (p : List (Fin n))
    (full : p.length = n) (b : Assignment n)
    (same : ∀ i : Fin n, p[i.val]'(by omega) = b i)
    (s t c : Fin n) (cert : LosingRegion (edgeOf a b) t)
    (check : s ≠ t ∧ ¬ edgeOf a b s t ∧ c ≠ s ∧ cert.region s c) :
    Excluded a p := by
  intro b' _ agrees
  have eq : b' = b := by
    funext i
    exact (agrees i (by omega)).trans (same i)
  subst b'
  exact ⟨s,t,check.1,check.2.1,
    losingRegion_not_guaranteed cert check.2.2.2 check.2.2.1⟩

/-- A fixed finite table is accepted only after all losing-closure obligations
are reduced in the kernel. Collision states may be listed; receipt states may not. -/
def maskRegion {n} (mask : Nat) (r c : Fin n) : Prop :=
  mask.testBit (r.val * n + c.val) = true
instance {n} (mask : Nat) (r c : Fin n) : Decidable (maskRegion mask r c) :=
  inferInstanceAs (Decidable (_ = true))

def losingMask {n} (a b : Assignment n) (t : Fin n) (mask : Nat)
    (nonterminal : ∀ r c : Fin n, maskRegion mask r c → r ≠ t)
    (closed : ∀ r c : Fin n, maskRegion mask r c → r ≠ c →
      ∀ z, Legal (edgeOf a b) r z → z ≠ t ∧
        (z = c ∨ ∃ c', Legal (edgeOf a b) c c' ∧
          (z = c' ∨ maskRegion mask z c'))) : LosingRegion (edgeOf a b) t where
  region := maskRegion mask
  nonterminal := nonterminal
  closed := closed

theorem fin9_cases (P : Fin 9 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) : ∀ v, P v := by
  intro ⟨v,hv⟩
  have cases : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨
      v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

#print axioms branch_excluded
#print axioms source_excluded
#print axioms predecessor_excluded
#print axioms losing_excluded
end Delivery.FiniteExclusion
