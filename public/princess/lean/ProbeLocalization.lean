import BeliefSemantics

/-! Exact localization of inspections in a finite block.
Keep only probes from which a freely moving target could reach an unwanted
endpoint. The resulting final belief is exactly unchanged. This semantic
statement holds on arbitrary directed graphs. Its geometric application to
a bounded strip around a pyramid frontier is an ordinary theorem.
-/
namespace Princess.ProbeLocalization

def reaches {V : Type} (adj : V → V → Prop) (target : Region V) :
    Nat → Region V
  | 0 => target
  | k+1 => fun v => ∃ w, adj v w ∧ reaches adj target k w

def cone {V : Type} (adj : V → V → Prop) (target : Region V)
    (horizon t : Nat) : Region V := reaches adj target (horizon-t)

def localized {V : Type} (adj : V → V → Prop) (target : Region V)
    (probes : Nat → Region V) (horizon : Nat) : Nat → Region V :=
  fun t v => probes t v ∧ cone adj target horizon t v

theorem restore_on_cone {V : Type} (adj : V → V → Prop)
    (initial target : Region V) (probes : Nat → Region V)
    (horizon t : Nat) (ht : t ≤ horizon) (v : V)
    (hp : possible adj initial (localized adj target probes horizon) t v)
    (hc : cone adj target horizon t v) : possible adj initial probes t v := by
  induction t generalizing v with
  | zero => exact hp
  | succ t ih =>
    obtain ⟨u,⟨hu,hm⟩,huv⟩ := hp
    have hucone : cone adj target horizon t u := by
      unfold cone at *
      have he : horizon-t = (horizon-(t+1))+1 := by omega
      rw [he]
      exact ⟨v,huv,hc⟩
    have huold := ih (by omega) u hu hucone
    have hmiss : ¬ probes t u := by
      intro hprobe
      exact hm ⟨hprobe,hucone⟩
    exact ⟨u,⟨huold,hmiss⟩,huv⟩

def noProbes {V : Type} : Nat → Region V := fun _ _ => False

def danger {V : Type} (adj : V → V → Prop) (initial : Region V)
    (probes : Nat → Region V) (horizon : Nat) : Region V :=
  fun v => possible adj initial noProbes horizon v ∧
    ¬ possible adj initial probes horizon v

/-- The canonical backward cone is sufficient: removing all inspections
outside it preserves exactly the final possible-position set. -/
theorem exact_endpoint {V : Type} (adj : V → V → Prop)
    (initial : Region V) (probes : Nat → Region V) (horizon : Nat) (v : V) :
    possible adj initial
      (localized adj (danger adj initial probes horizon) probes horizon) horizon v ↔
      possible adj initial probes horizon v := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hfree : possible adj initial noProbes horizon v :=
      possible_mono_probes adj initial noProbes
        (localized adj (danger adj initial probes horizon) probes horizon)
        (fun _ _ hf => False.elim hf) horizon v h
    have hc : cone adj (danger adj initial probes horizon) horizon horizon v := by
      simpa only [cone,Nat.sub_self,reaches,danger] using (And.intro hfree hn)
    exact hn (restore_on_cone adj initial (danger adj initial probes horizon)
      probes horizon horizon (Nat.le_refl _) v h hc)
  · intro h
    exact possible_mono_probes adj initial
      (localized adj (danger adj initial probes horizon) probes horizon) probes
      (fun _ _ hp => hp.1) horizon v h

/-- A larger retained region is also sound. This lets geometry replace
the exact backward cone by a convenient spatial interval. -/
theorem exact_endpoint_in_region {V : Type} (adj : V → V → Prop)
    (initial : Region V) (probes : Nat → Region V) (horizon : Nat)
    (keep : Nat → Region V)
    (hkeep : ∀ t v, cone adj (danger adj initial probes horizon) horizon t v → keep t v)
    (v : V) :
    possible adj initial (fun t u => probes t u ∧ keep t u) horizon v ↔
      possible adj initial probes horizon v := by
  constructor
  · intro h
    have hloc := possible_mono_probes adj initial
      (localized adj (danger adj initial probes horizon) probes horizon)
      (fun t u => probes t u ∧ keep t u)
      (fun t u hp => ⟨hp.1,hkeep t u hp.2⟩) horizon v h
    exact (exact_endpoint adj initial probes horizon v).mp hloc
  · intro h
    exact possible_mono_probes adj initial (fun t u => probes t u ∧ keep t u)
      probes (fun _ _ hp => hp.1) horizon v h

end Princess.ProbeLocalization
#print axioms Princess.ProbeLocalization.exact_endpoint
#print axioms Princess.ProbeLocalization.exact_endpoint_in_region
