import GraphRelabeling
import GuaranteedPrefix

/-! Recipient representatives for a symmetric lower/upper envelope. The
intermediate graph need not be symmetric: pull it back before applying its
representative certificate, then transport the actual game. -/
namespace Delivery.EnvelopeSymmetry
open FiniteGame GraphRelabeling RobustTwoMove

def pullback {n : Nat} (σ : Fin n → Fin n) (G : Graph (Fin n)) : Graph (Fin n) :=
  fun s t => G (σ s) (σ t)

def pullbackIso {n : Nat} {B : Graph (Fin n)} (σ : Iso B B) (G : Graph (Fin n)) :
    Iso (pullback σ.toFun G) G where
  toFun := σ.toFun
  invFun := σ.invFun
  left_inv := σ.left_inv
  right_inv := σ.right_inv
  edge_iff _ _ := Iff.rfl

theorem target_transport {n : Nat} {B U : Graph (Fin n)} (σ : Iso B B)
    (upperInvariant : ∀ s t, U s t ↔ U (σ.toFun s) (σ.toFun t)) (target : Fin n)
    (representative : ∀ G : Graph (Fin n), Subgraph B G → Subgraph G U →
      ∀ s, Guaranteed G s target) :
    ∀ G : Graph (Fin n), Subgraph B G → Subgraph G U →
      ∀ s, Guaranteed G s (σ.toFun target) := by
  intro G lower upper s
  have low : Subgraph B (pullback σ.toFun G) :=
    fun a b edge => lower _ _ ((σ.edge_iff a b).mp edge)
  have high : Subgraph (pullback σ.toFun G) U :=
    fun a b edge => (upperInvariant a b).mpr (upper _ _ edge)
  have actual := (pullbackIso σ G).guaranteed (σ.invFun s) target
    (representative (pullback σ.toFun G) low high (σ.invFun s))
  simpa only [pullbackIso,σ.right_inv] using actual

theorem delivers {n : Nat} (B U : Graph (Fin n)) (Representatives : Fin n → Prop)
    (checked : ∀ t, Representatives t → ∀ G : Graph (Fin n),
      Subgraph B G → Subgraph G U → ∀ s, Guaranteed G s t)
    (cover : ∀ t, ∃ r, Representatives r ∧ ∃ σ : Iso B B,
      (∀ s t, U s t ↔ U (σ.toFun s) (σ.toFun t)) ∧ σ.toFun r=t) :
    GuaranteedPrefix.Delivers B U := by
  intro G lower upper s t
  obtain ⟨r,member,σ,invariant,same⟩ := cover t
  rw [←same]
  exact target_transport σ invariant r (checked r member) G lower upper s

#print axioms target_transport
#print axioms delivers
end Delivery.EnvelopeSymmetry
