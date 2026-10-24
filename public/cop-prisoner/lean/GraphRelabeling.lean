import DenseZero
import ExclusionCertificates

/-! Relabeling invariance of the actual finite game and extremal counts.
The vertex correspondence and its two inverse laws are explicit. This supplies
the semantic justification for complete enumerations up to graph isomorphism;
coverage of any particular list remains a separately proved obligation. -/
namespace Delivery.GraphRelabeling
open FiniteGame Extremal

variable {V W : Type}

structure Iso (E : Graph V) (F : Graph W) where
  toFun : V → W
  invFun : W → V
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  edge_iff : ∀ x y, E x y ↔ F (toFun x) (toFun y)

namespace Iso
variable {E : Graph V} {F : Graph W} (e : Iso E F)

theorem injective {x y : V} (same : e.toFun x = e.toFun y) : x = y := by
  have := congrArg e.invFun same
  simpa only [e.left_inv] using this

theorem ne_iff (x y : V) : e.toFun x ≠ e.toFun y ↔ x ≠ y :=
  ⟨fun h same => h (congrArg e.toFun same), fun h same => h (e.injective same)⟩

def symm : Iso F E where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  edge_iff := fun x y => by simpa only [e.right_inv] using (e.edge_iff (e.invFun x) (e.invFun y)).symm

theorem legal_iff (x y : V) : Legal E x y ↔ Legal F (e.toFun x) (e.toFun y) := by
  constructor
  · rintro (same | edge)
    · exact Or.inl (congrArg e.toFun same)
    · exact Or.inr ((e.edge_iff x y).mp edge)
  · rintro (same | edge)
    · exact Or.inl (e.injective same)
    · exact Or.inr ((e.edge_iff x y).mpr edge)

theorem winning {t r c : V} {k : Nat} (win : Winning E t k r c) :
    Winning F (e.toFun t) k (e.toFun r) (e.toFun c) := by
  induction win with
  | delivered => exact Winning.delivered
  | finish distinct moveLegal =>
      exact Winning.finish ((e.ne_iff _ _).mpr distinct) ((e.legal_iff _ _).mp moveLegal)
  | @step k r c z distinct moveLegal safeNow safeReply next ih =>
      apply Winning.step ((e.ne_iff _ _).mpr distinct)
        ((e.legal_iff _ _).mp moveLegal) ((e.ne_iff _ _).mpr safeNow)
      · intro c' reply same
        have reply' : Legal E c (e.invFun c') := by
          apply (e.legal_iff _ _).mpr
          simpa only [e.right_inv] using reply
        exact safeReply (e.invFun c') reply' (by
          have h := congrArg e.invFun same
          simpa only [e.left_inv] using h)
      · intro c' reply
        have reply' : Legal E c (e.invFun c') := by
          apply (e.legal_iff _ _).mpr
          simpa only [e.right_inv] using reply
        simpa only [e.right_inv] using ih (e.invFun c') reply'

theorem winning_iff (t r c : V) (k : Nat) :
    Winning E t k r c ↔ Winning F (e.toFun t) k (e.toFun r) (e.toFun c) := by
  constructor
  · exact e.winning
  · intro win
    simpa only [symm, e.left_inv] using e.symm.winning win

theorem guaranteed (s t : V) (win : Guaranteed E s t) :
    Guaranteed F (e.toFun s) (e.toFun t) := by
  intro c initial
  have initial' : e.invFun c ≠ s := by
    intro same
    apply initial
    simpa only [e.right_inv] using congrArg e.toFun same
  obtain ⟨k,hk⟩ := win (e.invFun c) initial'
  exact ⟨k,by simpa only [e.right_inv] using e.winning hk⟩

theorem guaranteed_iff (s t : V) :
    Guaranteed E s t ↔ Guaranteed F (e.toFun s) (e.toFun t) := by
  constructor
  · exact e.guaranteed s t
  · intro win
    simpa only [symm, e.left_inv] using e.symm.guaranteed _ _ win

theorem indirect_iff (s t : V) :
    Indirect E s t ↔ Indirect F (e.toFun s) (e.toFun t) := by
  simp only [Indirect, e.ne_iff, ← e.edge_iff, ← e.guaranteed_iff]

theorem loopless (e : Iso E F) (h : Loopless E) : Loopless F := by
  intro y edge
  apply h (e.invFun y)
  apply (e.edge_iff _ _).mpr
  simpa only [e.right_inv] using edge

end Iso

theorem allPairs_mem {n : Nat} (p : Fin n × Fin n) : p ∈ allPairs n := by
  simp [allPairs, List.mem_flatMap, List.mem_map]
  exact ⟨p.1,p.2,rfl⟩

variable {n m : Nat} {E : Graph (Fin n)} {F : Graph (Fin m)}

def pairMap (e : Iso E F) (p : Fin n × Fin n) : Fin m × Fin m :=
  (e.toFun p.1,e.toFun p.2)

theorem pairMap_injective (e : Iso E F) {p q : Fin n × Fin n}
    (same : pairMap e p = pairMap e q) : p = q := by
  apply Prod.ext
  · exact e.injective (congrArg Prod.fst same)
  · exact e.injective (congrArg Prod.snd same)

theorem allPairs_perm (e : Iso E F) :
    ((allPairs n).map (pairMap e)).Perm (allPairs m) := by
  apply (List.perm_ext_iff_of_nodup ?_ (DenseZero.allPairs_nodup m)).mpr
  · intro p
    constructor
    · intro _; exact allPairs_mem p
    · intro _
      apply List.mem_map.mpr
      refine ⟨(e.invFun p.1,e.invFun p.2),allPairs_mem _,?_⟩
      simp only [pairMap, e.right_inv]
  · apply List.pairwise_map.mpr
    exact (DenseZero.allPairs_nodup n).imp (fun h same => h (pairMap_injective e same))

theorem count_transport (e : Iso E F) (p : Fin n × Fin n → Bool)
    (q : Fin m × Fin m → Bool) (same : ∀ x, q (pairMap e x) = p x) :
    ((allPairs n).filter p).length = ((allPairs m).filter q).length := by
  have h := ((allPairs_perm e).filter q).length_eq
  simpa only [List.filter_map, List.length_map, Function.comp_def, same] using h

theorem arcCount_eq (e : Iso E F) : arcCount E = arcCount F := by
  classical
  apply count_transport e
  intro p
  exact decide_eq_decide.mpr (e.edge_iff p.1 p.2).symm

theorem missingCount_eq (e : Iso E F) : missingCount E = missingCount F := by
  classical
  apply count_transport e
  intro p
  simp only [pairMap, e.ne_iff, ← e.edge_iff]

theorem score_eq (e : Iso E F) : score E = score F := by
  classical
  apply count_transport e
  intro p
  exact decide_eq_decide.mpr (e.indirect_iff p.1 p.2).symm

/-- Enumerated representatives may be relabeled. Complete graph coverage is
still an explicit theorem obligation; checking listed leaves alone is not enough. -/
structure CoverUpToIso (n : Nat) (admissible : Graph (Fin n) → Prop) where
  Index : Type
  cases : List Index
  graph : Index → Graph (Fin n)
  complete : ∀ E, admissible E → ∃ i, i ∈ cases ∧ Nonempty (Iso (graph i) E)

theorem upper_from_cover {n bound : Nat} {admissible : Graph (Fin n) → Prop}
    (cover : CoverUpToIso n admissible)
    (leaves : ∀ i, i ∈ cover.cases → score (cover.graph i) ≤ bound) :
    ∀ E, admissible E → score E ≤ bound := by
  intro E allowed
  obtain ⟨i,listed,⟨iso⟩⟩ := cover.complete E allowed
  rw [← score_eq iso]
  exact leaves i listed

#print axioms Iso.winning_iff
#print axioms Iso.guaranteed_iff
#print axioms arcCount_eq
#print axioms score_eq
#print axioms upper_from_cover
end Delivery.GraphRelabeling
