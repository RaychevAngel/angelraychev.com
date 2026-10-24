import LowBandProjection
import SixTypeComposition

namespace Delivery.LowBandComposition
open CyclicArithmetic SixTypeGraph LowBandLocal LowBandProjection LocalArena FiniteGame

def localVertex (u : Nat) (j : Fin 6) (lo : 3≤u) (hi : u≤13) : R :=
  ⟨6*(u-3)+j.val,by have := j.isLt; omega⟩

theorem local_col (u : Nat) (j : Fin 6) (lo : 3≤u) (hi : u≤13) :
    rcol (localVertex u j lo hi)=u := by
  unfold rcol localVertex
  have := j.isLt
  dsimp
  omega
theorem local_type (u : Nat) (j : Fin 6) (lo : 3≤u) (hi : u≤13) :
    rtype (localVertex u j lo hi)=j.val := by
  unfold rtype localVertex
  have := j.isLt
  dsimp
  omega

theorem represented {k u : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k)
    (s : Vertex H) (lo : 3≤u) (hi : u≤13) (col : s.val.1=shift base u) :
    ∃ r : R, presentR (crop H base) r ∧ rcol r=u ∧ embed H base r=s := by
  let r := localVertex u s.val.2 lo hi
  have rc : rcol r=u := local_col u s.val.2 lo hi
  have rt : rtype r=s.val.2.val := local_type u s.val.2 lo hi
  have raw : liftRaw base r=s.val := by
    apply Prod.ext
    · exact (congrArg (shift base) rc).trans col.symm
    · exact Fin.ext rt
  have hr := (present_lift H base r).mp (raw ▸ s.property)
  refine ⟨r,hr,rc,?_⟩
  apply Subtype.ext
  exact (embed_raw H base r hr).trans raw

theorem transfer {k : Nat} (hk : 20≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (G : Graph (Vertex H))
    (lower : RobustTwoMove.Subgraph (edge H) G)
    (upper : RobustTwoMove.Subgraph G (LowBandGraph.upper H))
    (cert : Certificates (crop H base)) (s c : Vertex H)
    (col : s.val.1=shift base 7) (safe : s≠c) :
    SafeReach G (fun z => z.val.1=shift base 8) 9 s c := by
  obtain ⟨r,hr,rc,rs⟩ := represented H base s (u:=7) (by decide) (by decide) col
  obtain ⟨D,checked,starts⟩ := cert.transfer
  have noncollision : ¬(arena (crop H base)).collision r (projectRaw base c.val) :=
    fun h => safe (rs.symm.trans ((collision_iff hk H base r c hr).mp h))
  obtain ⟨inside,bound⟩ := starts r (projectRaw base c.val) hr rc
    (project_present hk H base c) noncollision
  have win := safe_projection (simulation hk H base G lower upper) checked
    (P:=fun z => z.val.1=shift base 8)
    (fun z goal => by
      change (embed H base z).val.1=shift base 8
      rw [embed_raw H base z goal.1]
      exact congrArg (shift base) goal.2) r c inside
  change SafeReach G (fun z => z.val.1=shift base 8)
    (D.rank r (projectRaw base c.val)) (embed H base r) c at win
  rw [rs] at win
  exact safe_mono win bound

theorem delivery {k u : Nat} (hk : 20≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (G : Graph (Vertex H))
    (lower : RobustTwoMove.Subgraph (edge H) G)
    (upper : RobustTwoMove.Subgraph G (LowBandGraph.upper H))
    (cert : Certificates (crop H base)) (s c t : Vertex H)
    (entry : u=5 ∨ u=6) (source : s.val.1=shift base u)
    (target : t.val.1=shift base 8) (safe : s≠c) :
    Winning G t (if u=5 then 39 else 38) s c := by
  obtain ⟨r,hr,rc,rs⟩ := represented H base s (u:=u) (by omega) (by omega) source
  have targetPresent : t.val.2.val≠4 ∨ 8∉crop H base := by
    have ht := t.property
    change t.val.2≠4 ∨ ¬H t.val.1 at ht
    rw [target] at ht
    have eqs : t.val.2=4 ↔ t.val.2.val=4 := by simp [Fin.ext_iff]
    simpa only [ne_eq,eqs,mem_crop H base (by decide : 8<17)] using ht
  obtain ⟨D,checked,starts⟩ := cert.delivery t.val.2 targetPresent
  have noncollision : ¬(arena (crop H base)).collision r (projectRaw base c.val) :=
    fun h => safe (rs.symm.trans ((collision_iff hk H base r c hr).mp h))
  obtain ⟨inside,bound⟩ := starts r (projectRaw base c.val) hr
    (by simpa only [rc] using entry) (project_present hk H base c) noncollision
  have win := delivery_projection (simulation hk H base G lower upper) checked
    (t:=t) (fun z goal => by
      apply Subtype.ext
      change (embed H base z).val=t.val
      rw [embed_raw H base z goal.1]
      apply Prod.ext
      · exact (congrArg (shift base) goal.2.1).trans target.symm
      · exact Fin.ext goal.2.2) r c inside
  change Winning G t (D.rank r (projectRaw base c.val)) (embed H base r) c at win
  rw [rs] at win
  rw [rc] at bound
  exact winning_mono win bound

theorem one_step {k : Nat} (hk : 20≤k) (H : Fin k → Prop) [DecidablePred H]
    (G : Graph (Vertex H))
    (lower : RobustTwoMove.Subgraph (edge H) G)
    (upper : RobustTwoMove.Subgraph G (LowBandGraph.upper H))
    (cert : ∀ base, Certificates (crop H base)) (s c : Vertex H) (safe : s≠c) :
    SafeReach G (fun z => z.val.1=shift s.val.1 1) 9 s c := by
  let base := shift s.val.1 (k-7)
  have source : shift base 7=s.val.1 := SixTypeComposition.back_shift s.val.1 (by omega)
  have goal : shift base 8=shift s.val.1 1 := by
    calc
      shift base 8=shift (shift base 7) 1 := (shift_add base 7 1).symm
      _=shift s.val.1 1 := by rw [source]
  simpa only [goal] using transfer hk H base G lower upper (cert base) s c source.symm safe

/-- A pair of consecutive delivery-entry columns is met within k-2 forward
transfers. If the first entry is k-1 steps away, the source is already the second. -/
theorem adjacent_entries {k : Nat} (hk : 20≤k) (s base : Fin k) :
    ∃ j : Nat, j≤k-2 ∧ (shift s j=shift base 5 ∨ shift s j=shift base 6) := by
  obtain ⟨j,reaches⟩ := SixTypeComposition.shift_reaches s (shift base 5)
  by_cases short : j.val≤k-2
  · exact ⟨j.val,short,Or.inl reaches⟩
  · have last : j.val+1=k := by have := j.isLt; omega
    have next := congrArg (fun i => shift i 1) reaches
    rw [shift_add,last,shift_period,shift_add] at next
    refine ⟨0,by omega,Or.inr ?_⟩
    simpa only [shift_zero] using next

theorem winning {k : Nat} (hk : 20≤k) (H : Fin k → Prop) [DecidablePred H]
    (G : Graph (Vertex H))
    (lower : RobustTwoMove.Subgraph (edge H) G)
    (upper : RobustTwoMove.Subgraph G (LowBandGraph.upper H))
    (cert : ∀ base, Certificates (crop H base)) (s c t : Vertex H) (safe : s≠c) :
    Winning G t (9*k+21) s c := by
  let base := shift t.val.1 (k-8)
  have target : t.val.1=shift base 8 := (SixTypeComposition.back_shift t.val.1 (by omega)).symm
  obtain ⟨j,short,reaches⟩ := adjacent_entries hk s.val.1 base
  let P (i : Nat) (z : Vertex H) := z.val.1=shift s.val.1 i
  have stages : ∀ i r d, P i r → r≠d → SafeReach G (P (i+1)) 9 r d := by
    intro i r d loc distinct
    have next := one_step hk H G lower upper cert r d distinct
    simpa only [P,loc,shift_add] using next
  have finish : ∀ r d, P j r → r≠d → Winning G t 39 r d := by
    intro r d loc distinct
    rcases reaches with first | second
    · exact delivery hk H base G lower upper (cert base) r d t
        (Or.inl rfl) (loc.trans first) target distinct
    · have result := delivery hk H base G lower upper (cert base) r d t
        (Or.inr rfl) (loc.trans second) target distinct
      exact winning_mono result (by decide)
  have result := transfer_then_delivery P 9 39 t stages j finish
    (r:=s) (c:=c) (shift_zero s.val.1).symm safe
  exact winning_mono result (by omega)

theorem guaranteed {k : Nat} (hk : 20≤k) (H : Fin k → Prop) [DecidablePred H]
    (G : Graph (Vertex H))
    (lower : RobustTwoMove.Subgraph (edge H) G)
    (upper : RobustTwoMove.Subgraph G (LowBandGraph.upper H))
    (cert : ∀ base, Certificates (crop H base)) (s t : Vertex H) : Guaranteed G s t := by
  intro c safe
  exact ⟨9*k+21,winning hk H G lower upper cert s c t (Ne.symm safe)⟩

theorem canonical_guaranteed
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → Certificates p)
    {k r : Nat} (hk : 20≤k) (hr : r≤5)
    (G : Graph (Vertex (holes (k:=k) r)))
    (lower : RobustTwoMove.Subgraph (edge (holes r)) G)
    (upper : RobustTwoMove.Subgraph G (LowBandGraph.upper (holes r)))
    (s t : Vertex (holes (k:=k) r)) : Guaranteed G s t := by
  apply guaranteed hk (holes r) G lower upper _ s t
  intro base
  rw [canonical_crop]
  exact cert _ (LowBandCropCoverage.coverage k r base.val hk hr base.isLt)

#print axioms delivery
#print axioms winning
#print axioms canonical_guaranteed
end Delivery.LowBandComposition

