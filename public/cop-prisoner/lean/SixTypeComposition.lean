import SixTypeProjection
import FiniteHall

namespace Delivery.SixTypeComposition
open CyclicArithmetic SixTypeGraph SixTypeLocal SixTypeProjection LocalArena FiniteGame

def localVertex (u : Nat) (j : Fin 6) (lo : 2≤u) (hi : u≤10) : R :=
  ⟨6*(u-2)+j.val,by have := j.isLt; omega⟩

theorem local_col (u : Nat) (j : Fin 6) (lo : 2≤u) (hi : u≤10) :
    rcol (localVertex u j lo hi)=u := by
  unfold rcol localVertex
  have := j.isLt
  dsimp
  omega
theorem local_type (u : Nat) (j : Fin 6) (lo : 2≤u) (hi : u≤10) :
    rtype (localVertex u j lo hi)=j.val := by
  unfold rtype localVertex
  have := j.isLt
  dsimp
  omega

theorem represented {k u : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k)
    (s : Vertex H) (lo : 2≤u) (hi : u≤10) (col : s.val.1=shift base u) :
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

theorem transfer {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (cert : Certificates (crop H base)) (s c : Vertex H)
    (col : s.val.1=shift base 5) (safe : s≠c) :
    SafeReach (edge H) (fun z => z.val.1=shift base 6) 9 s c := by
  obtain ⟨r,hr,rc,rs⟩ := represented H base s (u:=5) (by decide) (by decide) col
  obtain ⟨D,checked,starts⟩ := cert.transfer
  have noncollision : ¬(arena (crop H base)).collision r (projectRaw base c.val) :=
    fun h => safe (rs.symm.trans ((collision_iff hk H base r c hr).mp h))
  obtain ⟨inside,bound⟩ := starts r (projectRaw base c.val) hr rc
    (project_present hk H base c) noncollision
  have win := safe_projection (simulation hk H base) checked
    (P:=fun z => z.val.1=shift base 6)
    (fun z goal => by
      change (embed H base z).val.1=shift base 6
      rw [embed_raw H base z goal.1]
      exact congrArg (shift base) goal.2) r c inside
  change SafeReach (edge H) (fun z => z.val.1=shift base 6)
    (D.rank r (projectRaw base c.val)) (embed H base r) c at win
  rw [rs] at win
  exact safe_mono win bound

theorem delivery {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (cert : Certificates (crop H base)) (s c t : Vertex H)
    (source : s.val.1=shift base 4) (target : t.val.1=shift base 6) (safe : s≠c) :
    Winning (edge H) t 27 s c := by
  obtain ⟨r,hr,rc,rs⟩ := represented H base s (u:=4) (by decide) (by decide) source
  have targetPresent : t.val.2.val≠4 ∨ 6∉crop H base := by
    have ht := t.property
    change t.val.2≠4 ∨ ¬H t.val.1 at ht
    rw [target] at ht
    have eqs : t.val.2=4 ↔ t.val.2.val=4 := by simp [Fin.ext_iff]
    simpa only [ne_eq,eqs,mem_crop H base (by decide : 6<13)] using ht
  obtain ⟨D,checked,starts⟩ := cert.delivery t.val.2 targetPresent
  have noncollision : ¬(arena (crop H base)).collision r (projectRaw base c.val) :=
    fun h => safe (rs.symm.trans ((collision_iff hk H base r c hr).mp h))
  obtain ⟨inside,bound⟩ := starts r (projectRaw base c.val) hr rc
    (project_present hk H base c) noncollision
  have win := delivery_projection (simulation hk H base) checked
    (t:=t) (fun z goal => by
      apply Subtype.ext
      change (embed H base z).val=t.val
      rw [embed_raw H base z goal.1]
      apply Prod.ext
      · exact (congrArg (shift base) goal.2.1).trans target.symm
      · exact Fin.ext goal.2.2) r c inside
  change Winning (edge H) t (D.rank r (projectRaw base c.val)) (embed H base r) c at win
  rw [rs] at win
  exact winning_mono win bound

theorem back_shift {k a : Nat} (i : Fin k) (small : a≤k) :
    shift (shift i (k-a)) a=i := by
  rw [shift_add,show k-a+a=k by omega,shift_period]

theorem one_step {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (cert : ∀ base, Certificates (crop H base)) (s c : Vertex H) (safe : s≠c) :
    SafeReach (edge H) (fun z => z.val.1=shift s.val.1 1) 9 s c := by
  let base := shift s.val.1 (k-5)
  have source : shift base 5=s.val.1 := back_shift s.val.1 (by omega)
  have goal : shift base 6=shift s.val.1 1 := by
    calc
      shift base 6=shift (shift base 5) 1 := (shift_add base 5 1).symm
      _=shift s.val.1 1 := by rw [source]
  simpa only [goal] using transfer hk H base (cert base) s c source.symm safe

theorem shift_reaches {k : Nat} (s t : Fin k) : ∃ j : Fin k, shift s j.val=t := by
  apply FiniteHall.injective_surjective (fun j : Fin k => shift s j.val)
  intro a b same
  have eqs := (shift_eq_iff s a.val b.val).mp same
  rw [Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt b.isLt] at eqs
  exact Fin.ext eqs

theorem winning {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (cert : ∀ base, Certificates (crop H base)) (s c t : Vertex H) (safe : s≠c) :
    Winning (edge H) t (9*k+18) s c := by
  let base := shift t.val.1 (k-6)
  have target : t.val.1=shift base 6 := (back_shift t.val.1 (by omega)).symm
  obtain ⟨j,reaches⟩ := shift_reaches s.val.1 (shift base 4)
  let P (i : Nat) (z : Vertex H) := z.val.1=shift s.val.1 i
  have stages : ∀ i r d, P i r → r≠d → SafeReach (edge H) (P (i+1)) 9 r d := by
    intro i r d loc distinct
    have next := one_step hk H cert r d distinct
    simpa only [P,loc,shift_add] using next
  have finish : ∀ r d, P j.val r → r≠d → Winning (edge H) t 27 r d := by
    intro r d loc distinct
    exact delivery hk H base (cert base) r d t (loc.trans reaches) target distinct
  have result := transfer_then_delivery P 9 27 t stages j.val finish
    (r:=s) (c:=c) (shift_zero s.val.1).symm safe
  apply winning_mono result
  have := j.isLt
  omega

theorem guaranteed {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (cert : ∀ base, Certificates (crop H base)) (s t : Vertex H) : Guaranteed (edge H) s t := by
  intro c safe
  exact ⟨9*k+18,winning hk H cert s c t (Ne.symm safe)⟩

theorem canonical_guaranteed
    (cert : ∀ p, p∈SparseCropCoverage.catalog → Certificates p)
    {k r : Nat} (hk : 15≤k) (hr : r≤5) (s t : Vertex (holes (k:=k) r)) :
    Guaranteed (edge (holes r)) s t := by
  apply guaranteed hk (holes r) _ s t
  intro base
  rw [canonical_crop]
  exact cert _ (SparseCropCoverage.coverage k r base.val hk hr base.isLt)

#print axioms canonical_guaranteed
end Delivery.SixTypeComposition
