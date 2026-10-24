import OddEndpointLocal

/-! Every cyclic window selects either its unique supported patch lift or
the ordinary arena. The exact outgoing-row diagram includes smoothing and
the deleted arrow, and is uniform across all six residues. -/
namespace Delivery.OddEndpointWindow
open OddEndpointGraph OddEndpointLocal OddEndpointLifting CyclicSigned

def Anchor (k : Nat) (r : Case) (origin h : Int) : Prop :=
  -(OddEndpointParameters.radius r : Int)-OddEndpointStrip.supportHigh r≤h ∧
  h≤(OddEndpointParameters.radius r : Int)-OddEndpointStrip.supportLow r ∧
  (origin+h)%(k : Int)=0

def Coherent (k : Nat) (r : Case) (origin : Int) : Option Int → Prop
  | none => ¬∃ h, Anchor k r origin h
  | some h => Anchor k r origin h

noncomputable def anchor (k : Nat) (r : Case) (origin : Int) : Option Int := by
  classical
  exact if h : ∃ a, Anchor k r origin a then some (Classical.choose h) else none

theorem anchor_coherent (k : Nat) (r : Case) (origin : Int) :
    Coherent k r origin (anchor k r origin) := by
  classical
  unfold anchor
  split
  · rename_i h
    exact Classical.choose_spec h
  · assumption

theorem anchor_unique {k : Nat} (hk : 15≤k) (r : Case) (origin h j : Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (first : Anchor k r origin h) (second : Anchor k r origin j) : h=j := by
  have width : (OddEndpointParameters.span r : Int)=
      OddEndpointStrip.supportHigh r-OddEndpointStrip.supportLow r := by
    have finite : ∀ r, (OddEndpointParameters.span r : Int)=
        OddEndpointStrip.supportHigh r-OddEndpointStrip.supportLow r := by decide +kernel
    exact finite r
  have fh := first.1
  have ft := first.2.1
  have sh := second.1
  have st := second.2.1
  have equal := CyclicSigned.injective_of_gap (by omega : 0<k)
    (x:=origin+h) (y:=origin+j) (by omega) (by omega)
    ((wrap_eq_iff (by omega : 0<k) _ _).mpr (first.2.2.trans second.2.2.symm))
  omega

theorem anchor_covered {k : Nat} (r : Case) (origin h : Int) (valid : Anchor k r origin h) :
    -(OddEndpointParameters.anchorLimit r : Int)≤h ∧
      h≤(OddEndpointParameters.anchorLimit r : Int) := by
  have finite : ∀ r,
      -(OddEndpointParameters.anchorLimit r : Int)≤
        -(OddEndpointParameters.radius r : Int)-OddEndpointStrip.supportHigh r ∧
      (OddEndpointParameters.radius r : Int)-OddEndpointStrip.supportLow r≤
        (OddEndpointParameters.anchorLimit r : Int) := by decide +kernel
  have bounds := finite r
  have := valid.1
  have := valid.2.1
  omega

def lift {k : Nat} (hk : 15≤k) (origin : Int) (v : OddEndpointStrip.Vertex) : Raw k :=
  project hk (translate v origin)

theorem lift_some {k : Nat} (hk : 15≤k) (r : Case) (origin h : Int)
    (coherent : Anchor k r origin h) (v : OddEndpointStrip.Vertex) :
    lift hk origin v=project hk (translate v (-h)) := by
  apply Prod.ext
  · apply (wrap_eq_iff (by omega : 0<k) _ _).mpr
    change (v.1+origin)%(k : Int)=(v.1 + -h)%(k : Int)
    have split : v.1+origin=(v.1 + -h)+(origin+h) := by omega
    rw [split,Int.add_emod,coherent.2.2,Int.add_zero,Int.emod_emod]
  · rfl

theorem raw_translate (r : Case) (b : Bool) (v : OddEndpointStrip.Vertex) (h : Int) :
    OddEndpointStrip.raw r b (translate v h)=translate (OddEndpointStrip.raw r b v) h := by
  apply Prod.ext
  · dsimp [OddEndpointStrip.raw,translate]; omega
  · rfl

theorem no_anchor_outside {k : Nat} (hk : 15≤k) (r : Case) (origin : Int)
    (coherent : Coherent k r origin none) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) :
    ¬InSupport r (view (lift hk origin v)) := by
  intro supported
  let w := view (lift hk origin v)
  have equal : project hk (translate v origin)=project hk w :=
    (project_view hk (lift hk origin v)).symm
  have cols := (wrap_eq_iff (by omega : 0<k) _ _).mp (congrArg Prod.fst equal)
  change (v.1+origin)%(k : Int)=w.1%(k : Int) at cols
  have zero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp cols
  apply coherent
  refine ⟨v.1-w.1,?_,?_,?_⟩
  · unfold InSupport at supported
    unfold inWindow at inside
    change OddEndpointStrip.supportLow r≤w.1 ∧ w.1≤OddEndpointStrip.supportHigh r at supported
    omega
  · unfold InSupport at supported
    unfold inWindow at inside
    change OddEndpointStrip.supportLow r≤w.1 ∧ w.1≤OddEndpointStrip.supportHigh r at supported
    omega
  · have rearrange : origin+(v.1-w.1)=v.1+origin-w.1 := by omega
    rw [rearrange]
    exact zero

theorem some_good {k : Nat} (r : Case) (origin h : Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Anchor k r origin h) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) :
    GoodLift k r (translate v (-h)) := by
  have result := translated_good r (OddEndpointParameters.radius r) h v.1 small
    coherent.1 coherent.2.1 inside.1 inside.2 v.2
  simpa only [translate,Int.sub_eq_add_neg] using result

theorem present_lift {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) :
    Present hk r (lift hk origin v) ↔ present r a v := by
  cases a with
  | some h =>
    rw [lift_some hk r origin h coherent v]
    exact present_project_iff hk r _ (some_good r origin h small coherent v inside)
  | none =>
    have away := no_anchor_outside hk r origin coherent v inside
    have outside : (view (lift hk origin v)).1<OddEndpointStrip.supportLow r ∨
        OddEndpointStrip.supportHigh r<(view (lift hk origin v)).1 := by
      unfold InSupport at away
      omega
    have available := (OddEndpointStrip.outside_support r _ outside).1
    exact ⟨fun _ => trivial,fun _ => (present_iff hk r _).mpr available⟩

/-- Exact agreement of the cyclic and local smoothed successors. The local
head may leave the cop window; it has not yet been collapsed to outside. -/
theorem next_lift {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) (b : Bool) :
    rawMove hk r b (lift hk origin v)=lift hk origin (next r a b v) := by
  cases a with
  | some h =>
    rw [lift_some hk r origin h coherent v,
      smooth_project hk r b _ (some_good r origin h small coherent v inside),
      lift_some hk r origin h coherent]
    congr 1
    apply Prod.ext
    · dsimp [next,translate]; omega
    · rfl
  | none =>
    have away := no_anchor_outside hk r origin coherent v inside
    have outside : (view (lift hk origin v)).1<OddEndpointStrip.supportLow r ∨
        OddEndpointStrip.supportHigh r<(view (lift hk origin v)).1 := by
      unfold InSupport at away
      omega
    rw [rawMove,(OddEndpointStrip.outside_support r _ outside).2.2 b]
    have result := raw_project_congr hk r b (project_view hk (lift hk origin v))
    change project hk (OddEndpointStrip.raw r b (view (lift hk origin v)))=
      project hk (OddEndpointStrip.raw r b (translate v origin)) at result
    rw [raw_translate] at result
    exact result

theorem source_lift {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) :
    lift hk origin v≠(lowSource hk r).val ↔ eligible r a v := by
  cases a with
  | some h =>
    rw [lift_some hk r origin h coherent v]
    exact not_congr (source_project_iff hk r _ (some_good r origin h small coherent v inside))
  | none =>
    refine ⟨fun _ => trivial,fun _ same => ?_⟩
    have away := no_anchor_outside hk r origin coherent v inside
    apply away
    have bounds := OddEndpointStrip.source_bounds r
    rw [same]
    change InSupport r (view (project hk (OddEndpointStrip.source r)))
    rw [view_project hk _ (by omega) (by omega)]
    exact source_support r

theorem permitted_lift {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) (b : Bool) :
    (lift hk origin v≠(lowSource hk r).val ∨ b≠OddEndpointStrip.deletedChoice r) ↔
      permitted r a v b := by
  rw [source_lift hk r origin a small coherent v inside]
  cases a <;> simp only [eligible,permitted,OddEndpointStrip.permitted,true_or]

#print axioms next_lift
#print axioms permitted_lift
end Delivery.OddEndpointWindow
