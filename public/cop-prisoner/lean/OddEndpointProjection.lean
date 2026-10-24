import OddEndpointWindow

namespace Delivery.OddEndpointProjection
open OddEndpointGraph OddEndpointLocal OddEndpointWindow OddEndpointLifting
open CyclicSigned CyclicArithmetic LocalArena

theorem pack_val (r : Case) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) :
    (pack r v).val=6*(v.1+7).toNat+v.2.val := by simp [pack,inside]

theorem pack_not_outside (r : Case) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) : pack r v≠outside := by
  have radius := radius_bounds r
  have typ := v.2.isLt
  intro same
  have values := congrArg Fin.val same
  rw [pack_val r v inside] at values
  change _=90 at values
  unfold inWindow at inside
  omega

theorem cvertex_pack (r : Case) (v : OddEndpointStrip.Vertex)
    (inside : inWindow (OddEndpointParameters.radius r) v) : cvertex (pack r v)=v := by
  have radius := radius_bounds r
  have typ := v.2.isLt
  apply Prod.ext
  · simp only [cvertex,pack_val r v inside]
    unfold inWindow at inside
    omega
  · apply Fin.ext
    simp only [cvertex,pack_val r v inside]
    omega

theorem pack_cvertex (r : Case) (c : C) (actual : c≠outside)
    (inside : inWindow (OddEndpointParameters.radius r) (cvertex c)) : pack r (cvertex c)=c := by
  have large := c.isLt
  have notOutside : c.val≠90 := fun h => actual (Fin.ext h)
  apply Fin.ext
  rw [pack_val r _ inside]
  dsimp [cvertex]
  omega

theorem rvertex_injective {x y : R} (same : rvertex x=rvertex y) : x=y := by
  have col := congrArg Prod.fst same
  have typ := congrArg (fun v : OddEndpointStrip.Vertex => v.2.val) same
  dsimp [rvertex] at col typ
  apply Fin.ext
  omega

theorem messenger_inside (r : Case) (a : Option Int) (x : R) (present : presentR r a x) :
    inWindow (OddEndpointParameters.radius r) (rvertex x) := by
  have radius := radius_bounds r
  unfold presentR inWindow at present
  unfold inWindow
  omega

theorem lift_injective {k : Nat} (hk : 15≤k) (origin : Int)
    {v w : OddEndpointStrip.Vertex}
    (right : v.1<w.1+(k : Int)) (left : w.1<v.1+(k : Int))
    (same : lift hk origin v=lift hk origin w) : v=w := by
  have equal := project_injective_of_gap hk (v:=translate v origin) (w:=translate w origin)
    (by dsimp [translate]; omega) (by dsimp [translate]; omega) same
  apply Prod.ext
  · have cols := congrArg Prod.fst equal
    dsimp [translate] at cols
    omega
  · simpa only [translate] using congrArg Prod.snd equal

noncomputable def projectRaw {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (v : Raw k) : C := by
  classical
  exact if h : ∃ c : C, c≠outside ∧ inWindow (OddEndpointParameters.radius r) (cvertex c) ∧
      lift hk origin (cvertex c)=v then Classical.choose h else outside

theorem project_cases {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (v : Raw k) :
    projectRaw hk r origin v=outside ∨
      projectRaw hk r origin v≠outside ∧
      inWindow (OddEndpointParameters.radius r) (cvertex (projectRaw hk r origin v)) ∧
      lift hk origin (cvertex (projectRaw hk r origin v))=v := by
  classical
  unfold projectRaw
  split
  · rename_i h
    exact Or.inr (Classical.choose_spec h)
  · exact Or.inl rfl

/-- Heads up to J columns beyond either boundary cannot wrap back into the
window. Thus collapsing them to the outside cop state is exact. -/
theorem project_lift {k : Nat} (hk : 15≤k) (r : Case) (origin : Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
    (v : OddEndpointStrip.Vertex)
    (low : -(OddEndpointParameters.radius r : Int)-(OddEndpointParameters.jump r : Int)≤v.1)
    (high : v.1≤(OddEndpointParameters.radius r : Int)+(OddEndpointParameters.jump r : Int)) :
    projectRaw hk r origin (lift hk origin v)=pack r v := by
  classical
  unfold projectRaw
  split
  · rename_i h
    let c : C := Classical.choose h
    have hit : c≠outside ∧ inWindow (OddEndpointParameters.radius r) (cvertex c) ∧
        lift hk origin (cvertex c)=lift hk origin v := Classical.choose_spec h
    have inside : -(OddEndpointParameters.radius r : Int)≤(cvertex c).1 ∧
        (cvertex c).1≤(OddEndpointParameters.radius r : Int) := hit.2.1
    have equal := lift_injective hk origin (v:=cvertex c) (w:=v)
      (by omega) (by omega) hit.2.2
    have packed := pack_cvertex r c hit.1 hit.2.1
    simpa only [equal] using packed.symm
  · rename_i absent
    have beyond : ¬inWindow (OddEndpointParameters.radius r) v := by
      intro inside
      apply absent
      refine ⟨pack r v,pack_not_outside r v inside,?_,?_⟩
      · simpa only [cvertex_pack r v inside] using inside
      · rw [cvertex_pack r v inside]
    simp only [pack,dif_neg beyond]

theorem project_present {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (v : Vertex hk r) :
    presentC r a (projectRaw hk r origin v.val) := by
  rcases project_cases hk r origin v.val with outside|⟨actual,inside,same⟩
  · exact Or.inl outside
  · refine Or.inr ⟨inside,?_⟩
    have available : Present hk r (lift hk origin (cvertex (projectRaw hk r origin v.val))) := by
      rw [same]
      exact v.property
    exact (present_lift hk r origin a small coherent _ inside).mp available

def embed {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (x : R) : Vertex hk r :=
  if h : presentR r a x then
    ⟨lift hk origin (rvertex x),(present_lift hk r origin a small coherent _
      (messenger_inside r a x h)).mpr h.2⟩
  else lowSource hk r

theorem embed_raw {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (x : R) (present : presentR r a x) :
    (embed hk r origin a small coherent x).val=lift hk origin (rvertex x) := by
  simp [embed,present]

theorem project_embed {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
    (coherent : Coherent k r origin a) (x : R) (present : presentR r a x) :
    projectRaw hk r origin (embed hk r origin a small coherent x).val=pack r (rvertex x) := by
  have inside := messenger_inside r a x present
  rw [embed_raw hk r origin a small coherent x present]
  exact project_lift hk r origin short _ (by unfold inWindow at inside; omega)
    (by unfold inWindow at inside; omega)

theorem collision_iff {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
    (coherent : Coherent k r origin a) (x : R) (c : Vertex hk r) (present : presentR r a x) :
    (arena r a).collision x (projectRaw hk r origin c.val) ↔
      embed hk r origin a small coherent x=c := by
  change (¬presentR r a x ∨ pack r (rvertex x)=projectRaw hk r origin c.val) ↔ _
  simp only [present,not_true_eq_false,false_or]
  constructor
  · intro same
    have inside := messenger_inside r a x present
    have notOutside := pack_not_outside r (rvertex x) inside
    rcases project_cases hk r origin c.val with outside|⟨_,_,equal⟩
    · exact False.elim (notOutside (same.trans outside))
    · rw [←same,cvertex_pack r _ inside] at equal
      apply Subtype.ext
      rw [embed_raw hk r origin a small coherent x present]
      exact equal
  · intro same
    rw [←same,project_embed hk r origin a small short coherent x present]

theorem messenger_sound {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (coherent : Coherent k r origin a) (x y : R) (legal : messenger r a x y) :
    Legal (edge hk r) (embed hk r origin a small coherent x) (embed hk r origin a small coherent y) := by
  obtain ⟨px,py,wait|⟨b,allowed,same⟩⟩ := legal
  · exact Or.inl (congrArg (embed hk r origin a small coherent) wait)
  · apply Or.inr
    refine ⟨b,?_,?_⟩
    · have permission := (permitted_lift hk r origin a small coherent (rvertex x)
        (messenger_inside r a x px) b).mpr allowed
      rcases permission with different|choice
      · exact Or.inl (fun equal => different (by
          simpa only [embed_raw hk r origin a small coherent x px] using congrArg Subtype.val equal))
      · exact Or.inr choice
    · apply Subtype.ext
      change (embed hk r origin a small coherent y).val=
        rawMove hk r b (embed hk r origin a small coherent x).val
      rw [embed_raw hk r origin a small coherent x px,embed_raw hk r origin a small coherent y py,
        next_lift hk r origin a small coherent (rvertex x) (messenger_inside r a x px) b,same]

theorem lift_col_shift {k : Nat} (hk : 15≤k) (r : Case) (origin : Int)
    (v : OddEndpointStrip.Vertex) (low : -(OddEndpointParameters.radius r : Int)≤v.1) :
    (lift hk origin v).1=shift
      (wrap (by omega : 0<k) (origin-(OddEndpointParameters.radius r : Int)))
      (v.1+(OddEndpointParameters.radius r : Int)).toNat := by
  change wrap (by omega : 0<k) (v.1+origin)=_
  rw [←wrap_shift]
  congr 1
  omega

theorem project_outside_window {k : Nat} (hk : 15≤k) (r : Case) (origin : Int)
    (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
    (v : Raw k) (out : projectRaw hk r origin v=outside) :
    ¬CyclicWindow.Inside
      (wrap (by omega : 0<k) (origin-(OddEndpointParameters.radius r : Int)))
      (2*OddEndpointParameters.radius r) v.1 := by
  rintro ⟨u,hu,same⟩
  let w : OddEndpointStrip.Vertex := ((u : Int)-(OddEndpointParameters.radius r : Int),v.2)
  have inside : inWindow (OddEndpointParameters.radius r) w := by
    dsimp [w,inWindow]
    omega
  have rawSame : lift hk origin w=v := by
    apply Prod.ext
    · rw [lift_col_shift hk r origin w inside.1]
      have offset : (w.1+(OddEndpointParameters.radius r : Int)).toNat=u := by dsimp [w]; omega
      rw [offset]
      exact same
    · rfl
  have result := project_lift hk r origin short w (by have := inside.1; omega)
    (by have := inside.2; omega)
  rw [rawSame,out] at result
  exact pack_not_outside r w inside result.symm

theorem outside_reply {k : Nat} (hk : 15≤k) (r : Case) (origin : Int)
    (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
    (s t : Vertex hk r) (out : projectRaw hk r origin s.val=outside)
    (legal : Legal (edge hk r) s t) :
    projectRaw hk r origin t.val=outside ∨ boundary r (projectRaw hk r origin t.val) := by
  rcases project_cases hk r origin t.val with outside|⟨_,inside,same⟩
  · exact Or.inl outside
  · apply Or.inr
    let u := ((cvertex (projectRaw hk r origin t.val)).1+(OddEndpointParameters.radius r : Int)).toNat
    have value : (u : Int)=(cvertex (projectRaw hk r origin t.val)).1+
        (OddEndpointParameters.radius r : Int) := by dsimp [u]; have := inside.1; omega
    have col : t.val.1=shift
        (wrap (by omega : 0<k) (origin-(OddEndpointParameters.radius r : Int))) u := by
      rw [←same]
      exact lift_col_shift hk r origin _ inside.1
    have move := legal_short hk r legal
    rw [col] at move
    have entered := CyclicWindow.outside_entries _ s.val.1
      (project_outside_window hk r origin short s.val out)
      (show u≤2*OddEndpointParameters.radius r by have := inside.2; omega) move
    unfold boundary
    omega

set_option maxRecDepth 2048 in
theorem pursuer_complete {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
    (coherent : Coherent k r origin a) (s t : Vertex hk r) (legal : Legal (edge hk r) s t) :
    pursuer r a (projectRaw hk r origin s.val) (projectRaw hk r origin t.val) := by
  refine ⟨project_present hk r origin a small coherent s,project_present hk r origin a small coherent t,?_⟩
  by_cases out : projectRaw hk r origin s.val=outside
  · rw [if_pos out]
    exact outside_reply hk r origin short s t out legal
  · rw [if_neg out]
    rcases legal with wait|arrow
    · exact Or.inl (congrArg (fun v : Vertex hk r => projectRaw hk r origin v.val) wait.symm)
    · rcases project_cases hk r origin s.val with impossible|⟨_,inside,same⟩
      · exact False.elim (out impossible)
      · obtain ⟨b,allowed,equal⟩ := arrow
        have available : present r a (cvertex (projectRaw hk r origin s.val)) :=
          ((project_present hk r origin a small coherent s).resolve_left out).2
        have localAllowed : permitted r a (cvertex (projectRaw hk r origin s.val)) b := by
          apply (permitted_lift hk r origin a small coherent _ inside b).mp
          rw [same]
          rcases allowed with different|choice
          · exact Or.inl (fun h => different (Subtype.ext h))
          · exact Or.inr choice
        refine Or.inr ⟨b,localAllowed,?_⟩
        have head : t.val=lift hk origin (next r a b (cvertex (projectRaw hk r origin s.val))) := by
          have raw := congrArg Subtype.val equal
          change t.val=rawMove hk r b s.val at raw
          rw [←same,next_lift hk r origin a small coherent _ inside b] at raw
          exact raw
        have jump := next_jump r a b _ available localAllowed
        rw [head]
        exact project_lift hk r origin short _ (by have := inside.1; omega)
          (by have := inside.2; omega)

noncomputable def simulation {k : Nat} (hk : 15≤k) (r : Case) (origin : Int) (a : Option Int)
    (small : 2*OddEndpointParameters.radius r+OddEndpointParameters.span r<k)
    (short : 2*OddEndpointParameters.radius r+OddEndpointParameters.jump r<k)
    (coherent : Coherent k r origin a) : Simulation (edge hk r) (arena r a) where
  embed := embed hk r origin a small coherent
  project := fun v => projectRaw hk r origin v.val
  messenger_sound := messenger_sound hk r origin a small coherent
  pursuer_complete := pursuer_complete hk r origin a small short coherent
  collision_complete := by
    intro x c same
    by_cases present : presentR r a x
    · exact (collision_iff hk r origin a small short coherent x c present).mpr same
    · exact Or.inl present

#print axioms collision_iff
#print axioms simulation
end Delivery.OddEndpointProjection
