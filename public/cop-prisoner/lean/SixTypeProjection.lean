import SixTypeLocal
import SixTypeGraph
import CyclicWindow

namespace Delivery.SixTypeProjection
open CyclicArithmetic SixTypeGraph SixTypeLocal LocalArena FiniteGame

def crop {k : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k) : List Nat :=
  (List.range 13).filter fun u => decide (H (shift base u))

theorem mem_crop {k u : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k)
    (hu : u<13) : u∈crop H base ↔ H (shift base u) := by simp [crop,hu]

theorem canonical_crop {k r : Nat} (base : Fin k) :
    crop (holes r) base=SparseCropCoverage.crop k r base.val := rfl

theorem pack_val {u : Nat} (j : Fin 6) (hu : u<13) :
    (pack u j).val=6*u+j.val := by simp [pack,hu]
theorem pack_col {u : Nat} (j : Fin 6) (hu : u<13) :
    (pack u j).val/6=u := by rw [pack_val j hu]; have := j.isLt; omega
theorem pack_type {u : Nat} (j : Fin 6) (hu : u<13) :
    (pack u j).val%6=j.val := by rw [pack_val j hu]; have := j.isLt; omega
theorem pack_inside {u : Nat} (j : Fin 6) (hu : u<13) : (pack u j).val<78 := by
  rw [pack_val j hu]; have := j.isLt; omega
theorem pack_outside {u : Nat} (j : Fin 6) (hu : 13≤u) : pack u j=SixTypeLocal.omega := by
  simp [pack,show ¬u<13 by omega]
theorem rcop_pack (r : R) :
    rcop r=pack (rcol r) ⟨rtype r,Nat.mod_lt _ (by decide)⟩ := by
  have hr := r.isLt
  apply Fin.ext
  rw [pack_val _ (show rcol r<13 by unfold rcol; omega)]
  dsimp [rcop,rcol,rtype]
  omega

noncomputable def projectRaw {k : Nat} (base : Fin k) (v : Raw k) : C :=
  if h : ∃ u : Fin 13, shift base u.val=v.1 then pack (Classical.choose h).val v.2
  else SixTypeLocal.omega

theorem project_shift {k u : Nat} (hk : 15≤k) (base : Fin k) (j : Fin 6)
    (hu : u<k) : projectRaw base (shift base u,j)=pack u j := by
  classical
  unfold projectRaw
  split
  · rename_i h
    have hc := Classical.choose_spec h
    have hv := (Classical.choose h).isLt
    have equal := (shift_eq_iff base (Classical.choose h).val u).mp hc
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt hu] at equal
    rw [equal]
  · rename_i h
    have large : 13≤u := by
      apply Classical.byContradiction
      intro hu'
      exact h ⟨⟨u,by omega⟩,rfl⟩
    exact (pack_outside j large).symm

theorem project_prev_zero {k : Nat} (hk : 15≤k) (base : Fin k) (j : Fin 6) :
    projectRaw base (prev base,j)=SixTypeLocal.omega := by
  classical
  unfold projectRaw
  split
  · rename_i h
    obtain ⟨u,equal⟩ := h
    have moved := congrArg (fun i => shift i 1) equal
    rw [shift_add,shift_prev] at moved
    have off := (shift_eq_iff base (u.val+1) 0).mp (moved.trans (shift_zero base).symm)
    rw [Nat.mod_eq_of_lt (by have := u.isLt; omega)] at off
    simp only [Nat.zero_mod] at off
    omega
  · rfl

theorem prev_offset {k u : Nat} (base : Fin k) (positive : 0<u) :
    prev (shift base u)=shift base (u-1) := by
  have sum : u-1+1=u := by omega
  rw [←sum,←shift_add,prev_shift]
  congr 1

theorem project_prev {k u : Nat} (hk : 15≤k) (base : Fin k) (j : Fin 6)
    (hu : u<13) : projectRaw base (prev (shift base u),j)=
      if u=0 then SixTypeLocal.omega else pack (u-1) j := by
  by_cases zero : u=0
  · subst u
    simp only [shift_zero]
    exact project_prev_zero hk base j
  · rw [if_neg zero,prev_offset base (by omega)]
    exact project_shift hk base j (by omega)

theorem first_diagram {k u : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (j : Fin 6) (hu : u<13) :
    projectRaw base (firstRaw H (shift base u,j))=
      SixTypeLocal.first (crop H base) (pack u j) := by
  have hu' : u<k := by omega
  rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [firstRaw,SixTypeLocal.first,pack_col _ hu,pack_type _ hu,
      val_three,val_four,val_five,Fin.val_zero,Fin.val_one]
  all_goals try simp only [show (2:Fin 6).val=2 from rfl]
  all_goals try simp only [shift_add,project_shift hk base _ hu',
    project_shift hk base _ (show u+1<k by omega),mem_crop H base hu]

theorem second_diagram {k u : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (j : Fin 6) (hu : u<13) :
    projectRaw base (secondRaw H (shift base u,j))=
      SixTypeLocal.second (crop H base) (pack u j) := by
  have hu' : u<k := by omega
  rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [secondRaw,SixTypeLocal.second,pack_col _ hu,pack_type _ hu,
      val_three,val_four,val_five,Fin.val_zero,Fin.val_one]
  all_goals try simp only [show (2:Fin 6).val=2 from rfl]
  all_goals try simp only [shift_add,project_shift hk base _ hu',
    project_shift hk base _ (show u+1<k by omega),project_prev hk base _ hu]
  by_cases inside : u+1<13
  · simp only [mem_crop H base inside]
    by_cases h : H (shift base (u+1)) <;>
      simp [h,project_shift hk base _ (show u+2<k by omega),
        project_shift hk base _ (show u+1<k by omega)]
  · have edge : u=12 := by omega
    subst u
    have no : 13∉crop H base := by simp [crop]
    simp only [no,if_false]
    by_cases h : H (shift base 13) <;>
      simp [h,project_shift hk base _ (show 14<k by omega),
        project_shift hk base _ (show 13<k by omega),pack_outside]

theorem pack_injective {u v : Nat} {j l : Fin 6} (hu : u<13) (hv : v<13)
    (same : pack u j=pack v l) : u=v ∧ j=l := by
  have h := congrArg Fin.val same
  rw [pack_val j hu,pack_val l hv] at h
  have hj := j.isLt
  have hl := l.isLt
  constructor
  · omega
  · apply Fin.ext; omega

theorem project_eq_pack {k u : Nat} (_hk : 15≤k) (base : Fin k) (v : Raw k)
    (j : Fin 6) (hu : u<13) (same : projectRaw base v=pack u j) :
    v=(shift base u,j) := by
  classical
  unfold projectRaw at same
  split at same
  · rename_i h
    have col := Classical.choose_spec h
    have eqs := pack_injective (Classical.choose h).isLt hu same
    apply Prod.ext
    · simpa only [eqs.1] using col.symm
    · exact eqs.2
  · have small := pack_inside j hu
    have equal := congrArg Fin.val same
    change 78=(pack u j).val at equal
    omega

theorem project_outside {k : Nat} (base : Fin k) (v : Raw k)
    (outside : ¬CyclicWindow.Inside base 12 v.1) : projectRaw base v=SixTypeLocal.omega := by
  classical
  unfold projectRaw
  apply dif_neg
  rintro ⟨u,equal⟩
  exact outside ⟨u.val,by have := u.isLt; omega,equal⟩

theorem present_pack {k u : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k)
    (j : Fin 6) (hu : u<13) :
    presentC (crop H base) (pack u j) ↔ Present H (shift base u,j) := by
  have small := pack_inside j hu
  simp only [presentC,pack_col j hu,pack_type j hu,Present,
    show ¬(pack u j).val=78 by omega, false_or,mem_crop H base hu]
  have eqs : j=4 ↔ j.val=4 := by simp [Fin.ext_iff]
  simp only [ne_eq,eqs]

theorem project_present {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (v : Vertex H) : presentC (crop H base) (projectRaw base v.val) := by
  classical
  by_cases inside : CyclicWindow.Inside base 12 v.val.1
  · obtain ⟨u,hu,equal⟩ := inside
    have raw : v.val=(shift base u,v.val.2) := Prod.ext equal.symm rfl
    rw [raw,project_shift hk base _ (by omega)]
    apply (present_pack H base _ (by omega)).mpr
    simpa only [←raw] using v.property
  · rw [project_outside base _ inside]
    exact Or.inl rfl

def liftRaw {k : Nat} (base : Fin k) (r : R) : Raw k :=
  (shift base (rcol r),⟨rtype r,Nat.mod_lt _ (by decide)⟩)

theorem rcol_bound (r : R) : 2≤rcol r ∧ rcol r≤10 := by
  have := r.isLt
  unfold rcol
  omega

theorem present_lift {k : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k) (r : R) :
    Present H (liftRaw base r) ↔ presentR (crop H base) r := by
  have hb := rcol_bound r
  have eqs : (⟨rtype r,Nat.mod_lt _ (by decide)⟩ : Fin 6)=4 ↔ rtype r=4 := by
    simp [Fin.ext_iff]
  simp only [Present,liftRaw,presentR,ne_eq,eqs,mem_crop (u:=rcol r) H base (by omega)]

def embed {k : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k) (r : R) : Vertex H :=
  if h : presentR (crop H base) r then ⟨liftRaw base r,(present_lift H base r).mpr h⟩
  else ⟨(shift base (rcol r),0),Or.inl (show (0:Fin 6)≠4 by decide)⟩

theorem embed_raw {k : Nat} (H : Fin k → Prop) [DecidablePred H] (base : Fin k) (r : R)
    (hr : presentR (crop H base) r) : (embed H base r).val=liftRaw base r := by
  simp [embed,hr]

theorem project_embed {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (r : R) (hr : presentR (crop H base) r) :
    projectRaw base (embed H base r).val=rcop r := by
  have hb := rcol_bound r
  rw [embed_raw H base r hr]
  unfold liftRaw
  rw [project_shift hk base _ (by omega),←rcop_pack]

theorem collision_iff {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (r : R) (c : Vertex H) (hr : presentR (crop H base) r) :
    (arena (crop H base)).collision r (projectRaw base c.val) ↔ embed H base r=c := by
  change (¬presentR (crop H base) r ∨ rcop r=projectRaw base c.val) ↔ _
  simp only [hr,not_true_eq_false,false_or]
  constructor
  · intro equal
    have hb := rcol_bound r
    rw [rcop_pack] at equal
    have raw := project_eq_pack hk base c.val _ (by omega) equal.symm
    apply Subtype.ext
    rw [embed_raw H base r hr]
    exact raw.symm
  · intro equal
    rw [←equal,project_embed hk H base r hr]

theorem messenger_sound {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (r z : R) (move : (arena (crop H base)).messenger r z) :
    Legal (edge H) (embed H base r) (embed H base z) := by
  obtain ⟨hr,hz,wait | first | second⟩ := move
  · exact Or.inl (congrArg (embed H base) wait.symm)
  · apply Or.inr; apply Or.inl
    apply Subtype.ext
    have rb := rcol_bound r
    have zb := rcol_bound z
    have projected := first_diagram hk H base
      (⟨rtype r,Nat.mod_lt _ (by decide)⟩ : Fin 6) (show rcol r<13 by omega)
    rw [←rcop_pack,←first,rcop_pack z] at projected
    have actual := project_eq_pack hk base _ _ (by omega) projected
    simp only [SixTypeGraph.first,embed_raw H base r hr,embed_raw H base z hz]
    exact actual.symm
  · apply Or.inr; apply Or.inr
    apply Subtype.ext
    have rb := rcol_bound r
    have zb := rcol_bound z
    have projected := second_diagram hk H base
      (⟨rtype r,Nat.mod_lt _ (by decide)⟩ : Fin 6) (show rcol r<13 by omega)
    rw [←rcop_pack,←second,rcop_pack z] at projected
    have actual := project_eq_pack hk base _ _ (by omega) projected
    simp only [SixTypeGraph.second,embed_raw H base r hr,embed_raw H base z hz]
    exact actual.symm

theorem first_short {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Raw k) :
    CyclicWindow.ShortMove 2 v.1 (firstRaw H v).1 := by
  obtain ⟨i,j⟩ := v
  rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [firstRaw,val_three,val_four,val_five,Fin.val_zero,Fin.val_one,
      show (2:Fin 6).val=2 from rfl]
  all_goals first
    | exact ⟨0,by decide,Or.inl (shift_zero i).symm⟩
    | exact ⟨1,by decide,Or.inl rfl⟩

theorem second_short {k : Nat} (H : Fin k → Prop) [DecidablePred H] (v : Raw k) :
    CyclicWindow.ShortMove 2 v.1 (secondRaw H v).1 := by
  obtain ⟨i,j⟩ := v
  rcases type_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [secondRaw,val_three,val_four,val_five,Fin.val_zero,Fin.val_one,
      show (2:Fin 6).val=2 from rfl]
  all_goals first
    | exact ⟨0,by decide,Or.inl (shift_zero i).symm⟩
    | exact ⟨1,by decide,Or.inl rfl⟩
    | exact ⟨1,by decide,Or.inr (shift_prev i).symm⟩
    | (split <;> first | exact ⟨2,by decide,Or.inl rfl⟩ | exact ⟨1,by decide,Or.inl rfl⟩)

theorem legal_short {k : Nat} (H : Fin k → Prop) [DecidablePred H] (c d : Vertex H)
    (move : Legal (edge H) c d) : CyclicWindow.ShortMove 2 c.val.1 d.val.1 := by
  rcases move with same | first | second
  · rw [same]; exact ⟨0,by decide,Or.inl (shift_zero _).symm⟩
  · rw [first]; exact first_short H c.val
  · rw [second]; exact second_short H c.val

theorem pursuer_complete {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) (c d : Vertex H) (move : Legal (edge H) c d) :
    (arena (crop H base)).pursuer (projectRaw base c.val) (projectRaw base d.val) := by
  classical
  change projectRaw base d.val∈replies (crop H base) (projectRaw base c.val)
  by_cases inside : CyclicWindow.Inside base 12 c.val.1
  · obtain ⟨u,hu,equal⟩ := inside
    have raw : c.val=(shift base u,c.val.2) := Prod.ext equal.symm rfl
    have pc : projectRaw base c.val=pack u c.val.2 := by
      rw [raw,project_shift hk base _ (by omega)]
    have hp := project_present hk H base c
    rw [pc] at hp ⊢
    have small := pack_inside c.val.2 (show u<13 by omega)
    rw [replies,if_neg (show ¬(pack u c.val.2).val=78 by omega),if_pos hp]
    rcases move with wait | first | second
    · rw [←wait,pc]; simp
    · have pd : projectRaw base d.val=SixTypeLocal.first (crop H base) (pack u c.val.2) := by
        rw [first]
        change projectRaw base (firstRaw H c.val)=_
        rw [raw]
        exact first_diagram hk H base _ (by omega)
      simp [pd]
    · have pd : projectRaw base d.val=SixTypeLocal.second (crop H base) (pack u c.val.2) := by
        rw [second]
        change projectRaw base (secondRaw H c.val)=_
        rw [raw]
        exact second_diagram hk H base _ (by omega)
      simp [pd]
  · have pc := project_outside base c.val inside
    rw [pc]
    have hp := project_present hk H base d
    have boundary : (projectRaw base d.val).val=78 ∨
        (projectRaw base d.val).val/6<2 ∨ 10<(projectRaw base d.val).val/6 := by
      by_cases dest : CyclicWindow.Inside base 12 d.val.1
      · obtain ⟨u,hu,equal⟩ := dest
        have raw : d.val=(shift base u,d.val.2) := Prod.ext equal.symm rfl
        have jump := legal_short H c d move
        rw [←equal] at jump
        have boundary := CyclicWindow.radius_six_entries base c.val.1 inside hu jump
        rw [raw,project_shift hk base _ (by omega),pack_col _ (by omega)]
        omega
      · rw [project_outside base d.val dest]
        exact Or.inl rfl
    rw [replies,if_pos (show SixTypeLocal.omega.val=78 from rfl)]
    simp only [List.mem_filter,List.mem_finRange,decide_eq_true_eq,true_and]
    exact ⟨hp,boundary⟩

noncomputable def simulation {k : Nat} (hk : 15≤k) (H : Fin k → Prop) [DecidablePred H]
    (base : Fin k) : Simulation (edge H) (arena (crop H base)) where
  embed := embed H base
  project c := projectRaw base c.val
  messenger_sound := messenger_sound hk H base
  pursuer_complete := pursuer_complete hk H base
  collision_complete r c same := by
    by_cases hr : presentR (crop H base) r
    · exact (collision_iff hk H base r c hr).mpr same
    · exact Or.inl hr

#print axioms simulation
#print axioms collision_iff
end Delivery.SixTypeProjection


