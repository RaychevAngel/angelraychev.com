import OddEndpointParameters

/-! The six literal odd-endpoint patches on the integer strip. Each of the
two displayed permutations is smoothed independently through at most five
deleted vertices, then one specified arrow is removed. These are structural
lemmas, not local game certificates. -/
namespace Delivery.OddEndpointStrip
abbrev Vertex := Int × Fin 6
abbrev Case := Fin 6

def sigma (r : Case) : List (Fin 6) :=
  if r.val=0 then [0,2,5,1,4,3]
  else if r.val=1 then [0,5,1,4,3,2]
  else if r.val=2 ∨ r.val=5 then [3,5,0,2,4,1]
  else [4,1,5,2,0,3]

def voltage (r : Case) : List Int :=
  if r.val=1 then [-1,1,1,-1,-1,1]
  else if r.val=2 ∨ r.val=5 then [-1,1,-1,-1,-1,0]
  else [-1,-1,1,1,-1,1]

def stepSpec (r : Case) (second : Bool) (j : Fin 6) : Int × Fin 6 :=
  if second then ((voltage r)[j.val]!, (sigma r)[j.val]!)
  else (if j.val=5 then 1 else 0, Fin.ofNat 6 (j.val+1))

def raw (r : Case) (second : Bool) (v : Vertex) : Vertex :=
  (v.1+(stepSpec r second v.2).1,(stepSpec r second v.2).2)

def holes (r : Case) : List Vertex :=
  match r.val with
  | 0 => []
  | 1 => [(0,3)]
  | 2 => [(0,0),(0,1)]
  | 3 => [(0,2),(0,3),(0,4)]
  | 4 => [(-1,4),(0,2),(0,3),(0,4)]
  | _ => [(0,0),(0,1),(1,0),(1,1),(1,5)]

def skip (r : Case) (second : Bool) : Nat → Vertex → Vertex
  | 0,v => v
  | count+1,v => let w := raw r second v
    if w∈holes r then skip r second count w else w

def smooth (r : Case) (second : Bool) (v : Vertex) : Vertex := skip r second 6 v

def source (r : Case) : Vertex :=
  if r.val=0 then (0,0) else if r.val=1 then (1,4)
  else if r.val=2 ∨ r.val=5 then (0,5) else (0,1)

def deletedChoice (r : Case) : Bool := r.val=1 ∨ r.val=2 ∨ r.val=5

def target (r : Case) : Vertex := smooth r (deletedChoice r) (source r)

def permitted (r : Case) (v : Vertex) (second : Bool) : Prop :=
  v≠source r ∨ second≠deletedChoice r
instance (r : Case) (v : Vertex) (b : Bool) : Decidable (permitted r v b) :=
  inferInstanceAs (Decidable (_∨_))

def edge (r : Case) (v w : Vertex) : Prop :=
  v∉holes r ∧ ∃ b : Bool, permitted r v b ∧ w=smooth r b v
instance (r : Case) (v w : Vertex) : Decidable (edge r v w) :=
  inferInstanceAs (Decidable (_∧∃ _ : Bool, _∧_))

def supportLow (r : Case) : Int := if r.val=0 then 0 else -1
def supportHigh (r : Case) : Int := OddEndpointParameters.supportMax r

theorem raw_displacement (r : Case) (b : Bool) (j : Fin 6) :
    -1≤(stepSpec r b j).1 ∧ (stepSpec r b j).1≤1 := by
  have finite : ∀ r b j, -1≤(stepSpec r b j).1 ∧ (stepSpec r b j).1≤1 := by decide +kernel
  exact finite r b j

theorem holes_bounds (r : Case) {v : Vertex} (gone : v∈holes r) : -1≤v.1 ∧ v.1≤1 := by
  have finite : ∀ r, (holes r).all (fun v => decide (-1≤v.1 ∧ v.1≤1))=true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp (finite r)) v gone)

theorem raw_outside (r : Case) (b : Bool) (v : Vertex) (far : v.1 < -2 ∨ 2<v.1) :
    raw r b v∉holes r := by
  intro gone
  have bound := holes_bounds r gone
  have step := raw_displacement r b v.2
  simp only [raw] at bound
  omega

theorem smooth_outside (r : Case) (b : Bool) (v : Vertex) (far : v.1 < -2 ∨ 2<v.1) :
    smooth r b v=raw r b v := by
  simp only [smooth,skip,if_neg (raw_outside r b v far)]

def Good (r : Case) (v : Vertex) : Prop :=
  (∀ b, smooth r b v∉holes r ∧ smooth r b v≠v ∧
    -2≤(smooth r b v).1-v.1 ∧ (smooth r b v).1-v.1≤2 ∧
    (permitted r v b →
      -(OddEndpointParameters.jump r : Int)≤(smooth r b v).1-v.1 ∧
      (smooth r b v).1-v.1≤(OddEndpointParameters.jump r : Int))) ∧
  smooth r false v≠smooth r true v
instance (r : Case) (v : Vertex) : Decidable (Good r v) :=
  inferInstanceAs (Decidable ((∀ _ : Bool, _∧_∧_∧_∧(_→_∧_))∧_))

theorem finite_good : ∀ (r : Case) (i : Fin 5) (j : Fin 6),
    let v : Vertex := ((i.val : Int)-2,j)
    v∉holes r → Good r v := by decide +kernel

theorem step_shape : ∀ (r : Case) (j : Fin 6),
    (∀ b, (stepSpec r b j).1≠0 ∨ (stepSpec r b j).2≠j) ∧
    stepSpec r false j≠stepSpec r true j := by decide +kernel

theorem jump_positive (r : Case) : 1≤OddEndpointParameters.jump r := by
  unfold OddEndpointParameters.jump
  split <;> omega

theorem good (r : Case) (v : Vertex) (present : v∉holes r) : Good r v := by
  by_cases near : -2≤v.1 ∧ v.1≤2
  · let i : Fin 5 := ⟨(v.1+2).toNat,by omega⟩
    have col : (i.val : Int)-2=v.1 := by dsimp [i]; omega
    simpa only [col] using finite_good r i v.2 (by simpa only [col] using present)
  · have far : v.1 < -2 ∨ 2<v.1 := by omega
    have unchanged (b : Bool) := smooth_outside r b v far
    have shape := step_shape r v.2
    have J := jump_positive r
    constructor
    · intro b
      rw [unchanged b]
      have bounds := raw_displacement r b v.2
      refine ⟨raw_outside r b v far,?_,by dsimp [raw]; omega,
        by dsimp [raw]; omega,?_⟩
      · intro same
        have col := congrArg Prod.fst same
        have typ := congrArg Prod.snd same
        simp only [raw] at col typ
        exact (shape.1 b).elim (fun h => h (by omega)) (fun h => h typ)
      · intro _
        dsimp [raw]
        omega
    · rw [unchanged false,unchanged true]
      intro same
      apply shape.2
      apply Prod.ext
      · have col := congrArg Prod.fst same
        simp only [raw] at col
        omega
      · simpa only [raw] using congrArg (fun x : Vertex => x.2) same

/-- The support statement concerns changed outgoing tails, not all possible
heads. Heads may fall outside this interval. -/
theorem finite_support : ∀ (r : Case) (i : Fin 5) (j : Fin 6),
    let v : Vertex := ((i.val : Int)-2,j)
    (v.1<supportLow r ∨ supportHigh r<v.1) →
      v∉holes r ∧ v≠source r ∧ ∀ b, smooth r b v=raw r b v := by decide +kernel

theorem support_bounds (r : Case) : -1≤supportLow r ∧ supportHigh r≤2 := by
  have finite : ∀ r, -1≤supportLow r ∧ supportHigh r≤2 := by decide +kernel
  exact finite r

theorem source_bounds (r : Case) : -1≤(source r).1 ∧ (source r).1≤1 := by
  have finite : ∀ r, -1≤(source r).1 ∧ (source r).1≤1 := by decide +kernel
  exact finite r

theorem outside_support (r : Case) (v : Vertex)
    (outside : v.1<supportLow r ∨ supportHigh r<v.1) :
    v∉holes r ∧ v≠source r ∧ ∀ b, smooth r b v=raw r b v := by
  by_cases near : -2≤v.1 ∧ v.1≤2
  · let i : Fin 5 := ⟨(v.1+2).toNat,by omega⟩
    have col : (i.val : Int)-2=v.1 := by dsimp [i]; omega
    simpa only [col] using finite_support r i v.2 (by simpa only [col] using outside)
  · have far : v.1 < -2 ∨ 2<v.1 := by omega
    refine ⟨?_,?_,fun b => smooth_outside r b v far⟩
    · intro gone
      have := holes_bounds r gone
      omega
    · intro same
      have := source_bounds r
      rw [same] at far
      omega

theorem defect_valid : ∀ r : Case,
    source r∉holes r ∧ target r∉holes r ∧ source r≠target r ∧
      ¬edge r (source r) (target r) := by decide +kernel

def uniquePredecessor (r : Case) : Vertex :=
  if r.val=0 ∨ r.val=1 then (-1,3)
  else if r.val=2 then (1,4)
  else if r.val=5 then (2,4) else (-1,2)

theorem finite_incoming : ∀ (r : Case) (i : Fin 6) (j : Fin 6),
    let v : Vertex := ((i.val : Int)-2,j)
    edge r v (target r) ↔ v=uniquePredecessor r := by decide +kernel

theorem target_bounds (r : Case) : -1≤(target r).1 ∧ (target r).1≤2 := by
  have finite : ∀ r, -1≤(target r).1 ∧ (target r).1≤2 := by decide +kernel
  exact finite r

theorem predecessor_bounds (r : Case) :
    -1≤(uniquePredecessor r).1 ∧ (uniquePredecessor r).1≤2 := by
  have finite : ∀ r, -1≤(uniquePredecessor r).1 ∧
      (uniquePredecessor r).1≤2 := by decide +kernel
  exact finite r

/-- The low-indegree recipient really has exactly the one displayed
predecessor. This suffices for counting the eligible missing pairs later. -/
theorem incoming (r : Case) (v : Vertex) :
    edge r v (target r) ↔ v=uniquePredecessor r := by
  by_cases near : -2≤v.1 ∧ v.1≤3
  · let i : Fin 6 := ⟨(v.1+2).toNat,by omega⟩
    have col : (i.val : Int)-2=v.1 := by dsimp [i]; omega
    simpa only [col] using finite_incoming r i v.2
  · have far : v.1 < -2 ∨ 2<v.1 := by omega
    have no : ¬edge r v (target r) := by
      rintro ⟨_,b,_,same⟩
      have targetRange := target_bounds r
      have step := raw_displacement r b v.2
      rw [smooth_outside r b v far] at same
      have col := congrArg (fun w : Vertex => w.1) same
      simp only [raw] at col
      omega
    have different : v≠uniquePredecessor r := by
      intro same
      have bounds := predecessor_bounds r
      rw [same] at near
      omega
    simp only [no,different]

theorem ordinary_row (r : Case) (v w : Vertex)
    (present : v∉holes r) (ordinary : v≠source r) :
    edge r v w ↔ w=smooth r false v ∨ w=smooth r true v := by
  constructor
  · rintro ⟨_,b,_,same⟩
    cases b with
    | false => exact Or.inl same
    | true => exact Or.inr same
  · rintro (first|second)
    · exact ⟨present,false,Or.inl ordinary,first⟩
    · exact ⟨present,true,Or.inl ordinary,second⟩

theorem source_row (r : Case) (w : Vertex) :
    edge r (source r) w ↔ w=smooth r (!(deletedChoice r)) (source r) := by
  constructor
  · rintro ⟨_,b,allowed,same⟩
    have other : b≠deletedChoice r := allowed.resolve_left (fun h => h rfl)
    have choice : b=!(deletedChoice r) := by cases b <;> cases h : deletedChoice r <;> simp_all
    simpa only [choice] using same
  · intro same
    refine ⟨(defect_valid r).1,!(deletedChoice r),Or.inr ?_,same⟩
    cases deletedChoice r <;> decide

theorem holes_length : ∀ r : Case, (holes r).length=r.val := by decide +kernel
theorem holes_nodup : ∀ r : Case, (holes r).Nodup := by decide +kernel

theorem finite_output_bounds : ∀ (r : Case) (i : Fin 5) (j : Fin 6) (b : Bool),
    let v : Vertex := ((i.val : Int)-2,j)
    v∉holes r → -3≤(smooth r b v).1 ∧ (smooth r b v).1≤3 := by decide +kernel

/-- Uniform bounds at the two ends of the chosen cyclic representative
interval. They rule out aliasing a hole through a different cyclic lift. -/
theorem output_bounds {k : Nat} (large : 15≤k) (r : Case) (b : Bool) (v : Vertex)
    (present : v∉holes r) (low : -2≤v.1) (high : v.1≤(k : Int)-3) :
    -3≤(smooth r b v).1 ∧ (smooth r b v).1≤(k : Int)-2 := by
  by_cases near : v.1≤2
  · let i : Fin 5 := ⟨(v.1+2).toNat,by omega⟩
    have col : (i.val : Int)-2=v.1 := by dsimp [i]; omega
    have bounds := finite_output_bounds r i v.2 b (by simpa only [col] using present)
    simp only [col] at bounds
    change -3≤(smooth r b v).1 ∧ (smooth r b v).1≤3 at bounds
    exact ⟨bounds.1,by omega⟩
  · rw [smooth_outside r b v (by omega)]
    have step := raw_displacement r b v.2
    dsimp [raw]
    omega

#print axioms incoming

#print axioms good
#print axioms outside_support
#print axioms defect_valid
end Delivery.OddEndpointStrip
