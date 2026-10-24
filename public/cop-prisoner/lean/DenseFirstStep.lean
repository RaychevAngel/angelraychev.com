import DenseOddCore
import DenseStaircase
import ConstructionCounts

/-! The next0 dense step: the explicit four-vertex missing-arc fork.
The abstract fork proof below is instantiated by the literal even and odd
cores; its local hypotheses are proved, never assumed in the final graph. -/
namespace Delivery.DenseFirstStep
open FiniteGame Extremal DenseCombinatorics CyclicArithmetic

structure ForkData (V : Type) where
  missing : Graph V
  next0 : V → V
  next1 : V → V
  loopless : ∀ s, ¬ missing s s
  rows : ∀ s t, missing s t ↔ t = next0 s ∨ t = next1 s
  distinct : ∀ s, next0 s ≠ next1 s
  unblocked : ∀ s t c, missing s t →
    (missing s (next0 c) ∨ missing (next0 c) t) →
    (missing s (next1 c) ∨ missing (next1 c) t) → c = s
  a : V
  b : V
  d : V
  e : V
  attachments : [a,b,d,e].Nodup
  branchOld : ∀ s t, missing s t →
    ¬ ((missing s a ∨ missing a t) ∧ (missing s b ∨ missing b t)) ∧
    ¬ ((missing s d ∨ missing d t) ∧ (missing s e ∨ missing e t))
  cross : (∀ t, (t = a ∨ t = b) → ¬ (missing d t ∧ missing e t)) ∧
    (∀ t, (t = d ∨ t = e) → ¬ (missing a t ∧ missing b t))
  oldBranch : ∀ c t,
    ((t = a ∨ t = b) →
      ¬ ((next0 c = a ∨ next0 c = b ∨ missing (next0 c) t) ∧
        (next1 c = a ∨ next1 c = b ∨ missing (next1 c) t))) ∧
    ((t = d ∨ t = e) →
      ¬ ((next0 c = d ∨ next0 c = e ∨ missing (next0 c) t) ∧
        (next1 c = d ∨ next1 c = e ∨ missing (next1 c) t)))

inductive Vertex (V : Type) where
  | old : V → Vertex V
  | c | x | y | z
  deriving DecidableEq

namespace ForkData
variable {V : Type} (D : ForkData V)

def first : Vertex V → Vertex V
  | .old s => .old (D.next0 s)
  | .c => .x
  | .x => .y
  | .y => .old D.a
  | .z => .old D.d

def second : Vertex V → Vertex V
  | .old s => .old (D.next1 s)
  | .c => .x
  | .x => .z
  | .y => .old D.b
  | .z => .old D.e

def relation : Graph (Vertex V)
  | .old s, .old t => D.missing s t
  | .c, .x => True
  | .x, .y => True
  | .x, .z => True
  | .y, .old t => t = D.a ∨ t = D.b
  | .z, .old t => t = D.d ∨ t = D.e
  | _, _ => False

def edge : Graph (Vertex V) := DenseCounting.complement D.relation

theorem relation_loopless (s : Vertex V) : ¬ D.relation s s := by
  cases s <;> simp [relation,D.loopless]

theorem relation_rows (s t : Vertex V) :
    D.relation s t ↔ t = D.first s ∨ t = D.second s := by
  cases s <;> cases t <;> simp [relation,first,second,D.rows]

theorem neighbours_distinct (s : Vertex V) (notc : s ≠ .c) :
    D.first s ≠ D.second s := by
  have att := D.attachments
  simp only [List.nodup_cons,List.mem_cons,
    List.not_mem_nil,not_false_eq_true,and_true,not_or] at att
  cases s <;> simp_all [first,second,D.distinct]

set_option maxHeartbeats 800000 in
theorem fork_unblocked (s t cop : Vertex V) (pair : D.relation s t)
    (good : s ≠ .x)
    (block0 : D.relation s (D.first cop) ∨ D.relation (D.first cop) t)
    (block1 : D.relation s (D.second cop) ∨ D.relation (D.second cop) t) : cop = s := by
  have att := D.attachments
  simp only [List.nodup_cons,List.mem_cons,
    List.not_mem_nil,not_false_eq_true,and_true,not_or] at att
  cases s <;> cases t <;> cases cop <;>
    simp_all [relation,first,second]
  all_goals first
    | exact False.elim ((D.branchOld _ _ pair).2 ⟨block0,block1⟩)
    | grind [D.unblocked,D.branchOld,D.oldBranch,D.cross]


theorem safe_neighbor {s t cop : Vertex V} (pair : D.relation s t)
    (good : s ≠ .x) (initial : cop ≠ s) :
    ∃ u, D.relation cop u ∧ ¬ D.relation s u ∧ ¬ D.relation u t := by
  classical
  by_cases good0 : ¬ D.relation s (D.first cop) ∧ ¬ D.relation (D.first cop) t
  · exact ⟨D.first cop, (D.relation_rows _ _).mpr (Or.inl rfl), good0⟩
  by_cases good1 : ¬ D.relation s (D.second cop) ∧ ¬ D.relation (D.second cop) t
  · exact ⟨D.second cop, (D.relation_rows _ _).mpr (Or.inr rfl), good1⟩
  have block0 : D.relation s (D.first cop) ∨ D.relation (D.first cop) t := by grind
  have block1 : D.relation s (D.second cop) ∨ D.relation (D.second cop) t := by grind
  exact False.elim (initial (D.fork_unblocked s t cop pair good block0 block1))

theorem two_move (s t : Vertex V) (good : s ≠ .x) : Universal D.edge t 2 s := by
  classical
  intro cop initial
  by_cases same : s = t
  · subst t; exact Winning.delivered
  by_cases direct : D.edge s t
  · exact Winning.finish (Ne.symm initial) (Or.inr direct)
  have pair : D.relation s t := Classical.byContradiction (fun h => direct ⟨same,h⟩)
  obtain ⟨u,cu,su,ut⟩ := D.safe_neighbor pair good initial
  have firstEdge : D.edge s u := ⟨fun eq => ut (eq ▸ pair),su⟩
  have lastEdge : D.edge u t := ⟨fun eq => su (eq ▸ pair),ut⟩
  exact DenseCounting.safe_intermediate_winning (Ne.symm initial) firstEdge lastEdge
    (DenseCounting.missing_arc_unreachable D.relation_loopless cu)

theorem bad_source (t : Vertex V) (pair : D.relation .x t) :
    ¬ Guaranteed D.edge .x t := by
  intro guaranteed
  have different : Vertex.x ≠ t := fun same => D.relation_loopless .x (same ▸ pair)
  obtain ⟨k,win⟩ := guaranteed .c (by simp)
  apply VertexBound.source_camping different (fun edge => edge.2 pair) ?_ k win
  intro u outgoing
  cases u <;> simp_all [edge,DenseCounting.complement,relation,Legal]

theorem indirect_iff (s t : Vertex V) :
    Indirect D.edge s t ↔ D.relation s t ∧ s ≠ .x := by
  classical
  constructor
  · intro h
    have pair : D.relation s t := Classical.byContradiction (fun missing => h.2.1 ⟨h.1,missing⟩)
    refine ⟨pair,?_⟩
    intro eq; subst s
    exact D.bad_source t pair h.2.2
  · rintro ⟨pair,good⟩
    exact ⟨fun eq => D.relation_loopless s (eq ▸ pair),fun edge => edge.2 pair,
      universal_guaranteed (D.two_move s t good)⟩

end ForkData


/-- A literal numbering, used only to put the already defined graph on Fin. -/
structure Numbering (V : Type) (n : Nat) where
  encode : V → Fin n
  decode : Fin n → V
  left_inv : ∀ v, decode (encode v) = v
  right_inv : ∀ v, encode (decode v) = v

namespace Numbering
variable {V : Type} {n : Nat} (N : Numbering V n)

def forkEncode : Vertex V → Fin (n+4)
  | .old v => ⟨(N.encode v).val,by omega⟩
  | .c => ⟨n,by omega⟩
  | .x => ⟨n+1,by omega⟩
  | .y => ⟨n+2,by omega⟩
  | .z => ⟨n+3,by omega⟩

def forkDecode (v : Fin (n+4)) : Vertex V :=
  if h : v.val < n then .old (N.decode ⟨v.val,h⟩)
  else if v.val = n then .c
  else if v.val = n+1 then .x
  else if v.val = n+2 then .y else .z

@[simp] theorem fork_left (v : Vertex V) : N.forkDecode (N.forkEncode v) = v := by
  cases v with
  | old v => simp [forkEncode,forkDecode,(N.encode v).isLt,N.left_inv]
  | c => simp [forkEncode,forkDecode]
  | x => simp [forkEncode,forkDecode]
  | y => simp [forkEncode,forkDecode]
  | z => simp [forkEncode,forkDecode]

@[simp] theorem fork_right (v : Fin (n+4)) : N.forkEncode (N.forkDecode v) = v := by
  unfold forkDecode
  split
  · simp only [forkEncode,N.right_inv]
  · repeat' split
    all_goals apply Fin.ext
    all_goals dsimp only [forkEncode]
    all_goals omega

theorem fork_injective {s t : Vertex V} (same : N.forkEncode s = N.forkEncode t) : s = t := by
  simpa only [N.fork_left] using congrArg N.forkDecode same

theorem decode_eq_iff (s : Fin (n+4)) (t : Vertex V) :
    N.forkDecode s = t ↔ s = N.forkEncode t := by
  constructor
  · intro h; simpa only [N.fork_right] using congrArg N.forkEncode h
  · intro h; subst s; exact N.fork_left t

end Numbering

namespace ForkData
variable {V : Type} {n : Nat} (D : ForkData V) (N : Numbering V n)

def graph : Graph (Fin (n+4)) := fun s t => D.edge (N.forkDecode s) (N.forkDecode t)

def graphIso : GraphRelabeling.Iso D.edge (D.graph N) where
  toFun := N.forkEncode
  invFun := N.forkDecode
  left_inv := N.fork_left
  right_inv := N.fork_right
  edge_iff := fun s t => by simp [graph]

theorem graph_loopless : Loopless (D.graph N) := fun _ edge => edge.1 rfl

theorem graph_missing_iff (s t : Fin (n+4)) :
    (s ≠ t ∧ ¬ D.graph N s t) ↔ D.relation (N.forkDecode s) (N.forkDecode t) := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro absent
    exact h.2 ⟨fun same => h.1 (by simpa only [N.fork_right] using congrArg N.forkEncode same),absent⟩
  · intro h
    exact ⟨fun same => D.relation_loopless _ (same ▸ h),fun edge => edge.2 h⟩

theorem graph_indirect_iff (s t : Fin (n+4)) :
    Indirect (D.graph N) s t ↔
      D.relation (N.forkDecode s) (N.forkDecode t) ∧ s ≠ N.forkEncode .x := by
  have transfer := (D.graphIso N).indirect_iff (N.forkDecode s) (N.forkDecode t)
  simp only [graphIso,N.fork_right] at transfer
  rw [← transfer,D.indirect_iff]
  simp only [ne_eq,N.decode_eq_iff]

theorem graph_two_move (s t : Fin (n+4)) (good : s ≠ N.forkEncode .x) :
    Universal (D.graph N) t 2 s := by
  intro cop initial
  have good' : N.forkDecode s ≠ .x := by simpa only [ne_eq,N.decode_eq_iff] using good
  have initial' : N.forkDecode cop ≠ N.forkDecode s := by
    intro same
    exact initial (by simpa only [N.fork_right] using congrArg N.forkEncode same)
  have transfer := (D.graphIso N).winning (D.two_move (N.forkDecode s) (N.forkDecode t) good' _ initial')
  simpa only [graphIso,N.fork_right] using transfer

theorem graph_missingCount : missingCount (D.graph N) = 2*(n+4)-1 := by
  classical
  have singleton (a : Fin (n+4)) : card (fun t => t = a) = 1 := by
    rw [card_eq]
    simp [List.filter_eq,(List.nodup_finRange (n+4)).count]
  have row (s : Fin (n+4)) : card (fun t => s ≠ t ∧ ¬ D.graph N s t) =
      if s = N.forkEncode .c then 1 else 2 := by
    rw [card_congr (D.graph_missing_iff N s)]
    rw [card_congr (fun t => D.relation_rows _ _)]
    have shape (t : Fin (n+4)) :
        (N.forkDecode t = D.first (N.forkDecode s) ∨ N.forkDecode t = D.second (N.forkDecode s)) ↔
        (t = N.forkEncode (D.first (N.forkDecode s)) ∨ t = N.forkEncode (D.second (N.forkDecode s))) := by
      simp only [N.decode_eq_iff]
    rw [card_congr shape]
    by_cases isc : s = N.forkEncode .c
    · subst s
      simp only [N.fork_left,first,second,or_self,ite_true]
      exact singleton _
    · rw [if_neg isc]
      exact DenseTwoType.card_two _ _ (fun equal => D.neighbours_distinct _
        (fun eq => isc ((N.decode_eq_iff _ _).mp eq)) (N.fork_injective equal))
  rw [ConstructionCounts.missing_rows]
  simp only [row]
  have total := ConstructionCounts.one_or_two (List.finRange (n+4))
    (fun s => s ≠ N.forkEncode .c)
  have partition := VertexBound.filter_partition (List.finRange (n+4))
    (fun s => decide (s = N.forkEncode .c))
  have one : ((List.finRange (n+4)).filter fun s => decide (s = N.forkEncode .c)).length = 1 := by
    rw [← card_eq]; exact singleton _
  have swap (s : Fin (n+4)) : (if s = N.forkEncode .c then 1 else 2) =
      (if s ≠ N.forkEncode .c then 2 else 1) := by split <;> simp_all
  simp only [swap]
  rw [total]
  simp only [List.length_finRange] at *
  have complement : ((List.finRange (n+4)).filter fun s => decide (s ≠ N.forkEncode .c)).length = n+3 := by
    simp only [decide_not] at *
    omega
  omega

theorem graph_lossCount : lossCount (D.graph N) = 2 := by
  classical
  let cx := N.forkEncode .x
  let cy := N.forkEncode .y
  let cz := N.forkEncode .z
  have equivalent (s t : Fin (n+4)) :
      ((s ≠ t ∧ ¬ D.graph N s t) ∧ ¬ Guaranteed (D.graph N) s t) ↔
      (s = cx ∧ (t = cy ∨ t = cz)) := by
    have missing := D.graph_missing_iff N s t
    have indirect := D.graph_indirect_iff N s t
    change _ ↔ (s = N.forkEncode .x ∧ (t = N.forkEncode .y ∨ t = N.forkEncode .z))
    constructor
    · intro h
      have pair := missing.mp h.1
      have sx : s = N.forkEncode .x := by
        by_cases sx : s = N.forkEncode .x
        · exact sx
        · exact False.elim (h.2 ((indirect.mpr ⟨pair,sx⟩).2.2))
      refine ⟨sx,?_⟩
      subst s
      simp only [N.fork_left] at pair
      rw [D.relation_rows] at pair
      simpa only [first,second,N.decode_eq_iff] using pair
    · rintro ⟨sx,targets⟩
      have pair : D.relation (N.forkDecode s) (N.forkDecode t) := by
        rw [sx,N.fork_left,D.relation_rows]
        simpa only [first,second,N.decode_eq_iff] using targets
      refine ⟨missing.mpr pair,?_⟩
      intro guaranteed
      exact (indirect.mp ⟨(missing.mpr pair).1,(missing.mpr pair).2,guaranteed⟩).2 sx
  have nodup : [(cx,cy),(cx,cz)].Nodup := by
    have different : cy ≠ cz := fun same => by have := N.fork_injective same; cases this
    simp [different]
  have perm := (List.perm_ext_iff_of_nodup
    ((DenseZero.allPairs_nodup (n+4)).filter (fun p => decide
      ((p.1 ≠ p.2 ∧ ¬ D.graph N p.1 p.2) ∧ ¬ Guaranteed (D.graph N) p.1 p.2))) nodup).mpr
    (fun p => by
      simp only [List.mem_filter,GraphRelabeling.allPairs_mem,true_and,decide_eq_true_eq,
        List.mem_cons,List.not_mem_nil,or_false]
      rw [equivalent]
      grind)
  rw [lossCount_eq]
  exact perm.length_eq

theorem graph_score : score (D.graph N) = 2*(n+4)-3 := by
  have partition := score_add_lossCount (D.graph N)
  rw [D.graph_missingCount N,D.graph_lossCount N] at partition
  omega

theorem graph_arcCount (hn : 1 ≤ n) : arcCount (D.graph N) = (n+4)*(n+1)+1 := by
  have partition := arcCount_add_missingCount (D.graph N) (D.graph_loopless N)
  rw [D.graph_missingCount N] at partition
  have identity : (n+4)*(n+4-1) = (n+4)*(n+1)+2*(n+4) := by
    have inner : n+4-1 = (n+1)+2 := by omega
    rw [inner,Nat.mul_add,Nat.mul_comm (n+4) 2]
  omega

end ForkData

set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
def evenData {k : Nat} (hk : 6 ≤ k) : ForkData (DenseTwoType.Vertex k) where
  missing := DenseTwoType.missing
  next0 := DenseTwoType.first
  next1 := DenseTwoType.second
  loopless := DenseTwoType.missing_loopless
  rows := fun _ _ => Iff.rfl
  distinct := DenseTwoType.neighbours_distinct (by omega)
  unblocked := DenseTwoType.unblocked (by omega)
  a := .point ⟨0,by omega⟩
  b := .point ⟨3,by omega⟩
  d := .point ⟨1,by omega⟩
  e := .point ⟨4,by omega⟩
  attachments := by simp [Fin.ext_iff]
  cross := by simp [DenseTwoType.missing,DenseTwoType.first,DenseTwoType.second]
  branchOld := by
    intro s t pair
    have sh1 (i : Fin k) := DenseOddCore.shift_val_small i (d := 1) (by omega : 1 < k)
    have sh3 (i : Fin k) := DenseOddCore.shift_val_small i (d := 3) (by omega : 3 < k)
    have sh5 (i : Fin k) := DenseOddCore.shift_val_small i (d := 5) (by omega : 5 < k)
    constructor <;> intro ⟨block0,block1⟩
    all_goals cases s <;> cases t <;>
      simp_all [DenseTwoType.missing,DenseTwoType.first,DenseTwoType.second,
        Fin.ext_iff,sh1,sh3,sh5]
    all_goals clear sh1 sh3 sh5
    all_goals repeat' (first | split at pair | split at block0 | split at block1)
    all_goals try simp_all
    all_goals omega
  oldBranch := by
    intro cop t
    have sh1 (i : Fin k) := DenseOddCore.shift_val_small i (d := 1) (by omega : 1 < k)
    have sh3 (i : Fin k) := DenseOddCore.shift_val_small i (d := 3) (by omega : 3 < k)
    have sh5 (i : Fin k) := DenseOddCore.shift_val_small i (d := 5) (by omega : 5 < k)
    constructor <;> intro pair ⟨block0,block1⟩
    all_goals cases cop <;> cases t <;>
      simp_all [DenseTwoType.missing,DenseTwoType.first,DenseTwoType.second,
        Fin.ext_iff,sh1,sh3,sh5]
    all_goals clear sh1 sh3 sh5
    all_goals repeat' (first | split at pair | split at block0 | split at block1)
    all_goals try simp_all
    all_goals omega

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
def oddData {k : Nat} (hk : 6 ≤ k) : ForkData (DenseOddCore.Vertex k) where
  missing := DenseOddCore.missing hk
  next0 := DenseOddCore.first hk
  next1 := DenseOddCore.second hk
  loopless := DenseOddCore.missing_loopless hk
  rows := DenseOddCore.missing_iff hk
  distinct := DenseOddCore.neighbours_distinct hk
  unblocked := DenseOddCore.unblocked hk
  a := .point ⟨1,by omega⟩
  b := .point ⟨4,by omega⟩
  d := .point ⟨2,by omega⟩
  e := .point ⟨5,by omega⟩
  attachments := by simp [Fin.ext_iff]
  cross := by simp [DenseOddCore.missing]
  branchOld := by
    intro s t pair
    have sh1 (i : Fin k) := DenseOddCore.shift_val_small i (d := 1) (by omega : 1 < k)
    have sh3 (i : Fin k) := DenseOddCore.shift_val_small i (d := 3) (by omega : 3 < k)
    have sh5 (i : Fin k) := DenseOddCore.shift_val_small i (d := 5) (by omega : 5 < k)
    constructor <;> intro ⟨block0,block1⟩
    all_goals cases s <;> cases t <;>
      simp_all [DenseOddCore.missing,Fin.ext_iff,sh1,sh3,sh5]
    all_goals clear sh1 sh3 sh5
    all_goals repeat' (first | split at pair | split at block0 | split at block1)
    all_goals try simp_all
    all_goals omega
  oldBranch := by
    intro cop t
    have sh1 (i : Fin k) := DenseOddCore.shift_val_small i (d := 1) (by omega : 1 < k)
    have sh3 (i : Fin k) := DenseOddCore.shift_val_small i (d := 3) (by omega : 3 < k)
    have sh5 (i : Fin k) := DenseOddCore.shift_val_small i (d := 5) (by omega : 5 < k)
    constructor <;> intro pair ⟨block0,block1⟩
    all_goals cases cop with
      | point i =>
        by_cases modified : i.val = 0 ∨ i.val = 3
        all_goals cases t <;> simp_all [DenseOddCore.missing,DenseOddCore.first,
          DenseOddCore.second,modified,Fin.ext_iff,sh1,sh3,sh5]
        all_goals clear sh1 sh3 sh5
        all_goals repeat' (first | split at pair | split at block0 | split at block1)
        all_goals try simp_all
        all_goals omega
      | line i =>
        cases t <;> simp_all [DenseOddCore.missing,DenseOddCore.first,
          DenseOddCore.second,Fin.ext_iff,sh1,sh3,sh5]
        all_goals clear sh1 sh3 sh5
        all_goals repeat' (first | split at pair | split at block0 | split at block1)
        all_goals try simp_all
        all_goals omega
      | hub =>
        cases t <;> simp_all [DenseOddCore.missing,DenseOddCore.first,
          DenseOddCore.second,Fin.ext_iff,sh1,sh3,sh5]
        all_goals clear sh1 sh3 sh5
        all_goals repeat' (first | split at pair | split at block0 | split at block1)
        all_goals try simp_all
        all_goals omega


structure Construction (n : Nat) where
  edge : Graph (Fin n)
  loopless : Loopless edge
  missing_count : missingCount edge = 2*n-1
  score_count : score edge = 2*n-3
  badSource : Fin n
  two_move : ∀ s t, s ≠ badSource → Universal edge t 2 s

namespace ForkData
variable {V : Type} {n : Nat} (D : ForkData V) (N : Numbering V n)

def construction : Construction (n+4) where
  edge := D.graph N
  loopless := D.graph_loopless N
  missing_count := D.graph_missingCount N
  score_count := D.graph_score N
  badSource := N.forkEncode .x
  two_move := D.graph_two_move N

end ForkData

def evenNumbering (k : Nat) : Numbering (DenseTwoType.Vertex k) (2*k) where
  encode := DenseTwoType.encode
  decode := DenseTwoType.decode
  left_inv := DenseTwoType.decode_encode
  right_inv := DenseTwoType.encode_decode

def oddNumbering (k : Nat) : Numbering (DenseOddCore.Vertex k) (2*k+1) where
  encode := DenseOddCore.encode
  decode := DenseOddCore.decode
  left_inv := DenseOddCore.decode_encode
  right_inv := DenseOddCore.encode_decode

/-- Literal parity choice, preserving the manuscript's n≥16 domain. -/
def construction (n : Nat) (hn : 16 ≤ n) : Construction n := by
  by_cases even : n % 2 = 0
  · have order : 2*((n-4)/2)+4 = n := by omega
    exact order ▸ (evenData (k := (n-4)/2) (by omega)).construction (evenNumbering _)
  · have order : (2*((n-4)/2)+1)+4 = n := by omega
    exact order ▸ (oddData (k := (n-4)/2) (by omega)).construction (oddNumbering _)

def graph (n : Nat) (hn : 16 ≤ n) : Graph (Fin n) := (construction n hn).edge

theorem graph_loopless {n : Nat} (hn : 16 ≤ n) : Loopless (graph n hn) :=
  (construction n hn).loopless

theorem graph_missingCount {n : Nat} (hn : 16 ≤ n) :
    missingCount (graph n hn) = 2*n-1 := (construction n hn).missing_count

theorem graph_score {n : Nat} (hn : 16 ≤ n) : score (graph n hn) = 2*n-3 :=
  (construction n hn).score_count

theorem graph_two_move {n : Nat} (hn : 16 ≤ n) (s t : Fin n)
    (good : s ≠ (construction n hn).badSource) : Universal (graph n hn) t 2 s :=
  (construction n hn).two_move s t good

theorem graph_arcCount {n : Nat} (hn : 16 ≤ n) :
    arcCount (graph n hn) = n*(n-3)+1 := by
  have partition := arcCount_add_missingCount (graph n hn) (graph_loopless hn)
  rw [graph_missingCount hn] at partition
  have identity : n*(n-1) = n*(n-3)+2*n := by
    have inner : n-1 = (n-3)+2 := by omega
    rw [inner,Nat.mul_add,Nat.mul_comm n 2]
  omega

/-- The first positive dense offset is exactly attained at every n≥16. -/
theorem maximum {n : Nat} (hn : 16 ≤ n) :
    IsMaximum n (n*(n-3)+1) (2*n-3) := by
  constructor
  · intro E loopless arrows
    have bound := DenseStaircase.bound_at_offset E loopless (by omega : 3 ≤ n)
      (by omega : 1 ≤ 1) (by omega : 1 ≤ n) arrows
    simp only [DenseCounting.ceilHalf] at bound
    omega
  · exact ⟨graph n hn,graph_loopless hn,graph_arcCount hn,graph_score hn⟩

#print axioms graph_score
#print axioms graph_two_move
#print axioms maximum

end Delivery.DenseFirstStep
