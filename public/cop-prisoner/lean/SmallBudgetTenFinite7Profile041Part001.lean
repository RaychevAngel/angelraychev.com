import SmallBudgetTenFinite7Profile041Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile41_node130_cert : Bound 7 := { allowed := (rows 32 48 56 0 0 0 0), upper := (rows 25 74 55 63 55 55 119), lower := (rows 25 74 4 8 16 32 64), losses := [] }

theorem profile41_node130 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,72] 6 55 profile41_node130_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,72] 6 55 profile41_node130_cert).mp (by decide +kernel))

def profile41_node131_cert : Bound 7 := { allowed := (rows 32 24 56 0 0 0 0), upper := (rows 25 98 63 63 63 63 127), lower := (rows 25 98 4 8 16 32 64), losses := [] }

theorem profile41_node131 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,96] 6 63 profile41_node131_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24,96] 6 63 profile41_node131_cert).mp (by decide +kernel))

def profile41_node94_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile41_node94_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node94 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [24] 6 (by decide) (choices 2) [5,9,12,24,33,36,40,65,68,72,96] profile41_node94_route profile41_node94_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node95
  · exact profile41_node107
  · exact profile41_node108
  · exact profile41_node109
  · exact profile41_node110
  · exact profile41_node111
  · exact profile41_node112
  · exact profile41_node113
  · exact profile41_node118
  · exact profile41_node130
  · exact profile41_node131

def profile41_node135_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 67 7 28 24 56 40 104), lower := (rows 67 7 28 24 16 32 64), losses := [{ target := 4, region := (rows 7 6 4 8 0 44 76), good := (rows 67 103 111 104 0 32 64) }] }

theorem profile41_node135 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,16] 6 40 profile41_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,16] 6 40 profile41_node135_cert).mp (by decide +kernel))

def profile41_node137_cert : CutBound 7 := { lost := (rows 8 8 0 0 0 0 0), upper := (rows 67 7 28 40 24 48 112), lower := (rows 67 7 28 40 24 32 64), losses := [{ target := 3, region := (rows 7 6 4 0 16 52 84), good := (rows 67 103 119 32 112 32 64) }] }

theorem profile41_node137 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32,8] 6 48 profile41_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32,8] 6 48 profile41_node137_cert).mp (by decide +kernel))

def profile41_node138_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 67 7 28 40 48 56 88), lower := (rows 67 7 28 40 48 32 64), losses := [{ target := 5, region := (rows 7 6 4 8 16 0 68), good := (rows 67 71 95 8 16 0 64) }] }

theorem profile41_node138 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32,32] 6 24 profile41_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32,32] 6 24 profile41_node138_cert).mp (by decide +kernel))

def profile41_node136_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node136_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node136 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24,32] 6 (by decide) (choices 1) [8,32] profile41_node136_route profile41_node136_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node137
  · exact profile41_node138

def profile41_node134_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node134_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node134 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5,24] 6 (by decide) (choices 1) [16,32] profile41_node134_route profile41_node134_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node135
  · exact profile41_node136

def profile41_node133_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node133_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node133 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,5] 6 (by decide) (choices 2) [24] profile41_node133_route profile41_node133_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile41_node134

def profile41_node140_cert : Bound 7 := { allowed := (rows 56 48 32 0 0 0 0), upper := (rows 67 11 28 60 52 52 116), lower := (rows 67 11 28 8 16 32 64), losses := [] }

theorem profile41_node140 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9,24] 6 52 profile41_node140_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9,24] 6 52 profile41_node140_cert).mp (by decide +kernel))

def profile41_node141_cert : Bound 7 := { allowed := (rows 56 48 8 0 0 0 0), upper := (rows 67 11 52 60 60 60 124), lower := (rows 67 11 52 8 16 32 64), losses := [] }

theorem profile41_node141 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9,48] 6 60 profile41_node141_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9,48] 6 60 profile41_node141_cert).mp (by decide +kernel))

def profile41_node139_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node139_route : Route 7 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node139 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,9] 6 (by decide) (choices 2) [24,48] profile41_node139_route profile41_node139_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node140
  · exact profile41_node141

def profile41_node143_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 67 14 13 56 48 48 112), lower := (rows 67 14 13 8 16 32 64), losses := [{ target := 3, region := (rows 3 2 4 0 127 127 127), good := (rows 115 119 117 112 112 112 112) }] }

theorem profile41_node143 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,9] 6 48 profile41_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,9] 6 48 profile41_node143_cert).mp (by decide +kernel))

def profile41_node145_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 67 14 21 24 56 40 104), lower := (rows 67 14 21 24 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 42 74), good := (rows 99 111 5 104 0 32 64) }] }

theorem profile41_node145 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,16] 6 40 profile41_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,16] 6 40 profile41_node145_cert).mp (by decide +kernel))

def profile41_node147_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 67 14 21 40 24 48 112), lower := (rows 67 14 21 40 24 32 64), losses := [{ target := 3, region := (rows 3 2 4 0 16 52 84), good := (rows 67 103 117 32 112 32 64) }] }

theorem profile41_node147 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32,8] 6 48 profile41_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32,8] 6 48 profile41_node147_cert).mp (by decide +kernel))

def profile41_node148_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 67 14 21 40 48 56 88), lower := (rows 67 14 21 40 48 32 64), losses := [{ target := 4, region := (rows 1 6 4 56 0 32 64), good := (rows 67 14 15 40 40 40 64) }] }

theorem profile41_node148 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32,32] 6 24 profile41_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32,32] 6 24 profile41_node148_cert).mp (by decide +kernel))

def profile41_node146_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node146_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node146 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17,32] 6 (by decide) (choices 1) [8,32] profile41_node146_route profile41_node146_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node147
  · exact profile41_node148

def profile41_node144_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node144_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node144 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,17] 6 (by decide) (choices 1) [16,32] profile41_node144_route profile41_node144_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node145
  · exact profile41_node146

def profile41_node149_cert : Bound 7 := { allowed := (rows 56 48 32 0 0 0 0), upper := (rows 67 14 28 57 49 49 113), lower := (rows 67 14 28 8 16 32 64), losses := [] }

theorem profile41_node149 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,24] 6 49 profile41_node149_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,24] 6 49 profile41_node149_cert).mp (by decide +kernel))

def profile41_node150_cert : Bound 7 := { allowed := (rows 56 48 8 0 0 0 0), upper := (rows 67 14 52 57 57 57 121), lower := (rows 67 14 52 8 16 32 64), losses := [] }

theorem profile41_node150 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,48] 6 57 profile41_node150_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12,48] 6 57 profile41_node150_cert).mp (by decide +kernel))

def profile41_node142_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node142_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node142 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,12] 6 (by decide) (choices 2) [9,17,24,48] profile41_node142_route profile41_node142_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node143
  · exact profile41_node144
  · exact profile41_node149
  · exact profile41_node150

def profile41_node152_cert : Bound 7 := { allowed := (rows 56 32 48 0 0 0 0), upper := (rows 67 26 13 60 52 52 116), lower := (rows 67 26 13 8 16 32 64), losses := [] }

theorem profile41_node152 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,9] 6 52 profile41_node152_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,9] 6 52 profile41_node152_cert).mp (by decide +kernel))

def profile41_node153_cert : Bound 7 := { allowed := (rows 56 32 32 0 0 0 0), upper := (rows 67 26 28 45 53 37 101), lower := (rows 67 26 28 8 16 32 64), losses := [] }

theorem profile41_node153 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,24] 6 37 profile41_node153_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,24] 6 37 profile41_node153_cert).mp (by decide +kernel))

def profile41_node154_cert : Bound 7 := { allowed := (rows 56 32 24 0 0 0 0), upper := (rows 67 26 37 60 60 60 124), lower := (rows 67 26 37 8 16 32 64), losses := [] }

theorem profile41_node154 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,33] 6 60 profile41_node154_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,33] 6 60 profile41_node154_cert).mp (by decide +kernel))

def profile41_node155_cert : Bound 7 := { allowed := (rows 56 32 16 0 0 0 0), upper := (rows 67 26 44 61 53 53 117), lower := (rows 67 26 44 8 16 32 64), losses := [] }

theorem profile41_node155 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,40] 6 53 profile41_node155_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24,40] 6 53 profile41_node155_cert).mp (by decide +kernel))

def profile41_node151_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node151_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node151 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66,24] 6 (by decide) (choices 2) [9,24,33,40] profile41_node151_route profile41_node151_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node152
  · exact profile41_node153
  · exact profile41_node154
  · exact profile41_node155

def profile41_node132_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 68 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node132_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 33 => (9,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 36 => (12,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node132 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [66] 6 (by decide) (choices 2) [5,9,12,24] profile41_node132_route profile41_node132_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node133
  · exact profile41_node139
  · exact profile41_node142
  · exact profile41_node151

def profile41_node158_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 73 7 14 56 48 48 112), lower := (rows 73 7 14 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 32 64), good := (rows 79 7 14 8 0 32 64) }] }

theorem profile41_node158 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,10] 6 48 profile41_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,10] 6 48 profile41_node158_cert).mp (by decide +kernel))

def profile41_node160_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 73 7 22 24 56 40 104), lower := (rows 73 7 22 24 16 32 64), losses := [{ target := 4, region := (rows 9 2 4 8 0 41 73), good := (rows 105 103 6 105 0 32 64) }] }

theorem profile41_node160 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,16] 6 40 profile41_node160_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,16] 6 40 profile41_node160_cert).mp (by decide +kernel))

def profile41_node162_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 73 7 22 40 24 48 112), lower := (rows 73 7 22 40 24 32 64), losses := [{ target := 5, region := (rows 1 3 7 8 25 0 64), good := (rows 95 23 22 24 24 0 64) }] }

theorem profile41_node162 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32,8] 6 48 profile41_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32,8] 6 48 profile41_node162_cert).mp (by decide +kernel))

def profile41_node163_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 73 7 22 40 48 56 88), lower := (rows 73 7 22 40 48 32 64), losses := [{ target := 3, region := (rows 1 3 5 0 56 32 64), good := (rows 87 7 22 48 48 48 64) }] }

theorem profile41_node163 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32,32] 6 24 profile41_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32,32] 6 24 profile41_node163_cert).mp (by decide +kernel))

def profile41_node161_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node161_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node161 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18,32] 6 (by decide) (choices 1) [8,32] profile41_node161_route profile41_node161_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node162
  · exact profile41_node163

def profile41_node159_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node159_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node159 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,18] 6 (by decide) (choices 1) [16,32] profile41_node159_route profile41_node159_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node160
  · exact profile41_node161

def profile41_node164_cert : Bound 7 := { allowed := (rows 48 56 32 0 0 0 0), upper := (rows 73 7 28 58 50 50 114), lower := (rows 73 7 28 8 16 32 64), losses := [] }

theorem profile41_node164 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,24] 6 50 profile41_node164_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,24] 6 50 profile41_node164_cert).mp (by decide +kernel))

def profile41_node165_cert : Bound 7 := { allowed := (rows 48 56 8 0 0 0 0), upper := (rows 73 7 52 58 58 58 122), lower := (rows 73 7 52 8 16 32 64), losses := [] }

theorem profile41_node165 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,48] 6 58 profile41_node165_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5,48] 6 58 profile41_node165_cert).mp (by decide +kernel))

def profile41_node157_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node157_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node157 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,5] 6 (by decide) (choices 2) [10,18,24,48] profile41_node157_route profile41_node157_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node158
  · exact profile41_node159
  · exact profile41_node164
  · exact profile41_node165

def profile41_node166_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 73 11 54 62 54 54 118), lower := (rows 73 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 18 34 66), good := (rows 65 119 4 0 16 32 64) }] }

theorem profile41_node166 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,9] 6 54 profile41_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,9] 6 54 profile41_node166_cert).mp (by decide +kernel))

def profile41_node168_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 73 14 7 56 48 48 112), lower := (rows 73 14 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 32 64), good := (rows 79 14 7 8 0 32 64) }] }

theorem profile41_node168 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,3] 6 48 profile41_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,3] 6 48 profile41_node168_cert).mp (by decide +kernel))

def profile41_node169_cert : Bound 7 := { allowed := (rows 48 48 40 0 0 0 0), upper := (rows 73 14 21 58 50 50 114), lower := (rows 73 14 21 8 16 32 64), losses := [] }

theorem profile41_node169 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,17] 6 50 profile41_node169_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,17] 6 50 profile41_node169_cert).mp (by decide +kernel))

def profile41_node170_cert : Bound 7 := { allowed := (rows 48 48 40 0 0 0 0), upper := (rows 73 14 22 57 49 49 113), lower := (rows 73 14 22 8 16 32 64), losses := [] }

theorem profile41_node170 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,18] 6 49 profile41_node170_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,18] 6 49 profile41_node170_cert).mp (by decide +kernel))

def profile41_node171_cert : Bound 7 := { allowed := (rows 48 48 8 0 0 0 0), upper := (rows 73 14 52 59 51 51 115), lower := (rows 73 14 52 8 16 32 64), losses := [] }

theorem profile41_node171 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,48] 6 51 profile41_node171_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12,48] 6 51 profile41_node171_cert).mp (by decide +kernel))

def profile41_node167_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node167_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node167 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,12] 6 (by decide) (choices 2) [3,17,18,48] profile41_node167_route profile41_node167_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile41_node168
  · exact profile41_node169
  · exact profile41_node170
  · exact profile41_node171

def profile41_node173_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 73 19 14 60 52 52 116), lower := (rows 73 19 14 8 16 32 64), losses := [] }

theorem profile41_node173 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,10] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,10] 6 52 profile41_node173_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,10] 6 52 profile41_node173_cert).mp (by decide +kernel))

def profile41_node174_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 73 19 22 44 60 44 108), lower := (rows 73 19 22 8 16 32 64), losses := [] }

theorem profile41_node174 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,18] 6 44 profile41_node174_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,18] 6 44 profile41_node174_cert).mp (by decide +kernel))

def profile41_node175_cert : Bound 7 := { allowed := (rows 48 40 32 0 0 0 0), upper := (rows 73 19 28 46 54 38 102), lower := (rows 73 19 28 8 16 32 64), losses := [] }

theorem profile41_node175 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,24] 6 38 profile41_node175_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,24] 6 38 profile41_node175_cert).mp (by decide +kernel))

def profile41_node176_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 73 19 38 60 60 60 124), lower := (rows 73 19 38 8 16 32 64), losses := [] }

theorem profile41_node176 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,34] 6 60 profile41_node176_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,34] 6 60 profile41_node176_cert).mp (by decide +kernel))

def profile41_node177_cert : Bound 7 := { allowed := (rows 48 40 16 0 0 0 0), upper := (rows 73 19 44 62 54 54 118), lower := (rows 73 19 44 8 16 32 64), losses := [] }

theorem profile41_node177 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,40] 6 54 profile41_node177_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,40] 6 54 profile41_node177_cert).mp (by decide +kernel))

def profile41_node178_cert : Bound 7 := { allowed := (rows 48 40 8 0 0 0 0), upper := (rows 73 19 52 46 62 46 110), lower := (rows 73 19 52 8 16 32 64), losses := [] }

theorem profile41_node178 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,48] 6 46 profile41_node178_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17,48] 6 46 profile41_node178_cert).mp (by decide +kernel))

def profile41_node172_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node172_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node172 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,17] 6 (by decide) (choices 2) [10,18,24,34,40,48] profile41_node172_route profile41_node172_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node173
  · exact profile41_node174
  · exact profile41_node175
  · exact profile41_node176
  · exact profile41_node177
  · exact profile41_node178

def profile41_node181_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 73 22 7 24 56 40 104), lower := (rows 73 22 7 24 16 32 64), losses := [{ target := 4, region := (rows 9 2 4 8 0 41 73), good := (rows 105 6 103 105 0 32 64) }] }

theorem profile41_node181 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,16] 6 40 profile41_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,16] 6 40 profile41_node181_cert).mp (by decide +kernel))

def profile41_node183_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 73 22 7 40 24 48 112), lower := (rows 73 22 7 40 24 32 64), losses := [{ target := 5, region := (rows 1 7 5 8 25 0 64), good := (rows 95 22 23 24 24 0 64) }] }

theorem profile41_node183 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32,8] 6 48 profile41_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32,8] 6 48 profile41_node183_cert).mp (by decide +kernel))

def profile41_node184_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 73 22 7 40 48 56 88), lower := (rows 73 22 7 40 48 32 64), losses := [{ target := 3, region := (rows 1 3 5 0 56 32 64), good := (rows 87 22 7 48 48 48 64) }] }

theorem profile41_node184 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32,32] 6 24 profile41_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32,32] 6 24 profile41_node184_cert).mp (by decide +kernel))

def profile41_node182_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node182_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node182 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3,32] 6 (by decide) (choices 1) [8,32] profile41_node182_route profile41_node182_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node183
  · exact profile41_node184

def profile41_node180_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile41_node180_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node180 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,3] 6 (by decide) (choices 1) [16,32] profile41_node180_route profile41_node180_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile41_node181
  · exact profile41_node182

def profile41_node185_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 73 22 13 58 50 50 114), lower := (rows 73 22 13 8 16 32 64), losses := [] }

theorem profile41_node185 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,9] 6 50 profile41_node185_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,9] 6 50 profile41_node185_cert).mp (by decide +kernel))

def profile41_node186_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 73 22 14 57 49 49 113), lower := (rows 73 22 14 8 16 32 64), losses := [] }

theorem profile41_node186 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,10] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,10] 6 49 profile41_node186_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,10] 6 49 profile41_node186_cert).mp (by decide +kernel))

def profile41_node187_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 73 22 21 42 58 42 106), lower := (rows 73 22 21 8 16 32 64), losses := [] }

theorem profile41_node187 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,17] 6 42 profile41_node187_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,17] 6 42 profile41_node187_cert).mp (by decide +kernel))

def profile41_node188_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 73 22 22 41 57 41 105), lower := (rows 73 22 22 8 16 32 64), losses := [] }

theorem profile41_node188 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,18] 6 41 profile41_node188_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,18] 6 41 profile41_node188_cert).mp (by decide +kernel))

def profile41_node189_cert : Bound 7 := { allowed := (rows 48 40 32 0 0 0 0), upper := (rows 73 22 28 43 51 35 99), lower := (rows 73 22 28 8 16 32 64), losses := [] }

theorem profile41_node189 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,24] 6 35 profile41_node189_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,24] 6 35 profile41_node189_cert).mp (by decide +kernel))

def profile41_node190_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 73 22 37 58 58 58 122), lower := (rows 73 22 37 8 16 32 64), losses := [] }

theorem profile41_node190 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,33] 6 58 profile41_node190_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,33] 6 58 profile41_node190_cert).mp (by decide +kernel))

def profile41_node191_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 73 22 38 57 57 57 121), lower := (rows 73 22 38 8 16 32 64), losses := [] }

theorem profile41_node191 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,34] 6 57 profile41_node191_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,34] 6 57 profile41_node191_cert).mp (by decide +kernel))

def profile41_node192_cert : Bound 7 := { allowed := (rows 48 40 16 0 0 0 0), upper := (rows 73 22 44 59 51 51 115), lower := (rows 73 22 44 8 16 32 64), losses := [] }

theorem profile41_node192 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,40] 6 51 profile41_node192_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,40] 6 51 profile41_node192_cert).mp (by decide +kernel))

def profile41_node193_cert : Bound 7 := { allowed := (rows 48 40 8 0 0 0 0), upper := (rows 73 22 52 43 59 43 107), lower := (rows 73 22 52 8 16 32 64), losses := [] }

theorem profile41_node193 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,48] 6 43 profile41_node193_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20,48] 6 43 profile41_node193_cert).mp (by decide +kernel))

def profile41_node179_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node179_route : Route 7 := (fun mask => (mask,id))

theorem profile41_node179 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,20] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile41_node179_route profile41_node179_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node180
  · exact profile41_node185
  · exact profile41_node186
  · exact profile41_node187
  · exact profile41_node188
  · exact profile41_node189
  · exact profile41_node190
  · exact profile41_node191
  · exact profile41_node192
  · exact profile41_node193

def profile41_node194_cert : Bound 7 := { allowed := (rows 48 32 56 0 0 0 0), upper := (rows 73 26 55 63 55 55 119), lower := (rows 73 26 4 8 16 32 64), losses := [] }

theorem profile41_node194 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,24] 6 55 profile41_node194_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,24] 6 55 profile41_node194_cert).mp (by decide +kernel))

def profile41_node195_cert : Bound 7 := { allowed := (rows 48 8 56 0 0 0 0), upper := (rows 73 50 63 63 63 63 127), lower := (rows 73 50 4 8 16 32 64), losses := [] }

theorem profile41_node195 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,48] 6 63 profile41_node195_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72,48] 6 63 profile41_node195_cert).mp (by decide +kernel))

def profile41_node156_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 68 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile41_node156_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile41_node156 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [72] 6 (by decide) (choices 2) [5,9,12,17,20,24,48] profile41_node156_route profile41_node156_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile41_node157
  · exact profile41_node166
  · exact profile41_node167
  · exact profile41_node172
  · exact profile41_node179
  · exact profile41_node194
  · exact profile41_node195

def profile41_node0_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile41_node0_route : Route 7 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 34 => (10,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 20 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | _ => i)) | 36 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | 3 => 5 | 5 => 3 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 96 => (72,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile41_node0 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [] 6 (by decide) (choices 2) [6,10,24,66,72] profile41_node0_route profile41_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile41_node1
  · exact profile41_node38
  · exact profile41_node94
  · exact profile41_node132
  · exact profile41_node156

theorem profile41 : Upper (D (n:=7) [33,33,33,18,18,18,17]) (R (n:=7) [33,33,33,18,18,18,17]) [] 6 := profile41_node0


#print axioms profile41
end Delivery.SmallBudgetTenFinite7
