import SmallBudgetTenFinite7Profile040Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile40_node131_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 67 11 28 57 49 49 113), lower := (rows 67 11 28 8 16 32 64), losses := [{ target := 3, region := (rows 3 2 4 0 19 35 67), good := (rows 115 115 20 0 16 32 64) }] }

theorem profile40_node131 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,24] 6 49 profile40_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,24] 6 49 profile40_node131_cert).mp (by decide +kernel))

def profile40_node133_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 67 11 52 9 56 56 120), lower := (rows 67 11 52 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 26 42 74), good := (rows 118 126 52 124 16 32 64) }] }

theorem profile40_node133 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48,1] 6 56 profile40_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48,1] 6 56 profile40_node133_cert).mp (by decide +kernel))

def profile40_node134_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 67 11 52 24 57 41 105), lower := (rows 67 11 52 24 16 32 64), losses := [{ target := 4, region := (rows 11 10 4 8 0 42 74), good := (rows 99 107 36 107 0 32 64) }] }

theorem profile40_node134 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48,16] 6 41 profile40_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48,16] 6 41 profile40_node134_cert).mp (by decide +kernel))

def profile40_node132_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node132_route : Route 7 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node132 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,48] 6 (by decide) (choices 1) [1,16] profile40_node132_route profile40_node132_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node133
  · exact profile40_node134

def profile40_node124_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node124_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node124 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9] 6 (by decide) (choices 2) [9,17,24,48] profile40_node124_route profile40_node124_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile40_node125
  · exact profile40_node126
  · exact profile40_node131
  · exact profile40_node132

def profile40_node136_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 67 26 13 57 49 49 113), lower := (rows 67 26 13 8 16 32 64), losses := [{ target := 3, region := (rows 3 2 4 0 23 39 71), good := (rows 115 115 117 0 16 32 64) }] }

theorem profile40_node136 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,9] 6 49 profile40_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,9] 6 49 profile40_node136_cert).mp (by decide +kernel))

def profile40_node137_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 67 26 28 41 49 33 97), lower := (rows 67 26 28 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 64), good := (rows 70 30 30 8 16 32 64) }] }

theorem profile40_node137 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,24] 6 33 profile40_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,24] 6 33 profile40_node137_cert).mp (by decide +kernel))

def profile40_node139_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 67 26 37 9 56 56 120), lower := (rows 67 26 37 9 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 26 42 74), good := (rows 114 122 36 122 16 32 64) }] }

theorem profile40_node139 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,1] 6 56 profile40_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,1] 6 56 profile40_node139_cert).mp (by decide +kernel))

def profile40_node140_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 67 26 37 24 57 41 105), lower := (rows 67 26 37 24 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 64), good := (rows 74 26 36 26 26 32 64) }] }

theorem profile40_node140 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,16] 6 41 profile40_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,16] 6 41 profile40_node140_cert).mp (by decide +kernel))

def profile40_node141_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 67 26 37 40 25 57 89), lower := (rows 67 26 37 40 16 32 64), losses := [{ target := 5, region := (rows 11 10 4 8 26 0 74), good := (rows 83 91 5 91 16 0 64) }] }

theorem profile40_node141 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,32] 6 25 profile40_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33,32] 6 25 profile40_node141_cert).mp (by decide +kernel))

def profile40_node138_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node138_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node138 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,33] 6 (by decide) (choices 1) [1,16,32] profile40_node138_route profile40_node138_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node139
  · exact profile40_node140
  · exact profile40_node141

def profile40_node142_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 67 26 44 57 49 49 113), lower := (rows 67 26 44 8 16 32 64), losses := [{ target := 3, region := (rows 3 2 4 0 19 35 67), good := (rows 115 115 36 0 16 32 64) }] }

theorem profile40_node142 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,40] 6 49 profile40_node142_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24,40] 6 49 profile40_node142_cert).mp (by decide +kernel))

def profile40_node135_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node135_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile40_node135 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,24] 6 (by decide) (choices 2) [9,24,33,40] profile40_node135_route profile40_node135_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile40_node136
  · exact profile40_node137
  · exact profile40_node138
  · exact profile40_node142

def profile40_node123_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 65 => 6 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node123_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 33 => (9,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile40_node123 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66] 6 (by decide) (choices 2) [9,24] profile40_node123_route profile40_node123_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node124
  · exact profile40_node135

def profile40_node144_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 73 11 55 59 51 51 115), lower := (rows 73 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 18 34 66), good := (rows 65 119 4 0 16 32 64) }] }

theorem profile40_node144 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,9] 6 51 profile40_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,9] 6 51 profile40_node144_cert).mp (by decide +kernel))

def profile40_node146_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 73 19 7 56 56 56 120), lower := (rows 73 19 7 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 64), good := (rows 65 23 7 0 16 32 64) }] }

theorem profile40_node146 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,3] 6 56 profile40_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,3] 6 56 profile40_node146_cert).mp (by decide +kernel))

def profile40_node147_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 73 19 13 58 50 50 114), lower := (rows 73 19 13 8 16 32 64), losses := [] }

theorem profile40_node147 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,9] 6 50 profile40_node147_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,9] 6 50 profile40_node147_cert).mp (by decide +kernel))

def profile40_node148_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 73 19 14 57 49 49 113), lower := (rows 73 19 14 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 118 0 16 32 64) }] }

theorem profile40_node148 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,10] 6 49 profile40_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,10] 6 49 profile40_node148_cert).mp (by decide +kernel))

def profile40_node149_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 73 19 21 42 58 42 106), lower := (rows 73 19 21 8 16 32 64), losses := [] }

theorem profile40_node149 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,17] 6 42 profile40_node149_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,17] 6 42 profile40_node149_cert).mp (by decide +kernel))

def profile40_node150_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 73 19 22 41 57 41 105), lower := (rows 73 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 64), good := (rows 72 22 22 8 16 32 64) }] }

theorem profile40_node150 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,18] 6 41 profile40_node150_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,18] 6 41 profile40_node150_cert).mp (by decide +kernel))

def profile40_node151_cert : Bound 7 := { allowed := (rows 48 40 33 0 0 0 0), upper := (rows 73 19 28 43 51 35 99), lower := (rows 73 19 28 8 16 32 64), losses := [] }

theorem profile40_node151 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,24] 6 35 profile40_node151_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,24] 6 35 profile40_node151_cert).mp (by decide +kernel))

def profile40_node152_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 73 19 37 58 58 58 122), lower := (rows 73 19 37 8 16 32 64), losses := [] }

theorem profile40_node152 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,33] 6 58 profile40_node152_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,33] 6 58 profile40_node152_cert).mp (by decide +kernel))

def profile40_node154_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 73 19 38 9 56 56 120), lower := (rows 73 19 38 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 25 41 73), good := (rows 120 118 38 120 16 32 64) }] }

theorem profile40_node154 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,1] 6 56 profile40_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,1] 6 56 profile40_node154_cert).mp (by decide +kernel))

def profile40_node155_cert : CutBound 7 := { lost := (rows 16 0 16 0 0 0 0), upper := (rows 73 19 38 24 57 41 105), lower := (rows 73 19 38 24 16 32 64), losses := [{ target := 4, region := (rows 9 2 6 8 0 41 73), good := (rows 105 103 38 105 0 32 64) }] }

theorem profile40_node155 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,16] 6 41 profile40_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,16] 6 41 profile40_node155_cert).mp (by decide +kernel))

def profile40_node156_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 73 19 38 40 25 57 89), lower := (rows 73 19 38 40 16 32 64), losses := [{ target := 5, region := (rows 9 11 4 8 25 0 73), good := (rows 91 83 6 91 16 0 64) }] }

theorem profile40_node156 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,32] 6 25 profile40_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34,32] 6 25 profile40_node156_cert).mp (by decide +kernel))

def profile40_node153_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node153_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node153 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,34] 6 (by decide) (choices 1) [1,16,32] profile40_node153_route profile40_node153_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node154
  · exact profile40_node155
  · exact profile40_node156

def profile40_node157_cert : Bound 7 := { allowed := (rows 48 40 17 0 0 0 0), upper := (rows 73 19 44 59 51 51 115), lower := (rows 73 19 44 8 16 32 64), losses := [] }

theorem profile40_node157 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,40] 6 51 profile40_node157_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,40] 6 51 profile40_node157_cert).mp (by decide +kernel))

def profile40_node158_cert : Bound 7 := { allowed := (rows 48 40 9 0 0 0 0), upper := (rows 73 19 52 43 59 43 107), lower := (rows 73 19 52 8 16 32 64), losses := [] }

theorem profile40_node158 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,48] 6 43 profile40_node158_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17,48] 6 43 profile40_node158_cert).mp (by decide +kernel))

def profile40_node145_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node145_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node145 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,17] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile40_node145_route profile40_node145_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node146
  · exact profile40_node147
  · exact profile40_node148
  · exact profile40_node149
  · exact profile40_node150
  · exact profile40_node151
  · exact profile40_node152
  · exact profile40_node153
  · exact profile40_node157
  · exact profile40_node158

def profile40_node161_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 73 26 7 9 48 48 112), lower := (rows 73 26 7 9 16 32 64), losses := [{ target := 0, region := (rows 0 11 4 8 127 127 127), good := (rows 122 122 118 122 112 112 112) }] }

theorem profile40_node161 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,1] 6 48 profile40_node161_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,1] 6 48 profile40_node161_cert).mp (by decide +kernel))

def profile40_node162_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 73 26 7 24 49 33 97), lower := (rows 73 26 7 24 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 64), good := (rows 74 26 14 26 26 32 64) }] }

theorem profile40_node162 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,16] 6 33 profile40_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,16] 6 33 profile40_node162_cert).mp (by decide +kernel))

def profile40_node164_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 73 26 7 40 17 48 112), lower := (rows 73 26 7 40 17 32 64), losses := [{ target := 0, region := (rows 0 18 4 62 16 50 82), good := (rows 72 122 110 40 122 40 64) }] }

theorem profile40_node164 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32,1] 6 48 profile40_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32,1] 6 48 profile40_node164_cert).mp (by decide +kernel))

def profile40_node165_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 73 26 7 40 48 49 81), lower := (rows 73 26 7 40 48 32 64), losses := [{ target := 0, region := (rows 0 59 4 56 56 32 64), good := (rows 90 26 6 58 58 58 64) }] }

theorem profile40_node165 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32,32] 6 17 profile40_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32,32] 6 17 profile40_node165_cert).mp (by decide +kernel))

def profile40_node163_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0

def profile40_node163_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node163 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3,32] 6 (by decide) (choices 1) [1,32] profile40_node163_route profile40_node163_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node164
  · exact profile40_node165

def profile40_node160_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node160_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node160 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,3] 6 (by decide) (choices 1) [1,16,32] profile40_node160_route profile40_node160_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node161
  · exact profile40_node162
  · exact profile40_node163

def profile40_node166_cert : Bound 7 := { allowed := (rows 48 33 40 0 0 0 0), upper := (rows 73 26 21 43 51 35 99), lower := (rows 73 26 21 8 16 32 64), losses := [] }

theorem profile40_node166 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,17] 6 35 profile40_node166_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,17] 6 35 profile40_node166_cert).mp (by decide +kernel))

def profile40_node167_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 73 26 22 41 49 33 97), lower := (rows 73 26 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 64), good := (rows 72 30 22 8 16 32 64) }] }

theorem profile40_node167 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,18] 6 33 profile40_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,18] 6 33 profile40_node167_cert).mp (by decide +kernel))

def profile40_node168_cert : Bound 7 := { allowed := (rows 48 33 24 0 0 0 0), upper := (rows 73 26 37 59 51 51 115), lower := (rows 73 26 37 8 16 32 64), losses := [] }

theorem profile40_node168 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,33] 6 51 profile40_node168_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,33] 6 51 profile40_node168_cert).mp (by decide +kernel))

def profile40_node170_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 73 26 38 9 49 49 113), lower := (rows 73 26 38 9 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 25 41 73), good := (rows 113 118 38 113 16 32 64) }] }

theorem profile40_node170 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,1] 6 49 profile40_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,1] 6 49 profile40_node170_cert).mp (by decide +kernel))

def profile40_node171_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 73 26 38 24 49 33 97), lower := (rows 73 26 38 24 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 64), good := (rows 74 26 46 26 26 32 64) }] }

theorem profile40_node171 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,16] 6 33 profile40_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,16] 6 33 profile40_node171_cert).mp (by decide +kernel))

def profile40_node172_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 73 26 38 40 17 49 81), lower := (rows 73 26 38 40 16 32 64), losses := [{ target := 5, region := (rows 11 11 4 8 31 0 79), good := (rows 91 91 87 91 16 0 64) }] }

theorem profile40_node172 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,32] 6 17 profile40_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34,32] 6 17 profile40_node172_cert).mp (by decide +kernel))

def profile40_node169_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node169_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node169 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,34] 6 (by decide) (choices 1) [1,16,32] profile40_node169_route profile40_node169_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node170
  · exact profile40_node171
  · exact profile40_node172

def profile40_node173_cert : Bound 7 := { allowed := (rows 48 33 9 0 0 0 0), upper := (rows 73 26 52 43 51 35 99), lower := (rows 73 26 52 8 16 32 64), losses := [] }

theorem profile40_node173 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,48] 6 35 profile40_node173_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24,48] 6 35 profile40_node173_cert).mp (by decide +kernel))

def profile40_node159_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node159_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node159 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,24] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile40_node159_route profile40_node159_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node160
  · exact profile40_node166
  · exact profile40_node167
  · exact profile40_node168
  · exact profile40_node169
  · exact profile40_node173

def profile40_node176_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 73 50 7 9 56 56 120), lower := (rows 73 50 7 9 16 32 64), losses := [{ target := 0, region := (rows 0 15 4 8 25 41 73), good := (rows 122 50 118 122 16 32 64) }] }

theorem profile40_node176 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3,1] 6 56 profile40_node176_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3,1] 6 56 profile40_node176_cert).mp (by decide +kernel))

def profile40_node177_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 73 50 7 24 57 41 105), lower := (rows 73 50 7 24 16 32 64), losses := [{ target := 4, region := (rows 9 2 4 8 0 41 73), good := (rows 105 34 103 105 0 32 64) }] }

theorem profile40_node177 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3,16] 6 41 profile40_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3,16] 6 41 profile40_node177_cert).mp (by decide +kernel))

def profile40_node175_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node175_route : Route 7 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node175 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,3] 6 (by decide) (choices 1) [1,16] profile40_node175_route profile40_node175_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node176
  · exact profile40_node177

def profile40_node178_cert : Bound 7 := { allowed := (rows 48 9 48 0 0 0 0), upper := (rows 73 50 13 59 51 51 115), lower := (rows 73 50 13 8 16 32 64), losses := [] }

theorem profile40_node178 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,9] 6 51 profile40_node178_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,9] 6 51 profile40_node178_cert).mp (by decide +kernel))

def profile40_node179_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 73 50 14 57 49 49 113), lower := (rows 73 50 14 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 50 6 0 16 32 64) }] }

theorem profile40_node179 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,10] 6 49 profile40_node179_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,10] 6 49 profile40_node179_cert).mp (by decide +kernel))

def profile40_node180_cert : Bound 7 := { allowed := (rows 48 9 40 0 0 0 0), upper := (rows 73 50 21 43 59 43 107), lower := (rows 73 50 21 8 16 32 64), losses := [] }

theorem profile40_node180 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,17] 6 43 profile40_node180_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,17] 6 43 profile40_node180_cert).mp (by decide +kernel))

def profile40_node181_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 73 50 22 41 57 41 105), lower := (rows 73 50 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 64), good := (rows 72 54 22 8 16 32 64) }] }

theorem profile40_node181 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,18] 6 41 profile40_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,18] 6 41 profile40_node181_cert).mp (by decide +kernel))

def profile40_node182_cert : Bound 7 := { allowed := (rows 48 9 33 0 0 0 0), upper := (rows 73 50 28 43 51 35 99), lower := (rows 73 50 28 8 16 32 64), losses := [] }

theorem profile40_node182 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,24] 6 35 profile40_node182_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,24] 6 35 profile40_node182_cert).mp (by decide +kernel))

def profile40_node183_cert : Bound 7 := { allowed := (rows 48 9 9 0 0 0 0), upper := (rows 73 50 52 11 27 43 75), lower := (rows 73 50 52 8 16 32 64), losses := [] }

theorem profile40_node183 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,48] 6 11 profile40_node183_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48,48] 6 11 profile40_node183_cert).mp (by decide +kernel))

def profile40_node174_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node174_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node174 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72,48] 6 (by decide) (choices 2) [3,9,10,17,18,24,48] profile40_node174_route profile40_node174_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node175
  · exact profile40_node178
  · exact profile40_node179
  · exact profile40_node180
  · exact profile40_node181
  · exact profile40_node182
  · exact profile40_node183

def profile40_node143_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 65 => 6 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node143_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node143 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [72] 6 (by decide) (choices 2) [9,17,24,48] profile40_node143_route profile40_node143_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile40_node144
  · exact profile40_node145
  · exact profile40_node159
  · exact profile40_node174

def profile40_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile40_node0_route : Route 7 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 34 => (10,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 96 => (72,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile40_node0 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [] 6 (by decide) (choices 2) [10,24,66,72] profile40_node0_route profile40_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile40_node1
  · exact profile40_node54
  · exact profile40_node123
  · exact profile40_node143

theorem profile40 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [] 6 := profile40_node0


#print axioms profile40
end Delivery.SmallBudgetTenFinite7
