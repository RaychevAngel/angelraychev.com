import SmallBudgetTenFinite6Profile013Part000

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile13_node125_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node125_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node125 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,33] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node125_route profile13_node125_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node126
  · exact profile13_node127
  · exact profile13_node128
  · exact profile13_node129
  · exact profile13_node130
  · exact profile13_node131

def profile13_node133_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 19 14 38 25 49 33), lower := (rows 19 14 38 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 25 41), good := (rows 57 60 36 57 16 32) },{ target := 4, region := (rows 1 10 15 8 0 41), good := (rows 39 46 38 47 0 32) }] }

theorem profile13_node133 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,17] 6 33 profile13_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,17] 6 33 profile13_node133_cert).mp (by decide +kernel))

def profile13_node134_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 19 14 38 41 17 49), lower := (rows 19 14 38 41 16 32), losses := [{ target := 0, region := (rows 0 10 12 8 16 32), good := (rows 18 14 38 46 16 32) }] }

theorem profile13_node134 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,33] 6 17 profile13_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,33] 6 17 profile13_node134_cert).mp (by decide +kernel))

def profile13_node135_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 19 14 38 56 17 33), lower := (rows 19 14 38 56 16 32), losses := [{ target := 0, region := (rows 0 10 12 8 16 32), good := (rows 18 14 38 62 16 32) }] }

theorem profile13_node135 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,48] 6 1 profile13_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34,48] 6 1 profile13_node135_cert).mp (by decide +kernel))

def profile13_node132_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node132_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node132 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,34] 6 (by decide) (choices 2) [17,33,48] profile13_node132_route profile13_node132_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node133
  · exact profile13_node134
  · exact profile13_node135

def profile13_node137_cert : CutBound 6 := { lost := (rows 0 0 2 16 0 0), upper := (rows 19 14 52 11 49 33), lower := (rows 19 14 52 11 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 25 41), good := (rows 53 60 52 61 16 32) },{ target := 4, region := (rows 1 2 4 9 0 41), good := (rows 43 46 36 43 0 32) }] }

theorem profile13_node137 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,3] 6 33 profile13_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,3] 6 33 profile13_node137_cert).mp (by decide +kernel))

def profile13_node138_cert : CutBound 6 := { lost := (rows 32 0 0 16 0 0), upper := (rows 19 14 52 41 19 35), lower := (rows 19 14 52 41 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 43 14 36 41 0 32) },{ target := 5, region := (rows 3 2 4 8 19 0), good := (rows 19 31 20 25 16 0) }] }

theorem profile13_node138 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,33] 6 3 profile13_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,33] 6 3 profile13_node138_cert).mp (by decide +kernel))

def profile13_node139_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 19 14 52 42 17 33), lower := (rows 19 14 52 42 16 32), losses := [{ target := 0, region := (rows 0 6 4 12 16 32), good := (rows 18 14 62 42 16 32) }] }

theorem profile13_node139 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,34] 6 1 profile13_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48,34] 6 1 profile13_node139_cert).mp (by decide +kernel))

def profile13_node136_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node136_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node136 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12,48] 6 (by decide) (choices 2) [3,33,34] profile13_node136_route profile13_node136_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node137
  · exact profile13_node138
  · exact profile13_node139

def profile13_node121_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node121_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node121 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,12] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node121_route profile13_node121_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node122
  · exact profile13_node123
  · exact profile13_node124
  · exact profile13_node125
  · exact profile13_node132
  · exact profile13_node136

def profile13_node140_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 19 47 47 63 47), lower := (rows 19 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 35), good := (rows 47 47 4 8 0 32) }] }

theorem profile13_node140 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,17] 6 47 profile13_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,17] 6 47 profile13_node140_cert).mp (by decide +kernel))

def profile13_node141_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 22 47 43 59 43), lower := (rows 19 22 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 6 4 8 0 32) }] }

theorem profile13_node141 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,20] 6 43 profile13_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,20] 6 43 profile13_node141_cert).mp (by decide +kernel))

def profile13_node143_cert : CutBound 6 := { lost := (rows 0 0 0 3 0 0), upper := (rows 19 35 7 60 60 60), lower := (rows 19 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 18 34 62 8 16 32) },{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 17 33 61 8 16 32) }] }

theorem profile13_node143 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,3] 6 60 profile13_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,3] 6 60 profile13_node143_cert).mp (by decide +kernel))

def profile13_node145_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 35 13 14 48 48), lower := (rows 19 35 13 14 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 32), good := (rows 15 47 13 14 0 32) }] }

theorem profile13_node145 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,6] 6 48 profile13_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,6] 6 48 profile13_node145_cert).mp (by decide +kernel))

def profile13_node146_cert : Bound 6 := { allowed := (rows 32 16 50 32 0 0), upper := (rows 19 35 13 26 52 36), lower := (rows 19 35 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 20 36), good := (rows 26 42 60 26 16 32) }] }

theorem profile13_node146 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,18] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,18] 6 36 profile13_node146_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,18] 6 36 profile13_node146_cert).mp (by decide +kernel))

def profile13_node147_cert : CutBound 6 := { lost := (rows 0 0 2 3 0 0), upper := (rows 19 35 13 28 50 34), lower := (rows 19 35 13 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 19 35), good := (rows 50 50 60 28 16 32) },{ target := 1, region := (rows 1 0 7 9 16 32), good := (rows 29 45 13 28 16 32) }] }

theorem profile13_node147 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,20] 6 34 profile13_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,20] 6 34 profile13_node147_cert).mp (by decide +kernel))

def profile13_node148_cert : Bound 6 := { allowed := (rows 32 16 50 16 0 0), upper := (rows 19 35 13 42 20 52), lower := (rows 19 35 13 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 20 36), good := (rows 26 42 60 42 16 32) }] }

theorem profile13_node148 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,34] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,34] 6 20 profile13_node148_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,34] 6 20 profile13_node148_cert).mp (by decide +kernel))

def profile13_node149_cert : CutBound 6 := { lost := (rows 0 0 2 3 0 0), upper := (rows 19 35 13 44 18 50), lower := (rows 19 35 13 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 19 35), good := (rows 50 50 60 44 16 32) },{ target := 1, region := (rows 1 0 7 10 16 32), good := (rows 29 45 13 44 16 32) }] }

theorem profile13_node149 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,36] 6 18 profile13_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,36] 6 18 profile13_node149_cert).mp (by decide +kernel))

def profile13_node150_cert : Bound 6 := { allowed := (rows 32 0 50 3 0 0), upper := (rows 19 35 13 56 22 38), lower := (rows 19 35 13 56 16 32), losses := [{ target := 4, region := (rows 1 6 4 8 0 36), good := (rows 3 35 47 40 0 32) }] }

theorem profile13_node150 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,48] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,48] 6 6 profile13_node150_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9,48] 6 6 profile13_node150_cert).mp (by decide +kernel))

def profile13_node144_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | _ => 0

def profile13_node144_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node144 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,9] 6 (by decide) (choices 2) [6,18,20,34,36,48] profile13_node144_route profile13_node144_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node145
  · exact profile13_node146
  · exact profile13_node147
  · exact profile13_node148
  · exact profile13_node149
  · exact profile13_node150

def profile13_node152_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 35 14 13 48 48), lower := (rows 19 35 14 13 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 32), good := (rows 15 47 14 13 0 32) }] }

theorem profile13_node152 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,5] 6 48 profile13_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,5] 6 48 profile13_node152_cert).mp (by decide +kernel))

def profile13_node153_cert : Bound 6 := { allowed := (rows 32 16 49 32 0 0), upper := (rows 19 35 14 25 52 36), lower := (rows 19 35 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 20 36), good := (rows 25 41 60 25 16 32) }] }

theorem profile13_node153 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,17] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,17] 6 36 profile13_node153_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,17] 6 36 profile13_node153_cert).mp (by decide +kernel))

def profile13_node154_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 14 28 49 33), lower := (rows 19 35 14 28 16 32), losses := [{ target := 0, region := (rows 0 2 7 9 16 32), good := (rows 30 46 14 28 16 32) }] }

theorem profile13_node154 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,20] 6 33 profile13_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,20] 6 33 profile13_node154_cert).mp (by decide +kernel))

def profile13_node155_cert : Bound 6 := { allowed := (rows 32 16 49 16 0 0), upper := (rows 19 35 14 41 20 52), lower := (rows 19 35 14 41 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 20 36), good := (rows 25 41 60 41 16 32) }] }

theorem profile13_node155 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,33] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,33] 6 20 profile13_node155_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,33] 6 20 profile13_node155_cert).mp (by decide +kernel))

def profile13_node156_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 14 44 17 49), lower := (rows 19 35 14 44 16 32), losses := [{ target := 0, region := (rows 0 2 7 10 16 32), good := (rows 30 46 14 44 16 32) }] }

theorem profile13_node156 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,36] 6 17 profile13_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,36] 6 17 profile13_node156_cert).mp (by decide +kernel))

def profile13_node157_cert : Bound 6 := { allowed := (rows 0 16 49 3 0 0), upper := (rows 19 35 14 56 21 37), lower := (rows 19 35 14 56 16 32), losses := [{ target := 5, region := (rows 5 2 4 8 20 0), good := (rows 19 3 31 24 16 0) }] }

theorem profile13_node157 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,48] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,48] 6 5 profile13_node157_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10,48] 6 5 profile13_node157_cert).mp (by decide +kernel))

def profile13_node151_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | _ => 0

def profile13_node151_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node151 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,10] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile13_node151_route profile13_node151_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node152
  · exact profile13_node153
  · exact profile13_node154
  · exact profile13_node155
  · exact profile13_node156
  · exact profile13_node157

def profile13_node158_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 19 35 21 46 62 46), lower := (rows 19 35 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 37 21 8 16 32) },{ target := 4, region := (rows 1 6 4 12 0 36), good := (rows 3 35 47 8 0 32) }] }

theorem profile13_node158 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,17] 6 46 profile13_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,17] 6 46 profile13_node158_cert).mp (by decide +kernel))

def profile13_node159_cert : CutBound 6 := { lost := (rows 32 0 33 0 0 0), upper := (rows 19 35 22 45 61 45), lower := (rows 19 35 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) },{ target := 5, region := (rows 5 2 5 8 16 0), good := (rows 23 7 23 8 16 0) }] }

theorem profile13_node159 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,18] 6 45 profile13_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,18] 6 45 profile13_node159_cert).mp (by decide +kernel))

def profile13_node161_cert : Bound 6 := { allowed := (rows 32 16 34 48 0 0), upper := (rows 19 35 28 11 52 36), lower := (rows 19 35 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 28 44), good := (rows 18 34 60 62 16 32) }] }

theorem profile13_node161 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,3] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,3] 6 36 profile13_node161_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,3] 6 36 profile13_node161_cert).mp (by decide +kernel))

def profile13_node162_cert : CutBound 6 := { lost := (rows 0 0 3 2 0 0), upper := (rows 19 35 28 13 50 34), lower := (rows 19 35 28 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 50 50 28 60 16 32) },{ target := 1, region := (rows 1 0 5 11 16 32), good := (rows 29 45 28 13 16 32) }] }

theorem profile13_node162 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,5] 6 34 profile13_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,5] 6 34 profile13_node162_cert).mp (by decide +kernel))

def profile13_node163_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 28 14 49 33), lower := (rows 19 35 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 5 11 16 32), good := (rows 30 46 28 14 16 32) }] }

theorem profile13_node163 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,6] 6 33 profile13_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,6] 6 33 profile13_node163_cert).mp (by decide +kernel))

def profile13_node164_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 19 35 28 41 22 38), lower := (rows 19 35 28 41 16 32), losses := [{ target := 1, region := (rows 1 0 5 10 16 32), good := (rows 29 45 28 45 16 32) }] }

theorem profile13_node164 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,33] 6 6 profile13_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,33] 6 6 profile13_node164_cert).mp (by decide +kernel))

def profile13_node165_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 28 42 21 37), lower := (rows 19 35 28 42 16 32), losses := [{ target := 0, region := (rows 0 2 5 10 16 32), good := (rows 30 46 28 42 16 32) }] }

theorem profile13_node165 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,34] 6 5 profile13_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,34] 6 5 profile13_node165_cert).mp (by decide +kernel))

def profile13_node166_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 28 44 19 35), lower := (rows 19 35 28 44 16 32), losses := [{ target := 0, region := (rows 0 2 5 10 16 32), good := (rows 30 46 28 44 16 32) }] }

theorem profile13_node166 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,36] 6 3 profile13_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24,36] 6 3 profile13_node166_cert).mp (by decide +kernel))

def profile13_node160_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile13_node160_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node160 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,24] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile13_node160_route profile13_node160_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node161
  · exact profile13_node162
  · exact profile13_node163
  · exact profile13_node164
  · exact profile13_node165
  · exact profile13_node166

def profile13_node167_cert : CutBound 6 := { lost := (rows 0 16 18 0 0 0), upper := (rows 19 35 37 30 30 62), lower := (rows 19 35 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 21 37 37 8 16 32) },{ target := 4, region := (rows 1 6 6 8 0 32), good := (rows 7 39 39 8 0 32) }] }

theorem profile13_node167 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,33] 6 30 profile13_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,33] 6 30 profile13_node167_cert).mp (by decide +kernel))

def profile13_node168_cert : CutBound 6 := { lost := (rows 0 0 17 0 0 0), upper := (rows 19 35 38 29 29 61), lower := (rows 19 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 22 38 38 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 7 39 38 8 0 32) }] }

theorem profile13_node168 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,34] 6 29 profile13_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,34] 6 29 profile13_node168_cert).mp (by decide +kernel))

def profile13_node170_cert : Bound 6 := { allowed := (rows 32 16 18 48 0 0), upper := (rows 19 35 44 11 20 52), lower := (rows 19 35 44 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 28 44), good := (rows 18 34 60 62 16 32) }] }

theorem profile13_node170 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,3] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,3] 6 20 profile13_node170_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,3] 6 20 profile13_node170_cert).mp (by decide +kernel))

def profile13_node171_cert : CutBound 6 := { lost := (rows 0 0 3 2 0 0), upper := (rows 19 35 44 13 18 50), lower := (rows 19 35 44 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 50 50 44 60 16 32) },{ target := 1, region := (rows 1 0 6 11 16 32), good := (rows 29 45 44 13 16 32) }] }

theorem profile13_node171 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,5] 6 18 profile13_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,5] 6 18 profile13_node171_cert).mp (by decide +kernel))

def profile13_node172_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 44 14 17 49), lower := (rows 19 35 44 14 16 32), losses := [{ target := 0, region := (rows 0 2 6 11 16 32), good := (rows 30 46 44 14 16 32) }] }

theorem profile13_node172 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,6] 6 17 profile13_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,6] 6 17 profile13_node172_cert).mp (by decide +kernel))

def profile13_node173_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 19 35 44 25 22 38), lower := (rows 19 35 44 25 16 32), losses := [{ target := 1, region := (rows 1 0 6 9 16 32), good := (rows 29 45 44 25 16 32) }] }

theorem profile13_node173 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,17] 6 6 profile13_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,17] 6 6 profile13_node173_cert).mp (by decide +kernel))

def profile13_node174_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 44 26 21 37), lower := (rows 19 35 44 26 16 32), losses := [{ target := 0, region := (rows 0 2 6 9 16 32), good := (rows 30 46 44 30 16 32) }] }

theorem profile13_node174 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,18] 6 5 profile13_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,18] 6 5 profile13_node174_cert).mp (by decide +kernel))

def profile13_node175_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 44 28 19 35), lower := (rows 19 35 44 28 16 32), losses := [{ target := 0, region := (rows 0 2 6 9 16 32), good := (rows 30 46 44 28 16 32) }] }

theorem profile13_node175 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,20] 6 3 profile13_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40,20] 6 3 profile13_node175_cert).mp (by decide +kernel))

def profile13_node169_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile13_node169_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node169 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,40] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile13_node169_route profile13_node169_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node170
  · exact profile13_node171
  · exact profile13_node172
  · exact profile13_node173
  · exact profile13_node174
  · exact profile13_node175

def profile13_node177_cert : Bound 6 := { allowed := (rows 32 16 3 48 0 0), upper := (rows 19 35 52 11 28 44), lower := (rows 19 35 52 11 16 32), losses := [] }

theorem profile13_node177 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,3] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,3] 6 12 profile13_node177_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,3] 6 12 profile13_node177_cert).mp (by decide +kernel))

def profile13_node178_cert : Bound 6 := { allowed := (rows 32 0 3 50 0 0), upper := (rows 19 35 52 13 26 42), lower := (rows 19 35 52 13 16 32), losses := [{ target := 4, region := (rows 1 10 4 8 0 40), good := (rows 3 35 36 47 0 32) }] }

theorem profile13_node178 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,5] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,5] 6 10 profile13_node178_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,5] 6 10 profile13_node178_cert).mp (by decide +kernel))

def profile13_node179_cert : Bound 6 := { allowed := (rows 0 16 3 49 0 0), upper := (rows 19 35 52 14 25 41), lower := (rows 19 35 52 14 16 32), losses := [{ target := 5, region := (rows 9 2 4 8 24 0), good := (rows 19 3 20 31 16 0) }] }

theorem profile13_node179 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,6] 6 :=
  DegreeLoss.bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,6] 6 9 profile13_node179_cert
    ((DegreeLoss.boundCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48,6] 6 9 profile13_node179_cert).mp (by decide +kernel))

def profile13_node176_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile13_node176_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node176 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33,48] 6 (by decide) (choices 2) [3,5,6] profile13_node176_route profile13_node176_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node177
  · exact profile13_node178
  · exact profile13_node179

def profile13_node142_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node142_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node142 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,33] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile13_node142_route profile13_node142_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node143
  · exact profile13_node144
  · exact profile13_node151
  · exact profile13_node158
  · exact profile13_node159
  · exact profile13_node160
  · exact profile13_node167
  · exact profile13_node168
  · exact profile13_node169
  · exact profile13_node176

def profile13_node181_cert : CutBound 6 := { lost := (rows 0 0 16 2 0 0), upper := (rows 19 38 7 57 57 57), lower := (rows 19 38 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 13 21 37), good := (rows 57 60 61 8 16 32) },{ target := 4, region := (rows 1 2 5 8 0 32), good := (rows 7 38 7 8 0 32) }] }

theorem profile13_node181 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,3] 6 57 profile13_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,3] 6 57 profile13_node181_cert).mp (by decide +kernel))

def profile13_node183_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 19 38 13 11 48 48), lower := (rows 19 38 13 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 63 63), good := (rows 50 54 62 58 48 48) },{ target := 1, region := (rows 1 0 12 8 63 63), good := (rows 49 52 61 61 48 48) }] }

theorem profile13_node183 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,3] 6 48 profile13_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,3] 6 48 profile13_node183_cert).mp (by decide +kernel))

def profile13_node184_cert : CutBound 6 := { lost := (rows 0 1 2 2 0 0), upper := (rows 19 38 13 25 50 34), lower := (rows 19 38 13 25 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 23 39), good := (rows 50 54 62 56 16 32) },{ target := 1, region := (rows 1 0 13 9 16 32), good := (rows 29 36 13 29 16 32) }] }

theorem profile13_node184 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,17] 6 34 profile13_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,17] 6 34 profile13_node184_cert).mp (by decide +kernel))

def profile13_node185_cert : CutBound 6 := { lost := (rows 0 16 0 1 0 0), upper := (rows 19 38 13 26 49 33), lower := (rows 19 38 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 26 38 12 26 16 32) },{ target := 4, region := (rows 1 6 4 8 0 37), good := (rows 35 38 47 10 0 32) }] }

theorem profile13_node185 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,18] 6 33 profile13_node185_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,18] 6 33 profile13_node185_cert).mp (by decide +kernel))

def profile13_node186_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 19 38 13 41 18 50), lower := (rows 19 38 13 41 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 23 39), good := (rows 50 54 62 56 16 32) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 17 36 13 45 16 32) }] }

theorem profile13_node186 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,33] 6 18 profile13_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,33] 6 18 profile13_node186_cert).mp (by decide +kernel))

def profile13_node187_cert : CutBound 6 := { lost := (rows 0 0 16 17 0 0), upper := (rows 19 38 13 42 17 49), lower := (rows 19 38 13 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 26 46 12 42 16 32) },{ target := 4, region := (rows 1 2 5 10 0 32), good := (rows 15 46 13 42 0 32) }] }

theorem profile13_node187 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,34] 6 17 profile13_node187_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,34] 6 17 profile13_node187_cert).mp (by decide +kernel))

def profile13_node188_cert : CutBound 6 := { lost := (rows 32 16 0 0 0 0), upper := (rows 19 38 13 56 19 35), lower := (rows 19 38 13 56 16 32), losses := [{ target := 4, region := (rows 1 6 4 8 0 37), good := (rows 35 38 47 40 0 32) },{ target := 5, region := (rows 3 2 4 8 19 0), good := (rows 19 23 29 24 16 0) }] }

theorem profile13_node188 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,48] 6 3 profile13_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9,48] 6 3 profile13_node188_cert).mp (by decide +kernel))

def profile13_node182_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node182_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node182 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node182_route profile13_node182_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node183
  · exact profile13_node184
  · exact profile13_node185
  · exact profile13_node186
  · exact profile13_node187
  · exact profile13_node188

def profile13_node190_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 19 38 14 25 49 33), lower := (rows 19 38 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 25 41), good := (rows 57 36 60 57 16 32) },{ target := 4, region := (rows 1 14 12 8 0 41), good := (rows 35 38 46 47 0 32) }] }

theorem profile13_node190 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,17] 6 33 profile13_node190_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,17] 6 33 profile13_node190_cert).mp (by decide +kernel))

def profile13_node191_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 19 38 14 41 17 49), lower := (rows 19 38 14 41 16 32), losses := [{ target := 0, region := (rows 0 10 12 8 16 32), good := (rows 18 38 14 46 16 32) }] }

theorem profile13_node191 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,33] 6 17 profile13_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,33] 6 17 profile13_node191_cert).mp (by decide +kernel))

def profile13_node192_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 19 38 14 56 17 33), lower := (rows 19 38 14 56 16 32), losses := [{ target := 0, region := (rows 0 10 12 8 16 32), good := (rows 18 38 14 62 16 32) }] }

theorem profile13_node192 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,48] 6 1 profile13_node192_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10,48] 6 1 profile13_node192_cert).mp (by decide +kernel))

def profile13_node189_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node189_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node189 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,10] 6 (by decide) (choices 2) [17,33,48] profile13_node189_route profile13_node189_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node190
  · exact profile13_node191
  · exact profile13_node192

def profile13_node193_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 19 38 21 43 59 43), lower := (rows 19 38 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 36 21 8 16 32) },{ target := 4, region := (rows 1 6 4 13 0 37), good := (rows 43 46 47 8 0 32) }] }

theorem profile13_node193 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,17] 6 43 profile13_node193_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,17] 6 43 profile13_node193_cert).mp (by decide +kernel))

def profile13_node194_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 19 38 22 41 57 41), lower := (rows 19 38 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) },{ target := 1, region := (rows 1 0 4 9 17 33), good := (rows 57 36 20 8 16 32) }] }

theorem profile13_node194 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,18] 6 41 profile13_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,18] 6 41 profile13_node194_cert).mp (by decide +kernel))

def profile13_node196_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 19 38 28 11 49 33), lower := (rows 19 38 28 11 16 32), losses := [{ target := 1, region := (rows 1 0 12 8 25 41), good := (rows 49 36 60 61 16 32) },{ target := 4, region := (rows 1 6 4 9 0 41), good := (rows 43 38 46 43 0 32) }] }

theorem profile13_node196 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,3] 6 33 profile13_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,3] 6 33 profile13_node196_cert).mp (by decide +kernel))

def profile13_node197_cert : CutBound 6 := { lost := (rows 32 0 32 16 0 0), upper := (rows 19 38 28 41 19 35), lower := (rows 19 38 28 41 16 32), losses := [{ target := 4, region := (rows 1 2 4 9 0 33), good := (rows 43 38 12 41 0 32) },{ target := 5, region := (rows 3 2 12 8 19 0), good := (rows 19 23 28 29 16 0) }] }

theorem profile13_node197 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,33] 6 3 profile13_node197_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,33] 6 3 profile13_node197_cert).mp (by decide +kernel))

def profile13_node198_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 38 28 42 17 33), lower := (rows 19 38 28 42 16 32), losses := [{ target := 0, region := (rows 0 2 5 10 16 32), good := (rows 30 46 28 42 16 32) }] }

theorem profile13_node198 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,34] 6 1 profile13_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24,34] 6 1 profile13_node198_cert).mp (by decide +kernel))

def profile13_node195_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node195_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node195 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,24] 6 (by decide) (choices 2) [3,33,34] profile13_node195_route profile13_node195_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node196
  · exact profile13_node197
  · exact profile13_node198

def profile13_node199_cert : CutBound 6 := { lost := (rows 0 17 0 0 0 0), upper := (rows 19 38 37 27 27 59), lower := (rows 19 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 38 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 38 39 8 0 32) }] }

theorem profile13_node199 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,33] 6 27 profile13_node199_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,33] 6 27 profile13_node199_cert).mp (by decide +kernel))

def profile13_node200_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 19 38 38 25 25 57), lower := (rows 19 38 38 8 16 32), losses := [{ target := 0, region := (rows 0 38 38 8 16 32), good := (rows 22 38 38 8 16 38) }] }

theorem profile13_node200 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,34] 6 25 profile13_node200_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,34] 6 25 profile13_node200_cert).mp (by decide +kernel))

def profile13_node201_cert : CutBound 6 := { lost := (rows 0 17 0 0 0 0), upper := (rows 19 38 44 27 19 51), lower := (rows 19 38 44 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 46 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 3 38 46 8 0 32) }] }

theorem profile13_node201 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,40] 6 19 profile13_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,40] 6 19 profile13_node201_cert).mp (by decide +kernel))

def profile13_node202_cert : CutBound 6 := { lost := (rows 0 17 0 16 0 0), upper := (rows 19 38 52 11 27 43), lower := (rows 19 38 52 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 18 38 54 8 16 32) },{ target := 4, region := (rows 1 6 4 9 0 33), good := (rows 43 38 38 8 0 32) }] }

theorem profile13_node202 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,48] 6 11 profile13_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36,48] 6 11 profile13_node202_cert).mp (by decide +kernel))

def profile13_node180_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node180_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node180 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,36] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile13_node180_route profile13_node180_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node181
  · exact profile13_node182
  · exact profile13_node189
  · exact profile13_node193
  · exact profile13_node194
  · exact profile13_node195
  · exact profile13_node199
  · exact profile13_node200
  · exact profile13_node201
  · exact profile13_node202

def profile13_node203_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 50 47 47 63 47), lower := (rows 19 50 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 5 9 0 33), good := (rows 47 34 4 8 0 32) }] }

theorem profile13_node203 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,48] 6 47 profile13_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18,48] 6 47 profile13_node203_cert).mp (by decide +kernel))

def profile13_node98_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node98_route : Route 6 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile13_node98 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [18] 6 (by decide) (choices 2) [5,12,17,20,33,36,48] profile13_node98_route profile13_node98_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node99
  · exact profile13_node121
  · exact profile13_node140
  · exact profile13_node141
  · exact profile13_node142
  · exact profile13_node180
  · exact profile13_node203

def profile13_node206_cert : CutBound 6 := { lost := (rows 0 0 16 1 0 0), upper := (rows 21 11 7 58 50 50), lower := (rows 21 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 60 58 62 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 5 15 7 8 0 32) }] }

theorem profile13_node206 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,3] 6 50 profile13_node206_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,3] 6 50 profile13_node206_cert).mp (by decide +kernel))

def profile13_node207_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 21 11 21 42 50 34), lower := (rows 21 11 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 20 58 20 8 16 32) },{ target := 1, region := (rows 21 0 21 8 16 32), good := (rows 21 13 21 8 21 32) }] }

theorem profile13_node207 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,17] 6 34 profile13_node207_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,17] 6 34 profile13_node207_cert).mp (by decide +kernel))

def profile13_node208_cert : CutBound 6 := { lost := (rows 2 16 0 16 0 0), upper := (rows 21 11 22 43 51 35), lower := (rows 21 11 22 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 9 21 8 16 32) },{ target := 4, region := (rows 1 3 4 11 0 35), good := (rows 47 43 46 8 0 32) }] }

theorem profile13_node208 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,18] 6 35 profile13_node208_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,18] 6 35 profile13_node208_cert).mp (by decide +kernel))

def profile13_node210_cert : CutBound 6 := { lost := (rows 0 0 16 1 0 0), upper := (rows 21 11 37 26 50 34), lower := (rows 21 11 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 26 42), good := (rows 20 58 36 58 16 32) },{ target := 4, region := (rows 1 2 6 8 0 42), good := (rows 5 47 37 46 0 32) }] }

theorem profile13_node210 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,18] 6 34 profile13_node210_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,18] 6 34 profile13_node210_cert).mp (by decide +kernel))

def profile13_node211_cert : CutBound 6 := { lost := (rows 0 16 0 17 0 0), upper := (rows 21 11 37 42 18 50), lower := (rows 21 11 37 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 26 42), good := (rows 20 58 36 58 16 32) },{ target := 4, region := (rows 1 7 4 12 0 32), good := (rows 15 11 47 42 0 32) }] }

theorem profile13_node211 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,34] 6 18 profile13_node211_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,34] 6 18 profile13_node211_cert).mp (by decide +kernel))

def profile13_node212_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 21 11 37 56 18 34), lower := (rows 21 11 37 56 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 20 58 36 56 16 32) },{ target := 1, region := (rows 9 0 12 8 16 32), good := (rows 21 13 37 61 16 32) }] }

theorem profile13_node212 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,48] 6 2 profile13_node212_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33,48] 6 2 profile13_node212_cert).mp (by decide +kernel))

def profile13_node209_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node209_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node209 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,33] 6 (by decide) (choices 2) [18,34,48] profile13_node209_route profile13_node209_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node210
  · exact profile13_node211
  · exact profile13_node212

def profile13_node214_cert : CutBound 6 := { lost := (rows 2 0 1 0 0 0), upper := (rows 21 11 38 11 48 48), lower := (rows 21 11 38 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 63 63), good := (rows 52 62 54 62 48 48) },{ target := 1, region := (rows 5 0 4 8 63 63), good := (rows 53 57 53 57 48 48) }] }

theorem profile13_node214 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,3] 6 48 profile13_node214_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,3] 6 48 profile13_node214_cert).mp (by decide +kernel))

def profile13_node215_cert : CutBound 6 := { lost := (rows 0 0 1 2 0 0), upper := (rows 21 11 38 25 50 34), lower := (rows 21 11 38 25 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 52 62 54 24 16 32) },{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 29 9 36 25 16 32) }] }

theorem profile13_node215 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,17] 6 34 profile13_node215_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,17] 6 34 profile13_node215_cert).mp (by decide +kernel))

def profile13_node216_cert : CutBound 6 := { lost := (rows 2 0 16 0 0 0), upper := (rows 21 11 38 26 49 33), lower := (rows 21 11 38 26 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 23 39), good := (rows 53 57 53 56 16 32) },{ target := 4, region := (rows 1 2 14 8 0 35), good := (rows 37 47 38 46 0 32) }] }

theorem profile13_node216 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,18] 6 33 profile13_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,18] 6 33 profile13_node216_cert).mp (by decide +kernel))

def profile13_node217_cert : CutBound 6 := { lost := (rows 0 16 17 0 0 0), upper := (rows 21 11 38 41 18 50), lower := (rows 21 11 38 41 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 52 62 54 40 16 32) },{ target := 4, region := (rows 1 10 12 8 0 32), good := (rows 5 15 38 47 0 32) }] }

theorem profile13_node217 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,33] 6 18 profile13_node217_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,33] 6 18 profile13_node217_cert).mp (by decide +kernel))

def profile13_node218_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 21 11 38 42 17 49), lower := (rows 21 11 38 42 16 32), losses := [{ target := 0, region := (rows 0 2 12 12 16 32), good := (rows 28 14 46 46 16 32) }] }

theorem profile13_node218 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,34] 6 17 profile13_node218_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,34] 6 17 profile13_node218_cert).mp (by decide +kernel))

def profile13_node219_cert : CutBound 6 := { lost := (rows 32 0 16 0 0 0), upper := (rows 21 11 38 56 19 35), lower := (rows 21 11 38 56 16 32), losses := [{ target := 4, region := (rows 1 2 6 8 0 34), good := (rows 5 47 38 40 0 32) },{ target := 5, region := (rows 5 2 4 8 22 0), good := (rows 21 27 23 24 16 0) }] }

theorem profile13_node219 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,48] 6 3 profile13_node219_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34,48] 6 3 profile13_node219_cert).mp (by decide +kernel))

def profile13_node213_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node213_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node213 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,34] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node213_route profile13_node213_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node214
  · exact profile13_node215
  · exact profile13_node216
  · exact profile13_node217
  · exact profile13_node218
  · exact profile13_node219

def profile13_node220_cert : CutBound 6 := { lost := (rows 2 16 0 16 0 0), upper := (rows 21 11 52 43 51 35), lower := (rows 21 11 52 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 9 53 8 16 32) },{ target := 4, region := (rows 1 3 4 11 0 35), good := (rows 47 43 36 8 0 32) }] }

theorem profile13_node220 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,48] 6 35 profile13_node220_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9,48] 6 35 profile13_node220_cert).mp (by decide +kernel))

def profile13_node205_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node205_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node205 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node205_route profile13_node205_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node206
  · exact profile13_node207
  · exact profile13_node208
  · exact profile13_node209
  · exact profile13_node213
  · exact profile13_node220

def profile13_node221_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 21 19 47 43 59 43), lower := (rows 21 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 34), good := (rows 5 47 4 8 0 32) }] }

theorem profile13_node221 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,17] 6 43 profile13_node221_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,17] 6 43 profile13_node221_cert).mp (by decide +kernel))

def profile13_node223_cert : CutBound 6 := { lost := (rows 32 0 32 16 0 0), upper := (rows 21 26 7 43 51 35), lower := (rows 21 26 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 45 10 47 8 0 32) },{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 21 31 7 8 16 0) }] }

theorem profile13_node223 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,3] 6 35 profile13_node223_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,3] 6 35 profile13_node223_cert).mp (by decide +kernel))

def profile13_node225_cert : CutBound 6 := { lost := (rows 0 1 16 0 0 0), upper := (rows 21 26 37 11 50 34), lower := (rows 21 26 37 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 26 42), good := (rows 20 58 36 58 16 32) },{ target := 4, region := (rows 1 2 12 8 0 42), good := (rows 5 46 37 47 0 32) }] }

theorem profile13_node225 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,3] 6 34 profile13_node225_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,3] 6 34 profile13_node225_cert).mp (by decide +kernel))

def profile13_node226_cert : CutBound 6 := { lost := (rows 2 1 2 2 0 0), upper := (rows 21 26 37 41 18 34), lower := (rows 21 26 37 41 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 26 42), good := (rows 20 58 36 58 16 32) },{ target := 1, region := (rows 3 0 12 12 16 32), good := (rows 29 29 45 45 16 32) }] }

theorem profile13_node226 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,33] 6 2 profile13_node226_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,33] 6 2 profile13_node226_cert).mp (by decide +kernel))

def profile13_node227_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 21 26 37 42 19 35), lower := (rows 21 26 37 42 16 32), losses := [{ target := 0, region := (rows 0 3 4 12 16 32), good := (rows 30 26 46 42 16 32) }] }

theorem profile13_node227 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,34] 6 3 profile13_node227_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33,34] 6 3 profile13_node227_cert).mp (by decide +kernel))

def profile13_node224_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node224_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node224 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,33] 6 (by decide) (choices 2) [3,33,34] profile13_node224_route profile13_node224_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node225
  · exact profile13_node226
  · exact profile13_node227

def profile13_node229_cert : CutBound 6 := { lost := (rows 2 0 16 0 0 0), upper := (rows 21 26 38 11 49 33), lower := (rows 21 26 38 11 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 29 45), good := (rows 53 56 53 57 16 32) },{ target := 4, region := (rows 1 2 14 8 0 41), good := (rows 37 46 38 47 0 32) }] }

theorem profile13_node229 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,3] 6 33 profile13_node229_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,3] 6 33 profile13_node229_cert).mp (by decide +kernel))

def profile13_node230_cert : CutBound 6 := { lost := (rows 32 32 0 0 0 0), upper := (rows 21 26 38 41 19 35), lower := (rows 21 26 38 41 16 32), losses := [{ target := 5, region := (rows 5 10 4 8 28 0), good := (rows 21 26 23 27 16 0) }] }

theorem profile13_node230 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,33] 6 3 profile13_node230_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,33] 6 3 profile13_node230_cert).mp (by decide +kernel))

def profile13_node231_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 21 26 38 42 17 33), lower := (rows 21 26 38 42 16 32), losses := [{ target := 0, region := (rows 0 3 12 12 16 32), good := (rows 30 30 46 46 16 32) }] }

theorem profile13_node231 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,34] 6 1 profile13_node231_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34,34] 6 1 profile13_node231_cert).mp (by decide +kernel))

def profile13_node228_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node228_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node228 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24,34] 6 (by decide) (choices 2) [3,33,34] profile13_node228_route profile13_node228_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node229
  · exact profile13_node230
  · exact profile13_node231

def profile13_node222_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile13_node222_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node222 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,24] 6 (by decide) (choices 2) [3,33,34] profile13_node222_route profile13_node222_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node223
  · exact profile13_node224
  · exact profile13_node228

def profile13_node233_cert : CutBound 6 := { lost := (rows 0 0 16 1 0 0), upper := (rows 21 35 7 58 58 58), lower := (rows 21 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 60 58 62 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 5 39 7 8 0 32) }] }

theorem profile13_node233 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,3] 6 58 profile13_node233_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,3] 6 58 profile13_node233_cert).mp (by decide +kernel))

def profile13_node235_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 21 35 13 26 50 34), lower := (rows 21 35 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 26 42), good := (rows 20 58 60 58 16 32) },{ target := 1, region := (rows 9 0 12 8 16 32), good := (rows 21 33 13 29 16 32) }] }

theorem profile13_node235 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,18] 6 34 profile13_node235_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,18] 6 34 profile13_node235_cert).mp (by decide +kernel))

def profile13_node236_cert : CutBound 6 := { lost := (rows 0 0 16 17 0 0), upper := (rows 21 35 13 42 18 50), lower := (rows 21 35 13 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 26 42), good := (rows 20 58 60 58 16 32) },{ target := 4, region := (rows 1 2 6 10 0 32), good := (rows 5 47 13 46 0 32) }] }

theorem profile13_node236 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,34] 6 18 profile13_node236_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,34] 6 18 profile13_node236_cert).mp (by decide +kernel))

def profile13_node237_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 21 35 13 56 18 34), lower := (rows 21 35 13 56 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 20 58 12 56 16 32) },{ target := 1, region := (rows 9 0 12 8 16 32), good := (rows 21 33 13 61 16 32) }] }

theorem profile13_node237 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,48] 6 2 profile13_node237_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9,48] 6 2 profile13_node237_cert).mp (by decide +kernel))

def profile13_node234_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node234_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node234 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,9] 6 (by decide) (choices 2) [18,34,48] profile13_node234_route profile13_node234_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node235
  · exact profile13_node236
  · exact profile13_node237

def profile13_node239_cert : CutBound 6 := { lost := (rows 2 0 1 0 0 0), upper := (rows 21 35 14 11 48 48), lower := (rows 21 35 14 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 63 63), good := (rows 52 50 62 62 48 48) },{ target := 1, region := (rows 5 0 4 8 63 63), good := (rows 53 49 61 57 48 48) }] }

theorem profile13_node239 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,3] 6 48 profile13_node239_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,3] 6 48 profile13_node239_cert).mp (by decide +kernel))

def profile13_node240_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 21 35 14 25 50 34), lower := (rows 21 35 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 29 41 12 25 16 32) },{ target := 4, region := (rows 1 11 12 8 0 47), good := (rows 39 35 46 47 0 32) }] }

theorem profile13_node240 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,17] 6 34 profile13_node240_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,17] 6 34 profile13_node240_cert).mp (by decide +kernel))

def profile13_node241_cert : CutBound 6 := { lost := (rows 2 0 1 0 0 0), upper := (rows 21 35 14 26 49 33), lower := (rows 21 35 14 26 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 20 34 14 30 16 32) },{ target := 1, region := (rows 5 0 4 8 23 39), good := (rows 53 49 61 56 16 32) }] }

theorem profile13_node241 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,18] 6 33 profile13_node241_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,18] 6 33 profile13_node241_cert).mp (by decide +kernel))

def profile13_node242_cert : CutBound 6 := { lost := (rows 0 16 16 18 0 0), upper := (rows 21 35 14 41 18 50), lower := (rows 21 35 14 41 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 16 32), good := (rows 21 41 12 41 16 32) },{ target := 4, region := (rows 1 10 14 10 0 32), good := (rows 5 47 14 47 0 32) }] }

theorem profile13_node242 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,33] 6 18 profile13_node242_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,33] 6 18 profile13_node242_cert).mp (by decide +kernel))

def profile13_node243_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 21 35 14 42 17 49), lower := (rows 21 35 14 42 16 32), losses := [{ target := 0, region := (rows 0 2 14 10 16 32), good := (rows 20 46 14 46 16 32) }] }

theorem profile13_node243 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,34] 6 17 profile13_node243_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,34] 6 17 profile13_node243_cert).mp (by decide +kernel))

def profile13_node244_cert : CutBound 6 := { lost := (rows 32 16 0 0 0 0), upper := (rows 21 35 14 56 19 35), lower := (rows 21 35 14 56 16 32), losses := [{ target := 4, region := (rows 1 3 4 8 0 35), good := (rows 39 35 46 40 0 32) },{ target := 5, region := (rows 5 2 4 8 22 0), good := (rows 21 19 31 24 16 0) }] }

theorem profile13_node244 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,48] 6 3 profile13_node244_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10,48] 6 3 profile13_node244_cert).mp (by decide +kernel))

def profile13_node238_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node238_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node238 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,10] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node238_route profile13_node238_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node239
  · exact profile13_node240
  · exact profile13_node241
  · exact profile13_node242
  · exact profile13_node243
  · exact profile13_node244

def profile13_node245_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 21 35 21 42 58 42), lower := (rows 21 35 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 20 58 20 8 16 32) },{ target := 1, region := (rows 21 0 21 8 16 32), good := (rows 21 37 21 8 21 32) }] }

theorem profile13_node245 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,17] 6 42 profile13_node245_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,17] 6 42 profile13_node245_cert).mp (by decide +kernel))

def profile13_node246_cert : CutBound 6 := { lost := (rows 2 16 0 16 0 0), upper := (rows 21 35 22 43 59 43), lower := (rows 21 35 22 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 33 21 8 16 32) },{ target := 4, region := (rows 1 3 4 11 0 35), good := (rows 47 43 46 8 0 32) }] }

theorem profile13_node246 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,18] 6 43 profile13_node246_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,18] 6 43 profile13_node246_cert).mp (by decide +kernel))

def profile13_node247_cert : CutBound 6 := { lost := (rows 2 16 0 16 0 0), upper := (rows 21 35 28 43 51 35), lower := (rows 21 35 28 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 33 29 8 16 32) },{ target := 4, region := (rows 1 3 4 11 0 35), good := (rows 47 43 12 8 0 32) }] }

theorem profile13_node247 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,24] 6 35 profile13_node247_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,24] 6 35 profile13_node247_cert).mp (by decide +kernel))

def profile13_node248_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 21 35 37 26 26 58), lower := (rows 21 35 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 20 58 36 8 16 32) },{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 21 37 37 8 16 32) }] }

theorem profile13_node248 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,33] 6 26 profile13_node248_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,33] 6 26 profile13_node248_cert).mp (by decide +kernel))

def profile13_node249_cert : CutBound 6 := { lost := (rows 0 0 17 0 0 0), upper := (rows 21 35 38 27 27 59), lower := (rows 21 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 38 38 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 5 39 38 8 0 32) }] }

theorem profile13_node249 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,34] 6 27 profile13_node249_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,34] 6 27 profile13_node249_cert).mp (by decide +kernel))

def profile13_node251_cert : CutBound 6 := { lost := (rows 0 0 17 16 0 0), upper := (rows 21 35 44 11 18 50), lower := (rows 21 35 44 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 26 42), good := (rows 20 50 60 62 16 32) },{ target := 4, region := (rows 1 2 6 10 0 32), good := (rows 5 47 44 15 0 32) }] }

theorem profile13_node251 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,3] 6 18 profile13_node251_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,3] 6 18 profile13_node251_cert).mp (by decide +kernel))

def profile13_node252_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 21 35 44 25 18 34), lower := (rows 21 35 44 25 16 32), losses := [{ target := 1, region := (rows 1 0 6 9 16 32), good := (rows 29 45 44 25 16 32) }] }

theorem profile13_node252 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,17] 6 2 profile13_node252_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,17] 6 2 profile13_node252_cert).mp (by decide +kernel))

def profile13_node253_cert : CutBound 6 := { lost := (rows 0 16 16 0 0 0), upper := (rows 21 35 44 26 19 35), lower := (rows 21 35 44 26 16 32), losses := [{ target := 4, region := (rows 1 3 12 8 0 35), good := (rows 39 35 44 46 0 32) }] }

theorem profile13_node253 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,18] 6 3 profile13_node253_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40,18] 6 3 profile13_node253_cert).mp (by decide +kernel))

def profile13_node250_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 48 => 5 | _ => 0

def profile13_node250_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node250 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,40] 6 (by decide) (choices 2) [3,17,18] profile13_node250_route profile13_node250_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node251
  · exact profile13_node252
  · exact profile13_node253

def profile13_node254_cert : CutBound 6 := { lost := (rows 2 16 0 16 0 0), upper := (rows 21 35 52 11 27 43), lower := (rows 21 35 52 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 33 53 8 16 32) },{ target := 4, region := (rows 1 3 4 11 0 35), good := (rows 47 43 36 8 0 32) }] }

theorem profile13_node254 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,48] 6 11 profile13_node254_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33,48] 6 11 profile13_node254_cert).mp (by decide +kernel))

def profile13_node232_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node232_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node232 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,33] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile13_node232_route profile13_node232_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node233
  · exact profile13_node234
  · exact profile13_node238
  · exact profile13_node245
  · exact profile13_node246
  · exact profile13_node247
  · exact profile13_node248
  · exact profile13_node249
  · exact profile13_node250
  · exact profile13_node254

def profile13_node257_cert : CutBound 6 := { lost := (rows 2 1 0 0 0 0), upper := (rows 21 42 7 11 48 48), lower := (rows 21 42 7 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 63 63), good := (rows 52 58 54 58 48 48) },{ target := 1, region := (rows 5 0 4 8 63 63), good := (rows 53 56 53 57 48 48) }] }

theorem profile13_node257 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,3] 6 48 profile13_node257_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,3] 6 48 profile13_node257_cert).mp (by decide +kernel))

def profile13_node258_cert : CutBound 6 := { lost := (rows 0 1 0 2 0 0), upper := (rows 21 42 7 25 50 34), lower := (rows 21 42 7 25 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 30 46), good := (rows 52 58 54 58 16 32) },{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 29 40 13 25 16 32) }] }

theorem profile13_node258 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,17] 6 34 profile13_node258_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,17] 6 34 profile13_node258_cert).mp (by decide +kernel))

def profile13_node259_cert : CutBound 6 := { lost := (rows 34 0 32 0 0 0), upper := (rows 21 42 7 26 49 33), lower := (rows 21 42 7 26 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 21 37), good := (rows 53 40 53 24 16 32) },{ target := 5, region := (rows 9 2 14 8 16 0), good := (rows 21 15 7 31 16 0) }] }

theorem profile13_node259 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,18] 6 33 profile13_node259_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,18] 6 33 profile13_node259_cert).mp (by decide +kernel))


#print axioms profile13_node259
end Delivery.SmallBudgetTenFinite6
