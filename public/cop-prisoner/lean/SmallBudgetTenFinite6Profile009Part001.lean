import SmallBudgetTenFinite6Profile009Part000

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile9_node131_cert : CutBound 6 := { lost := (rows 0 32 32 1 1 0), upper := (rows 25 7 7 46 54 32), lower := (rows 25 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 56 62 62 40 48 32) },{ target := 5, region := (rows 1 7 7 8 16 0), good := (rows 31 7 7 8 16 0) }] }

theorem profile9_node131 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,3] 6 38 profile9_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,3] 6 38 profile9_node131_cert).mp (by decide +kernel))

def profile9_node132_cert : CutBound 6 := { lost := (rows 0 0 2 1 1 0), upper := (rows 25 7 37 46 54 32), lower := (rows 25 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 56 62 36 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 61 37 37 40 48 32) }] }

theorem profile9_node132 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,33] 6 38 profile9_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,33] 6 38 profile9_node132_cert).mp (by decide +kernel))

def profile9_node134_cert : CutBound 6 := { lost := (rows 2 0 1 0 3 0), upper := (rows 25 7 38 11 52 32), lower := (rows 25 7 38 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 31 63), good := (rows 60 54 54 62 48 32) },{ target := 1, region := (rows 9 0 4 8 22 63), good := (rows 57 53 52 57 48 32) }] }

theorem profile9_node134 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,3] 6 36 profile9_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,3] 6 36 profile9_node134_cert).mp (by decide +kernel))

def profile9_node135_cert : CutBound 6 := { lost := (rows 0 0 1 2 1 0), upper := (rows 25 7 38 13 50 32), lower := (rows 25 7 38 13 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 63), good := (rows 56 54 54 60 48 32) },{ target := 1, region := (rows 1 0 4 10 16 63), good := (rows 57 45 44 45 48 32) }] }

theorem profile9_node135 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,5] 6 34 profile9_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,5] 6 34 profile9_node135_cert).mp (by decide +kernel))

def profile9_node136_cert : CutBound 6 := { lost := (rows 2 0 1 1 2 0), upper := (rows 25 7 38 14 49 32), lower := (rows 25 7 38 14 16 32), losses := [{ target := 0, region := (rows 0 2 14 14 16 63), good := (rows 60 46 46 46 48 32) },{ target := 1, region := (rows 9 0 4 8 27 63), good := (rows 57 53 52 61 48 32) }] }

theorem profile9_node136 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,6] 6 33 profile9_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,6] 6 33 profile9_node136_cert).mp (by decide +kernel))

def profile9_node137_cert : CutBound 6 := { lost := (rows 2 0 1 2 1 0), upper := (rows 25 7 38 41 22 32), lower := (rows 25 7 38 41 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 63), good := (rows 56 54 54 40 48 32) },{ target := 1, region := (rows 17 0 4 27 16 63), good := (rows 57 45 44 41 57 32) }] }

theorem profile9_node137 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,33] 6 6 profile9_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,33] 6 6 profile9_node137_cert).mp (by decide +kernel))

def profile9_node138_cert : CutBound 6 := { lost := (rows 2 0 1 1 2 0), upper := (rows 25 7 38 42 21 32), lower := (rows 25 7 38 42 16 32), losses := [{ target := 0, region := (rows 0 2 14 14 16 63), good := (rows 60 46 46 46 48 32) },{ target := 1, region := (rows 9 0 4 8 18 63), good := (rows 57 53 52 57 48 32) }] }

theorem profile9_node138 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,34] 6 5 profile9_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,34] 6 5 profile9_node138_cert).mp (by decide +kernel))

def profile9_node139_cert : CutBound 6 := { lost := (rows 0 0 1 3 0 0), upper := (rows 25 7 38 44 19 32), lower := (rows 25 7 38 44 16 32), losses := [{ target := 0, region := (rows 0 2 6 14 16 63), good := (rows 56 46 46 44 48 32) },{ target := 1, region := (rows 1 0 4 14 16 63), good := (rows 57 45 44 44 48 32) }] }

theorem profile9_node139 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,36] 6 3 profile9_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34,36] 6 3 profile9_node139_cert).mp (by decide +kernel))

def profile9_node133_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node133_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node133 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5,34] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node133_route profile9_node133_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node134
  · exact profile9_node135
  · exact profile9_node136
  · exact profile9_node137
  · exact profile9_node138
  · exact profile9_node139

def profile9_node130_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node130_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node130 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,5] 6 (by decide) (choices 2) [3,33,34] profile9_node130_route profile9_node130_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node131
  · exact profile9_node132
  · exact profile9_node133

def profile9_node141_cert : CutBound 6 := { lost := (rows 0 4 0 1 1 0), upper := (rows 25 35 7 46 54 32), lower := (rows 25 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 63), good := (rows 56 34 62 40 48 32) },{ target := 2, region := (rows 1 7 0 8 16 63), good := (rows 59 35 35 40 48 32) }] }

theorem profile9_node141 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,3] 6 38 profile9_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,3] 6 38 profile9_node141_cert).mp (by decide +kernel))

def profile9_node143_cert : CutBound 6 := { lost := (rows 0 4 2 0 1 0), upper := (rows 25 35 37 14 22 32), lower := (rows 25 35 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 24 63), good := (rows 56 34 36 62 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 61 37 37 44 48 32) },{ target := 2, region := (rows 1 7 0 8 16 63), good := (rows 59 35 35 42 48 32) }] }

theorem profile9_node143 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,33,6] 6 6 profile9_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,33,6] 6 6 profile9_node143_cert).mp (by decide +kernel))

def profile9_node142_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile9_node142_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node142 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,33] 6 (by decide) (choices 2) [6] profile9_node142_route profile9_node142_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node143

def profile9_node144_cert : CutBound 6 := { lost := (rows 32 4 1 32 32 0), upper := (rows 25 35 38 15 23 32), lower := (rows 25 35 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 56 38 38 40 48 32) },{ target := 2, region := (rows 1 3 0 8 16 63), good := (rows 59 35 34 40 48 32) },{ target := 5, region := (rows 5 2 4 12 20 0), good := (rows 25 3 31 8 16 0) }] }

theorem profile9_node144 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,34] 6 7 profile9_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33,34] 6 7 profile9_node144_cert).mp (by decide +kernel))

def profile9_node140_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node140_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node140 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,33] 6 (by decide) (choices 2) [3,33,34] profile9_node140_route profile9_node140_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node141
  · exact profile9_node142
  · exact profile9_node144

def profile9_node147_cert : CutBound 6 := { lost := (rows 2 1 0 0 3 0), upper := (rows 25 38 7 11 52 32), lower := (rows 25 38 7 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 56 54 54 58 48 32) },{ target := 1, region := (rows 9 0 4 8 22 63), good := (rows 57 52 53 57 48 32) }] }

theorem profile9_node147 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,3] 6 36 profile9_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,3] 6 36 profile9_node147_cert).mp (by decide +kernel))

def profile9_node148_cert : CutBound 6 := { lost := (rows 0 1 0 2 1 0), upper := (rows 25 38 7 13 50 32), lower := (rows 25 38 7 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 63), good := (rows 58 54 54 62 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 57 44 45 45 48 32) }] }

theorem profile9_node148 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,5] 6 34 profile9_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,5] 6 34 profile9_node148_cert).mp (by decide +kernel))

def profile9_node149_cert : CutBound 6 := { lost := (rows 2 1 0 1 2 0), upper := (rows 25 38 7 14 49 32), lower := (rows 25 38 7 14 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 63), good := (rows 58 46 46 46 48 32) },{ target := 1, region := (rows 9 0 4 8 29 63), good := (rows 57 52 53 61 48 32) }] }

theorem profile9_node149 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,6] 6 33 profile9_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,6] 6 33 profile9_node149_cert).mp (by decide +kernel))

def profile9_node150_cert : CutBound 6 := { lost := (rows 2 1 0 2 1 0), upper := (rows 25 38 7 41 22 32), lower := (rows 25 38 7 41 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 56 54 54 40 48 32) },{ target := 1, region := (rows 17 0 4 29 16 63), good := (rows 57 44 45 41 57 32) }] }

theorem profile9_node150 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,33] 6 6 profile9_node150_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,33] 6 6 profile9_node150_cert).mp (by decide +kernel))

def profile9_node151_cert : CutBound 6 := { lost := (rows 0 1 0 1 2 0), upper := (rows 25 38 7 42 21 32), lower := (rows 25 38 7 42 16 32), losses := [{ target := 0, region := (rows 0 6 4 14 16 63), good := (rows 56 46 46 42 48 32) },{ target := 1, region := (rows 1 0 4 8 20 63), good := (rows 57 52 53 40 48 32) }] }

theorem profile9_node151 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,34] 6 5 profile9_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,34] 6 5 profile9_node151_cert).mp (by decide +kernel))

def profile9_node152_cert : CutBound 6 := { lost := (rows 0 1 0 3 0 0), upper := (rows 25 38 7 44 19 32), lower := (rows 25 38 7 44 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 63), good := (rows 58 46 46 46 48 32) },{ target := 1, region := (rows 1 0 4 14 16 63), good := (rows 57 44 45 44 48 32) }] }

theorem profile9_node152 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,36] 6 3 profile9_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3,36] 6 3 profile9_node152_cert).mp (by decide +kernel))

def profile9_node146_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node146_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node146 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,3] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node146_route profile9_node146_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node147
  · exact profile9_node148
  · exact profile9_node149
  · exact profile9_node150
  · exact profile9_node151
  · exact profile9_node152

def profile9_node153_cert : CutBound 6 := { lost := (rows 32 1 2 32 32 0), upper := (rows 25 38 37 15 23 32), lower := (rows 25 38 37 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 56 38 38 40 48 32) },{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 61 36 37 40 48 32) },{ target := 5, region := (rows 3 2 4 10 18 0), good := (rows 25 31 5 8 16 0) }] }

theorem profile9_node153 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,33] 6 7 profile9_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,33] 6 7 profile9_node153_cert).mp (by decide +kernel))

def profile9_node154_cert : CutBound 6 := { lost := (rows 32 1 1 32 32 0), upper := (rows 25 38 38 15 23 32), lower := (rows 25 38 38 8 16 32), losses := [{ target := 0, region := (rows 0 63 63 8 16 63), good := (rows 62 38 38 46 54 38) },{ target := 5, region := (rows 7 2 4 14 22 0), good := (rows 25 31 31 8 16 0) }] }

theorem profile9_node154 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,34] 6 7 profile9_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36,34] 6 7 profile9_node154_cert).mp (by decide +kernel))

def profile9_node145_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node145_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node145 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24,36] 6 (by decide) (choices 2) [3,33,34] profile9_node145_route profile9_node145_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node146
  · exact profile9_node153
  · exact profile9_node154

def profile9_node129_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node129_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node129 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [24] 6 (by decide) (choices 2) [5,33,36] profile9_node129_route profile9_node129_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node130
  · exact profile9_node140
  · exact profile9_node145

def profile9_node157_cert : CutBound 6 := { lost := (rows 0 0 0 3 3 0), upper := (rows 35 7 7 60 60 32), lower := (rows 35 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 58 62 62 40 48 32) },{ target := 1, region := (rows 1 0 4 14 22 63), good := (rows 57 61 61 40 48 32) }] }

theorem profile9_node157 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,3] 6 60 profile9_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,3] 6 60 profile9_node157_cert).mp (by decide +kernel))

def profile9_node158_cert : CutBound 6 := { lost := (rows 4 0 0 1 1 0), upper := (rows 35 7 13 62 54 32), lower := (rows 35 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 44 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 41 40 48 32) }] }

theorem profile9_node158 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,9] 6 54 profile9_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,9] 6 54 profile9_node158_cert).mp (by decide +kernel))

def profile9_node159_cert : CutBound 6 := { lost := (rows 4 0 0 2 2 0), upper := (rows 35 7 14 61 53 32), lower := (rows 35 7 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 35 43 40 48 32) }] }

theorem profile9_node159 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,10] 6 53 profile9_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,10] 6 53 profile9_node159_cert).mp (by decide +kernel))

def profile9_node161_cert : CutBound 6 := { lost := (rows 0 0 3 0 3 0), upper := (rows 35 7 28 11 52 32), lower := (rows 35 7 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 30 63), good := (rows 50 54 60 62 48 32) },{ target := 1, region := (rows 1 0 12 8 30 63), good := (rows 49 53 60 61 48 32) }] }

theorem profile9_node161 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,3] 6 36 profile9_node161_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,3] 6 36 profile9_node161_cert).mp (by decide +kernel))

def profile9_node162_cert : CutBound 6 := { lost := (rows 0 0 1 2 1 0), upper := (rows 35 7 28 13 50 32), lower := (rows 35 7 28 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 63), good := (rows 50 54 60 60 48 32) },{ target := 1, region := (rows 1 0 4 10 16 63), good := (rows 41 45 60 45 48 32) }] }

theorem profile9_node162 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,5] 6 34 profile9_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,5] 6 34 profile9_node162_cert).mp (by decide +kernel))

def profile9_node163_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 35 7 28 14 49 32), lower := (rows 35 7 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 63), good := (rows 42 46 60 46 48 32) },{ target := 1, region := (rows 1 0 12 8 19 63), good := (rows 49 53 60 60 48 32) }] }

theorem profile9_node163 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,6] 6 33 profile9_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,6] 6 33 profile9_node163_cert).mp (by decide +kernel))

def profile9_node164_cert : CutBound 6 := { lost := (rows 4 0 0 6 1 0), upper := (rows 35 7 28 41 22 32), lower := (rows 35 7 28 41 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 18 63), good := (rows 50 54 60 40 48 32) },{ target := 1, region := (rows 1 0 4 11 16 63), good := (rows 41 45 60 41 48 32) },{ target := 2, region := (rows 3 2 0 11 16 63), good := (rows 43 43 56 41 48 32) }] }

theorem profile9_node164 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,33] 6 6 profile9_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,33] 6 6 profile9_node164_cert).mp (by decide +kernel))

def profile9_node165_cert : CutBound 6 := { lost := (rows 0 0 2 1 2 0), upper := (rows 35 7 28 42 21 32), lower := (rows 35 7 28 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 16 63), good := (rows 42 46 60 42 48 32) },{ target := 1, region := (rows 1 0 12 8 18 63), good := (rows 49 53 60 60 48 32) }] }

theorem profile9_node165 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,34] 6 5 profile9_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,34] 6 5 profile9_node165_cert).mp (by decide +kernel))

def profile9_node166_cert : CutBound 6 := { lost := (rows 0 0 3 3 0 0), upper := (rows 35 7 28 44 19 32), lower := (rows 35 7 28 44 16 32), losses := [{ target := 0, region := (rows 0 2 20 30 16 63), good := (rows 42 46 60 44 60 32) },{ target := 1, region := (rows 1 0 20 30 16 63), good := (rows 41 45 60 44 60 32) }] }

theorem profile9_node166 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,36] 6 3 profile9_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24,36] 6 3 profile9_node166_cert).mp (by decide +kernel))

def profile9_node160_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node160_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node160 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,24] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node160_route profile9_node160_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node161
  · exact profile9_node162
  · exact profile9_node163
  · exact profile9_node164
  · exact profile9_node165
  · exact profile9_node166

def profile9_node167_cert : CutBound 6 := { lost := (rows 0 0 2 1 1 0), upper := (rows 35 7 37 30 30 32), lower := (rows 35 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 58 62 36 40 48 32) },{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 37 37 40 48 32) }] }

theorem profile9_node167 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,33] 6 30 profile9_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,33] 6 30 profile9_node167_cert).mp (by decide +kernel))

def profile9_node168_cert : CutBound 6 := { lost := (rows 0 0 1 2 2 0), upper := (rows 35 7 38 29 29 32), lower := (rows 35 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 38 38 40 48 32) },{ target := 1, region := (rows 1 0 4 10 18 63), good := (rows 57 61 60 40 48 32) }] }

theorem profile9_node168 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,34] 6 29 profile9_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,34] 6 29 profile9_node168_cert).mp (by decide +kernel))

def profile9_node169_cert : CutBound 6 := { lost := (rows 4 0 3 0 0 0), upper := (rows 35 7 44 31 23 32), lower := (rows 35 7 44 8 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 63), good := (rows 34 38 44 44 48 32) },{ target := 1, region := (rows 1 0 12 8 16 63), good := (rows 33 37 44 44 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 40 40 48 32) }] }

theorem profile9_node169 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,40] 6 23 profile9_node169_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5,40] 6 23 profile9_node169_cert).mp (by decide +kernel))

def profile9_node156_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile9_node156_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile9_node156 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,5] 6 (by decide) (choices 2) [3,9,10,24,33,34,40] profile9_node156_route profile9_node156_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node157
  · exact profile9_node158
  · exact profile9_node159
  · exact profile9_node160
  · exact profile9_node167
  · exact profile9_node168
  · exact profile9_node169

def profile9_node171_cert : CutBound 6 := { lost := (rows 0 0 0 3 3 0), upper := (rows 35 11 7 60 52 32), lower := (rows 35 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 63), good := (rows 34 42 62 40 48 32) },{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 33 41 61 40 48 32) }] }

theorem profile9_node171 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,3] 6 52 profile9_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,3] 6 52 profile9_node171_cert).mp (by decide +kernel))

def profile9_node173_cert : CutBound 6 := { lost := (rows 0 0 2 0 3 0), upper := (rows 35 11 21 14 52 32), lower := (rows 35 11 21 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 28 63), good := (rows 34 58 52 62 48 32) },{ target := 1, region := (rows 1 0 7 8 31 63), good := (rows 53 61 53 60 48 32) }] }

theorem profile9_node173 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,6] 6 36 profile9_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,6] 6 36 profile9_node173_cert).mp (by decide +kernel))

def profile9_node174_cert : CutBound 6 := { lost := (rows 0 0 2 1 3 0), upper := (rows 35 11 21 42 20 32), lower := (rows 35 11 21 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 11 20 63), good := (rows 42 42 60 42 48 32) },{ target := 1, region := (rows 1 0 7 8 31 63), good := (rows 53 61 53 60 48 32) }] }

theorem profile9_node174 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,34] 6 4 profile9_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,34] 6 4 profile9_node174_cert).mp (by decide +kernel))

def profile9_node175_cert : CutBound 6 := { lost := (rows 4 4 0 3 0 0), upper := (rows 35 11 21 44 22 32), lower := (rows 35 11 21 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 63), good := (rows 34 42 60 44 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 33 41 61 44 48 32) },{ target := 2, region := (rows 11 10 0 8 16 63), good := (rows 35 43 49 43 48 32) }] }

theorem profile9_node175 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,36] 6 6 profile9_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17,36] 6 6 profile9_node175_cert).mp (by decide +kernel))

def profile9_node172_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node172_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node172 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,17] 6 (by decide) (choices 2) [6,34,36] profile9_node172_route profile9_node172_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node173
  · exact profile9_node174
  · exact profile9_node175

def profile9_node177_cert : CutBound 6 := { lost := (rows 0 0 1 0 3 0), upper := (rows 35 11 22 13 52 32), lower := (rows 35 11 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 63), good := (rows 54 62 54 60 48 32) },{ target := 1, region := (rows 1 0 4 8 28 63), good := (rows 33 57 52 61 48 32) }] }

theorem profile9_node177 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,5] 6 36 profile9_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,5] 6 36 profile9_node177_cert).mp (by decide +kernel))

def profile9_node178_cert : CutBound 6 := { lost := (rows 0 0 1 2 3 0), upper := (rows 35 11 22 41 20 32), lower := (rows 35 11 22 41 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 63), good := (rows 54 62 54 60 48 32) },{ target := 1, region := (rows 1 0 4 11 20 63), good := (rows 41 41 60 41 48 32) }] }

theorem profile9_node178 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,33] 6 4 profile9_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,33] 6 4 profile9_node178_cert).mp (by decide +kernel))

def profile9_node179_cert : CutBound 6 := { lost := (rows 4 4 0 3 0 0), upper := (rows 35 11 22 44 21 32), lower := (rows 35 11 22 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 63), good := (rows 34 42 62 44 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 33 41 60 44 48 32) },{ target := 2, region := (rows 15 10 0 8 16 63), good := (rows 35 43 51 43 48 32) }] }

theorem profile9_node179 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,36] 6 5 profile9_node179_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18,36] 6 5 profile9_node179_cert).mp (by decide +kernel))

def profile9_node176_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node176_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node176 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,18] 6 (by decide) (choices 2) [5,33,36] profile9_node176_route profile9_node176_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node177
  · exact profile9_node178
  · exact profile9_node179

def profile9_node180_cert : CutBound 6 := { lost := (rows 4 4 2 0 0 0), upper := (rows 35 11 37 30 22 32), lower := (rows 35 11 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 16 63), good := (rows 37 45 37 40 48 32) },{ target := 2, region := (rows 11 10 0 8 16 63), good := (rows 35 43 33 43 48 32) }] }

theorem profile9_node180 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,33] 6 22 profile9_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,33] 6 22 profile9_node180_cert).mp (by decide +kernel))

def profile9_node181_cert : CutBound 6 := { lost := (rows 4 4 1 0 0 0), upper := (rows 35 11 38 29 21 32), lower := (rows 35 11 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 46 38 40 48 32) },{ target := 2, region := (rows 15 10 0 8 16 63), good := (rows 35 43 35 43 48 32) }] }

theorem profile9_node181 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,34] 6 21 profile9_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,34] 6 21 profile9_node181_cert).mp (by decide +kernel))

def profile9_node182_cert : CutBound 6 := { lost := (rows 4 4 3 0 0 0), upper := (rows 35 11 52 15 23 32), lower := (rows 35 11 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 20 8 16 63), good := (rows 34 42 52 40 52 32) },{ target := 1, region := (rows 1 0 20 8 16 63), good := (rows 33 41 52 40 52 32) },{ target := 2, region := (rows 11 10 0 8 16 63), good := (rows 35 43 48 43 48 32) }] }

theorem profile9_node182 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,48] 6 7 profile9_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9,48] 6 7 profile9_node182_cert).mp (by decide +kernel))

def profile9_node170_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node170_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node170 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node170_route profile9_node170_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node171
  · exact profile9_node172
  · exact profile9_node176
  · exact profile9_node180
  · exact profile9_node181
  · exact profile9_node182

def profile9_node184_cert : CutBound 6 := { lost := (rows 4 0 0 2 2 0), upper := (rows 35 14 7 61 53 32), lower := (rows 35 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 33 60 61 40 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 43 35 40 48 32) }] }

theorem profile9_node184 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,3] 6 53 profile9_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,3] 6 53 profile9_node184_cert).mp (by decide +kernel))

def profile9_node186_cert : CutBound 6 := { lost := (rows 0 0 2 0 3 0), upper := (rows 35 14 21 11 52 32), lower := (rows 35 14 21 11 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 22 63), good := (rows 50 62 52 58 48 32) },{ target := 1, region := (rows 1 0 13 8 31 63), good := (rows 53 60 53 61 48 32) }] }

theorem profile9_node186 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,3] 6 36 profile9_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,3] 6 36 profile9_node186_cert).mp (by decide +kernel))

def profile9_node187_cert : CutBound 6 := { lost := (rows 0 1 0 2 1 0), upper := (rows 35 14 21 13 50 32), lower := (rows 35 14 21 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 63), good := (rows 50 62 52 62 48 32) },{ target := 1, region := (rows 1 0 4 12 16 63), good := (rows 33 44 61 45 48 32) }] }

theorem profile9_node187 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,5] 6 34 profile9_node187_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,5] 6 34 profile9_node187_cert).mp (by decide +kernel))

def profile9_node188_cert : CutBound 6 := { lost := (rows 0 1 2 1 2 0), upper := (rows 35 14 21 14 49 32), lower := (rows 35 14 21 14 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 63), good := (rows 42 46 62 46 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 53 60 53 60 48 32) }] }

theorem profile9_node188 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,6] 6 33 profile9_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,6] 6 33 profile9_node188_cert).mp (by decide +kernel))

def profile9_node189_cert : CutBound 6 := { lost := (rows 4 0 0 6 1 0), upper := (rows 35 14 21 41 22 32), lower := (rows 35 14 21 41 16 32), losses := [{ target := 0, region := (rows 0 2 4 8 18 63), good := (rows 50 62 52 40 48 32) },{ target := 1, region := (rows 1 0 4 13 16 63), good := (rows 41 44 61 41 48 32) },{ target := 2, region := (rows 3 2 0 15 16 63), good := (rows 43 43 57 41 48 32) }] }

theorem profile9_node189 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,33] 6 6 profile9_node189_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,33] 6 6 profile9_node189_cert).mp (by decide +kernel))

def profile9_node190_cert : CutBound 6 := { lost := (rows 0 1 2 1 2 0), upper := (rows 35 14 21 42 21 32), lower := (rows 35 14 21 42 16 32), losses := [{ target := 0, region := (rows 0 6 4 15 16 63), good := (rows 42 46 62 42 48 32) },{ target := 1, region := (rows 1 0 5 8 21 63), good := (rows 53 60 53 40 48 32) }] }

theorem profile9_node190 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,34] 6 5 profile9_node190_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,34] 6 5 profile9_node190_cert).mp (by decide +kernel))

def profile9_node191_cert : CutBound 6 := { lost := (rows 0 1 0 3 0 0), upper := (rows 35 14 21 44 19 32), lower := (rows 35 14 21 44 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 63), good := (rows 42 46 62 46 48 32) },{ target := 1, region := (rows 1 0 4 14 16 63), good := (rows 41 44 61 44 48 32) }] }

theorem profile9_node191 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,36] 6 3 profile9_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17,36] 6 3 profile9_node191_cert).mp (by decide +kernel))

def profile9_node185_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node185_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node185 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,17] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node185_route profile9_node185_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node186
  · exact profile9_node187
  · exact profile9_node188
  · exact profile9_node189
  · exact profile9_node190
  · exact profile9_node191

def profile9_node193_cert : CutBound 6 := { lost := (rows 4 1 0 0 6 0), upper := (rows 35 14 22 13 49 32), lower := (rows 35 14 22 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 34 46 54 46 48 32) },{ target := 1, region := (rows 1 0 4 8 25 63), good := (rows 49 60 52 61 48 32) },{ target := 2, region := (rows 7 2 0 8 31 63), good := (rows 51 59 51 57 48 32) }] }

theorem profile9_node193 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,5] 6 33 profile9_node193_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,5] 6 33 profile9_node193_cert).mp (by decide +kernel))

def profile9_node194_cert : CutBound 6 := { lost := (rows 4 0 0 6 0 0), upper := (rows 35 14 22 41 21 32), lower := (rows 35 14 22 41 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 63), good := (rows 41 44 52 41 48 32) },{ target := 2, region := (rows 7 2 0 15 16 63), good := (rows 43 43 59 41 48 32) }] }

theorem profile9_node194 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,33] 6 5 profile9_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,33] 6 5 profile9_node194_cert).mp (by decide +kernel))

def profile9_node195_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 35 14 22 44 17 32), lower := (rows 35 14 22 44 16 32), losses := [{ target := 0, region := (rows 0 30 20 30 16 63), good := (rows 42 46 62 46 62 32) }] }

theorem profile9_node195 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,36] 6 1 profile9_node195_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18,36] 6 1 profile9_node195_cert).mp (by decide +kernel))

def profile9_node192_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node192_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node192 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,18] 6 (by decide) (choices 2) [5,33,36] profile9_node192_route profile9_node192_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node193
  · exact profile9_node194
  · exact profile9_node195

def profile9_node196_cert : CutBound 6 := { lost := (rows 4 32 2 32 32 0), upper := (rows 35 14 37 31 23 32), lower := (rows 35 14 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 44 37 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 43 33 40 48 32) },{ target := 5, region := (rows 1 6 4 12 20 0), good := (rows 3 30 31 8 16 0) }] }

theorem profile9_node196 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,33] 6 23 profile9_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,33] 6 23 profile9_node196_cert).mp (by decide +kernel))

def profile9_node197_cert : CutBound 6 := { lost := (rows 4 1 1 0 0 0), upper := (rows 35 14 38 29 21 32), lower := (rows 35 14 38 8 16 32), losses := [{ target := 0, region := (rows 0 10 15 8 16 63), good := (rows 38 46 38 46 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 43 35 40 48 32) }] }

theorem profile9_node197 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,34] 6 21 profile9_node197_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,34] 6 21 profile9_node197_cert).mp (by decide +kernel))

def profile9_node198_cert : CutBound 6 := { lost := (rows 4 0 3 0 0 0), upper := (rows 35 14 52 15 23 32), lower := (rows 35 14 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 20 8 16 63), good := (rows 34 46 52 40 52 32) },{ target := 1, region := (rows 1 0 20 8 16 63), good := (rows 33 44 52 40 52 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 43 48 40 48 32) }] }

theorem profile9_node198 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,48] 6 7 profile9_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12,48] 6 7 profile9_node198_cert).mp (by decide +kernel))

def profile9_node183_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node183_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node183 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,12] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node183_route profile9_node183_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node184
  · exact profile9_node185
  · exact profile9_node192
  · exact profile9_node196
  · exact profile9_node197
  · exact profile9_node198

def profile9_node200_cert : CutBound 6 := { lost := (rows 4 0 0 2 2 0), upper := (rows 35 26 7 45 53 32), lower := (rows 35 26 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 63), good := (rows 33 56 61 40 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 59 35 40 48 32) }] }

theorem profile9_node200 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,3] 6 37 profile9_node200_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,3] 6 37 profile9_node200_cert).mp (by decide +kernel))

def profile9_node201_cert : CutBound 6 := { lost := (rows 4 32 2 32 32 0), upper := (rows 35 26 37 15 23 32), lower := (rows 35 26 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 63), good := (rows 37 56 37 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 59 33 40 48 32) },{ target := 5, region := (rows 1 6 4 12 20 0), good := (rows 3 26 31 8 16 0) }] }

theorem profile9_node201 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,33] 6 7 profile9_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,33] 6 7 profile9_node201_cert).mp (by decide +kernel))

def profile9_node203_cert : CutBound 6 := { lost := (rows 4 0 1 0 2 0), upper := (rows 35 26 38 13 21 32), lower := (rows 35 26 38 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 16 63), good := (rows 38 62 38 44 48 32) },{ target := 1, region := (rows 1 0 4 8 24 63), good := (rows 33 56 36 61 48 32) },{ target := 2, region := (rows 7 2 0 8 16 63), good := (rows 35 59 35 41 48 32) }] }

theorem profile9_node203 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,34,5] 6 5 profile9_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,34,5] 6 5 profile9_node203_cert).mp (by decide +kernel))

def profile9_node202_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile9_node202_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node202 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24,34] 6 (by decide) (choices 2) [5] profile9_node202_route profile9_node202_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile9_node203

def profile9_node199_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node199_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node199 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,24] 6 (by decide) (choices 2) [3,33,34] profile9_node199_route profile9_node199_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node200
  · exact profile9_node201
  · exact profile9_node202

def profile9_node204_cert : CutBound 6 := { lost := (rows 4 4 32 32 32 0), upper := (rows 35 35 31 31 31 32), lower := (rows 35 35 4 8 16 32), losses := [{ target := 2, region := (rows 63 63 0 8 16 63), good := (rows 35 35 35 43 51 35) },{ target := 5, region := (rows 1 2 7 11 19 0), good := (rows 31 31 4 8 16 0) }] }

theorem profile9_node204 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,33] 6 31 profile9_node204_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,33] 6 31 profile9_node204_cert).mp (by decide +kernel))

def profile9_node205_cert : CutBound 6 := { lost := (rows 4 1 32 32 32 0), upper := (rows 35 38 31 31 31 32), lower := (rows 35 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 34 38 38 40 48 32) },{ target := 2, region := (rows 3 2 0 8 16 63), good := (rows 35 35 32 40 48 32) },{ target := 5, region := (rows 1 2 5 9 17 0), good := (rows 31 6 4 8 16 0) }] }

theorem profile9_node205 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,36] 6 31 profile9_node205_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,36] 6 31 profile9_node205_cert).mp (by decide +kernel))

def profile9_node206_cert : CutBound 6 := { lost := (rows 4 5 0 0 0 0), upper := (rows 35 42 23 31 23 32), lower := (rows 35 42 4 8 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 63), good := (rows 34 42 36 42 48 32) },{ target := 2, region := (rows 11 10 0 8 16 63), good := (rows 35 43 32 43 48 32) }] }

theorem profile9_node206 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,40] 6 23 profile9_node206_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34,40] 6 23 profile9_node206_cert).mp (by decide +kernel))

def profile9_node155_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile9_node155_route : Route 6 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile9_node155 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [34] 6 (by decide) (choices 2) [5,9,12,24,33,36,40] profile9_node155_route profile9_node155_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node156
  · exact profile9_node170
  · exact profile9_node183
  · exact profile9_node199
  · exact profile9_node204
  · exact profile9_node205
  · exact profile9_node206

def profile9_node209_cert : CutBound 6 := { lost := (rows 2 0 0 1 1 0), upper := (rows 41 7 7 62 54 32), lower := (rows 41 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 63), good := (rows 40 62 62 40 48 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 37 37 41 48 32) }] }

theorem profile9_node209 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,3] 6 54 profile9_node209_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,3] 6 54 profile9_node209_cert).mp (by decide +kernel))

def profile9_node210_cert : CutBound 6 := { lost := (rows 2 0 0 1 1 0), upper := (rows 41 7 21 46 54 32), lower := (rows 41 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 40 62 52 40 48 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 37 53 41 48 32) }] }

theorem profile9_node210 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,17] 6 38 profile9_node210_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,17] 6 38 profile9_node210_cert).mp (by decide +kernel))

def profile9_node212_cert : CutBound 6 := { lost := (rows 2 0 1 0 3 0), upper := (rows 41 7 22 11 52 32), lower := (rows 41 7 22 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 31 63), good := (rows 60 54 54 62 48 32) },{ target := 1, region := (rows 9 0 4 8 22 63), good := (rows 41 53 52 57 48 32) }] }

theorem profile9_node212 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,3] 6 36 profile9_node212_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,3] 6 36 profile9_node212_cert).mp (by decide +kernel))

def profile9_node213_cert : CutBound 6 := { lost := (rows 2 0 1 2 1 0), upper := (rows 41 7 22 13 50 32), lower := (rows 41 7 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 63), good := (rows 40 54 54 60 48 32) },{ target := 1, region := (rows 15 0 4 14 16 63), good := (rows 41 45 61 45 48 32) }] }

theorem profile9_node213 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,5] 6 34 profile9_node213_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,5] 6 34 profile9_node213_cert).mp (by decide +kernel))

def profile9_node214_cert : CutBound 6 := { lost := (rows 2 0 0 1 2 0), upper := (rows 41 7 22 14 49 32), lower := (rows 41 7 22 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 40 46 62 46 48 32) },{ target := 1, region := (rows 9 0 4 8 27 63), good := (rows 57 53 52 61 48 32) }] }

theorem profile9_node214 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,6] 6 33 profile9_node214_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,6] 6 33 profile9_node214_cert).mp (by decide +kernel))

def profile9_node215_cert : CutBound 6 := { lost := (rows 2 0 1 2 1 0), upper := (rows 41 7 22 41 22 32), lower := (rows 41 7 22 41 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 63), good := (rows 40 54 54 40 48 32) },{ target := 1, region := (rows 63 0 4 63 16 63), good := (rows 41 45 61 41 57 41) }] }

theorem profile9_node215 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,33] 6 6 profile9_node215_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,33] 6 6 profile9_node215_cert).mp (by decide +kernel))

def profile9_node216_cert : CutBound 6 := { lost := (rows 2 0 0 1 2 0), upper := (rows 41 7 22 42 21 32), lower := (rows 41 7 22 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 40 46 62 42 48 32) },{ target := 1, region := (rows 9 0 4 8 18 63), good := (rows 41 53 52 57 48 32) }] }

theorem profile9_node216 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,34] 6 5 profile9_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,34] 6 5 profile9_node216_cert).mp (by decide +kernel))

def profile9_node217_cert : CutBound 6 := { lost := (rows 2 0 0 3 0 0), upper := (rows 41 7 22 44 19 32), lower := (rows 41 7 22 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 40 46 62 44 48 32) },{ target := 1, region := (rows 15 0 4 14 16 63), good := (rows 41 45 61 45 48 32) }] }

theorem profile9_node217 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,36] 6 3 profile9_node217_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18,36] 6 3 profile9_node217_cert).mp (by decide +kernel))

def profile9_node211_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node211_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node211 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,18] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node211_route profile9_node211_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node212
  · exact profile9_node213
  · exact profile9_node214
  · exact profile9_node215
  · exact profile9_node216
  · exact profile9_node217

def profile9_node218_cert : CutBound 6 := { lost := (rows 2 0 2 1 1 0), upper := (rows 41 7 37 30 22 32), lower := (rows 41 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 63), good := (rows 40 62 36 40 48 32) },{ target := 1, region := (rows 9 0 15 8 16 63), good := (rows 45 37 37 45 48 32) }] }

theorem profile9_node218 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,33] 6 22 profile9_node218_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,33] 6 22 profile9_node218_cert).mp (by decide +kernel))

def profile9_node219_cert : CutBound 6 := { lost := (rows 6 0 1 0 0 0), upper := (rows 41 7 38 31 23 32), lower := (rows 41 7 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 40 38 38 40 48 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 37 36 41 48 32) },{ target := 2, region := (rows 9 2 0 8 16 63), good := (rows 41 35 34 41 48 32) }] }

theorem profile9_node219 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,34] 6 23 profile9_node219_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,34] 6 23 profile9_node219_cert).mp (by decide +kernel))

def profile9_node220_cert : CutBound 6 := { lost := (rows 2 0 3 0 0 0), upper := (rows 41 7 52 15 23 32), lower := (rows 41 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 20 8 16 63), good := (rows 40 38 52 40 52 32) },{ target := 1, region := (rows 9 0 20 8 16 63), good := (rows 41 37 52 41 52 32) }] }

theorem profile9_node220 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,48] 6 7 profile9_node220_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5,48] 6 7 profile9_node220_cert).mp (by decide +kernel))

def profile9_node208_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node208_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node208 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile9_node208_route profile9_node208_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node209
  · exact profile9_node210
  · exact profile9_node211
  · exact profile9_node218
  · exact profile9_node219
  · exact profile9_node220

def profile9_node222_cert : CutBound 6 := { lost := (rows 2 0 0 1 1 0), upper := (rows 41 19 7 46 54 32), lower := (rows 41 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 63), good := (rows 40 50 62 40 48 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 49 37 41 48 32) }] }

theorem profile9_node222 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,3] 6 38 profile9_node222_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,3] 6 38 profile9_node222_cert).mp (by decide +kernel))

def profile9_node223_cert : CutBound 6 := { lost := (rows 6 0 2 0 0 0), upper := (rows 41 19 37 14 22 32), lower := (rows 41 19 37 8 16 32), losses := [{ target := 1, region := (rows 9 0 15 8 16 63), good := (rows 45 53 37 45 48 32) },{ target := 2, region := (rows 9 2 0 8 16 63), good := (rows 41 51 33 41 48 32) }] }

theorem profile9_node223 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,33] 6 6 profile9_node223_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,33] 6 6 profile9_node223_cert).mp (by decide +kernel))

def profile9_node224_cert : CutBound 6 := { lost := (rows 6 0 1 0 0 0), upper := (rows 41 19 38 15 23 32), lower := (rows 41 19 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 63), good := (rows 40 54 38 40 48 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 49 36 41 48 32) },{ target := 2, region := (rows 9 2 0 8 16 63), good := (rows 41 51 34 41 48 32) }] }

theorem profile9_node224 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,34] 6 7 profile9_node224_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17,34] 6 7 profile9_node224_cert).mp (by decide +kernel))

def profile9_node221_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node221_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node221 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,17] 6 (by decide) (choices 2) [3,33,34] profile9_node221_route profile9_node221_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node222
  · exact profile9_node223
  · exact profile9_node224

def profile9_node227_cert : CutBound 6 := { lost := (rows 2 1 0 0 3 0), upper := (rows 41 22 7 11 52 32), lower := (rows 41 22 7 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 40 54 54 58 48 32) },{ target := 1, region := (rows 9 0 4 8 22 63), good := (rows 41 52 53 57 48 32) }] }

theorem profile9_node227 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,3] 6 36 profile9_node227_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,3] 6 36 profile9_node227_cert).mp (by decide +kernel))

def profile9_node228_cert : CutBound 6 := { lost := (rows 2 1 0 2 1 0), upper := (rows 41 22 7 13 50 32), lower := (rows 41 22 7 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 63), good := (rows 58 54 54 62 48 32) },{ target := 1, region := (rows 15 0 4 14 16 63), good := (rows 41 61 45 45 48 32) }] }

theorem profile9_node228 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,5] 6 34 profile9_node228_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,5] 6 34 profile9_node228_cert).mp (by decide +kernel))

def profile9_node229_cert : CutBound 6 := { lost := (rows 2 0 0 1 2 0), upper := (rows 41 22 7 14 49 32), lower := (rows 41 22 7 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 40 62 46 46 48 32) },{ target := 1, region := (rows 9 0 4 8 29 63), good := (rows 57 52 53 61 48 32) }] }

theorem profile9_node229 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,6] 6 33 profile9_node229_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,6] 6 33 profile9_node229_cert).mp (by decide +kernel))

def profile9_node230_cert : CutBound 6 := { lost := (rows 2 1 0 2 1 0), upper := (rows 41 22 7 41 22 32), lower := (rows 41 22 7 41 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 63), good := (rows 40 54 54 40 48 32) },{ target := 1, region := (rows 63 0 4 63 16 63), good := (rows 41 61 45 41 57 41) }] }

theorem profile9_node230 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,33] 6 6 profile9_node230_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,33] 6 6 profile9_node230_cert).mp (by decide +kernel))

def profile9_node231_cert : CutBound 6 := { lost := (rows 2 0 0 1 2 0), upper := (rows 41 22 7 42 21 32), lower := (rows 41 22 7 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 40 62 46 42 48 32) },{ target := 1, region := (rows 9 0 4 8 20 63), good := (rows 41 52 53 41 48 32) }] }

theorem profile9_node231 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,34] 6 5 profile9_node231_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,34] 6 5 profile9_node231_cert).mp (by decide +kernel))

def profile9_node232_cert : CutBound 6 := { lost := (rows 2 0 0 3 0 0), upper := (rows 41 22 7 44 19 32), lower := (rows 41 22 7 44 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 63), good := (rows 40 62 46 44 48 32) },{ target := 1, region := (rows 15 0 4 14 16 63), good := (rows 41 61 45 45 48 32) }] }

theorem profile9_node232 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,36] 6 3 profile9_node232_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3,36] 6 3 profile9_node232_cert).mp (by decide +kernel))

def profile9_node226_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | _ => 0

def profile9_node226_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node226 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,3] 6 (by decide) (choices 2) [3,5,6,33,34,36] profile9_node226_route profile9_node226_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node227
  · exact profile9_node228
  · exact profile9_node229
  · exact profile9_node230
  · exact profile9_node231
  · exact profile9_node232

def profile9_node233_cert : CutBound 6 := { lost := (rows 6 0 2 0 0 0), upper := (rows 41 22 37 15 23 32), lower := (rows 41 22 37 8 16 32), losses := [{ target := 1, region := (rows 9 0 13 8 16 63), good := (rows 45 52 37 45 48 32) },{ target := 2, region := (rows 9 2 0 8 16 63), good := (rows 41 50 33 41 48 32) }] }

theorem profile9_node233 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,33] 6 7 profile9_node233_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,33] 6 7 profile9_node233_cert).mp (by decide +kernel))

def profile9_node234_cert : CutBound 6 := { lost := (rows 2 1 1 0 0 0), upper := (rows 41 22 38 15 23 32), lower := (rows 41 22 38 8 16 32), losses := [{ target := 0, region := (rows 0 18 22 8 16 63), good := (rows 40 54 38 40 54 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 52 36 41 48 32) }] }

theorem profile9_node234 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,34] 6 7 profile9_node234_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20,34] 6 7 profile9_node234_cert).mp (by decide +kernel))

def profile9_node225_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile9_node225_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node225 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,20] 6 (by decide) (choices 2) [3,33,34] profile9_node225_route profile9_node225_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node226
  · exact profile9_node233
  · exact profile9_node234

def profile9_node235_cert : CutBound 6 := { lost := (rows 6 4 0 0 0 0), upper := (rows 41 35 23 31 23 32), lower := (rows 41 35 4 8 16 32), losses := [{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 33 36 41 48 32) },{ target := 2, region := (rows 9 11 0 8 16 63), good := (rows 43 35 32 43 48 32) }] }

theorem profile9_node235 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,33] 6 23 profile9_node235_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,33] 6 23 profile9_node235_cert).mp (by decide +kernel))

def profile9_node236_cert : CutBound 6 := { lost := (rows 6 1 0 0 0 0), upper := (rows 41 38 23 31 23 32), lower := (rows 41 38 4 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 63), good := (rows 40 38 38 40 48 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 36 36 41 48 32) },{ target := 2, region := (rows 9 2 0 8 16 63), good := (rows 41 34 32 41 48 32) }] }

theorem profile9_node236 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,36] 6 23 profile9_node236_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,36] 6 23 profile9_node236_cert).mp (by decide +kernel))

def profile9_node237_cert : CutBound 6 := { lost := (rows 6 5 0 0 0 0), upper := (rows 41 50 7 15 23 32), lower := (rows 41 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 18 4 8 16 63), good := (rows 40 50 36 40 50 32) },{ target := 1, region := (rows 9 0 4 8 16 63), good := (rows 41 48 36 41 48 32) },{ target := 2, region := (rows 9 18 0 8 16 63), good := (rows 41 50 32 41 50 32) }] }

theorem profile9_node237 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,48] 6 7 profile9_node237_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40,48] 6 7 profile9_node237_cert).mp (by decide +kernel))

def profile9_node207_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile9_node207_route : Route 6 := (fun mask => (mask,id))

theorem profile9_node207 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [40] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile9_node207_route profile9_node207_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node208
  · exact profile9_node221
  · exact profile9_node225
  · exact profile9_node235
  · exact profile9_node236
  · exact profile9_node237

def profile9_node0_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile9_node0_route : Route 6 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 20 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile9_node0 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [] 6 (by decide) (choices 2) [6,10,24,34,40] profile9_node0_route profile9_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile9_node1
  · exact profile9_node57
  · exact profile9_node129
  · exact profile9_node155
  · exact profile9_node207

theorem profile9 : Upper (D (n:=6) [34,34,34,33,33,2]) (R (n:=6) [34,34,34,33,33,2]) [] 6 := profile9_node0


#print axioms profile9
end Delivery.SmallBudgetTenFinite6
