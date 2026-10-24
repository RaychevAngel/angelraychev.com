import SmallBudgetTenFinite6Profile010Part000

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile10_node115_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node115_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node115 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,20] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node115_route profile10_node115_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node116
  · exact profile10_node117
  · exact profile10_node118
  · exact profile10_node119
  · exact profile10_node126
  · exact profile10_node130

def profile10_node132_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 35 7 28 20 52), lower := (rows 11 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 10 34 62 8 16 32) }] }

theorem profile10_node132 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,3] 6 20 profile10_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,3] 6 20 profile10_node132_cert).mp (by decide +kernel))

def profile10_node134_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 35 21 14 20 52), lower := (rows 11 35 21 14 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 61 53 53 60 16 32) }] }

theorem profile10_node134 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,6] 6 20 profile10_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,6] 6 20 profile10_node134_cert).mp (by decide +kernel))

def profile10_node135_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 35 21 26 20 36), lower := (rows 11 35 21 26 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 61 53 53 60 16 32) }] }

theorem profile10_node135 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,18] 6 4 profile10_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,18] 6 4 profile10_node135_cert).mp (by decide +kernel))

def profile10_node136_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 35 21 28 22 38), lower := (rows 11 35 21 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 10 34 28 28 16 32) }] }

theorem profile10_node136 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,20] 6 6 profile10_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17,20] 6 6 profile10_node136_cert).mp (by decide +kernel))

def profile10_node133_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node133_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node133 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,17] 6 (by decide) (choices 2) [6,18,20] profile10_node133_route profile10_node133_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node134
  · exact profile10_node135
  · exact profile10_node136

def profile10_node138_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 35 22 13 20 52), lower := (rows 11 35 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 62 54 54 60 16 32) }] }

theorem profile10_node138 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,5] 6 20 profile10_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,5] 6 20 profile10_node138_cert).mp (by decide +kernel))

def profile10_node139_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 35 22 25 20 36), lower := (rows 11 35 22 25 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 62 54 54 60 16 32) }] }

theorem profile10_node139 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,17] 6 4 profile10_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,17] 6 4 profile10_node139_cert).mp (by decide +kernel))

def profile10_node140_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 35 22 28 21 37), lower := (rows 11 35 22 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 10 34 30 28 16 32) }] }

theorem profile10_node140 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,20] 6 5 profile10_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18,20] 6 5 profile10_node140_cert).mp (by decide +kernel))

def profile10_node137_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node137_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node137 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33,18] 6 (by decide) (choices 2) [5,17,20] profile10_node137_route profile10_node137_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node138
  · exact profile10_node139
  · exact profile10_node140

def profile10_node131_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node131_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node131 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,33] 6 (by decide) (choices 2) [3,17,18] profile10_node131_route profile10_node131_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node132
  · exact profile10_node133
  · exact profile10_node137

def profile10_node142_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 11 38 7 29 21 53), lower := (rows 11 38 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 9 60 61 8 16 32) }] }

theorem profile10_node142 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,3] 6 21 profile10_node142_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,3] 6 21 profile10_node142_cert).mp (by decide +kernel))

def profile10_node144_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 38 21 11 20 52), lower := (rows 11 38 21 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 58 54 54 58 16 32) }] }

theorem profile10_node144 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,3] 6 20 profile10_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,3] 6 20 profile10_node144_cert).mp (by decide +kernel))

def profile10_node145_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 38 21 13 18 50), lower := (rows 11 38 21 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 47), good := (rows 58 54 54 62 16 32) }] }

theorem profile10_node145 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,5] 6 18 profile10_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,5] 6 18 profile10_node145_cert).mp (by decide +kernel))

def profile10_node146_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 38 21 14 17 49), lower := (rows 11 38 21 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 10 46 20 14 16 32) }] }

theorem profile10_node146 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,6] 6 17 profile10_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,6] 6 17 profile10_node146_cert).mp (by decide +kernel))

def profile10_node147_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 38 21 25 22 38), lower := (rows 11 38 21 25 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 58 54 54 24 16 32) }] }

theorem profile10_node147 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,17] 6 6 profile10_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,17] 6 6 profile10_node147_cert).mp (by decide +kernel))

def profile10_node148_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 38 21 26 21 37), lower := (rows 11 38 21 26 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 21 37), good := (rows 61 52 53 24 16 32) }] }

theorem profile10_node148 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,18] 6 5 profile10_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,18] 6 5 profile10_node148_cert).mp (by decide +kernel))

def profile10_node149_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 38 21 28 19 35), lower := (rows 11 38 21 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 10 46 28 28 16 32) }] }

theorem profile10_node149 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,20] 6 3 profile10_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17,20] 6 3 profile10_node149_cert).mp (by decide +kernel))

def profile10_node143_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node143_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node143 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,17] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node143_route profile10_node143_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node144
  · exact profile10_node145
  · exact profile10_node146
  · exact profile10_node147
  · exact profile10_node148
  · exact profile10_node149

def profile10_node151_cert : CutBound 6 := { lost := (rows 16 0 0 16 0 0), upper := (rows 11 38 22 13 17 49), lower := (rows 11 38 22 13 16 32), losses := [{ target := 4, region := (rows 7 2 4 14 0 32), good := (rows 11 47 15 13 0 32) }] }

theorem profile10_node151 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,5] 6 17 profile10_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,5] 6 17 profile10_node151_cert).mp (by decide +kernel))

def profile10_node152_cert : CutBound 6 := { lost := (rows 4 0 0 4 0 0), upper := (rows 11 38 22 25 21 37), lower := (rows 11 38 22 25 16 32), losses := [{ target := 2, region := (rows 7 2 0 12 16 32), good := (rows 11 43 27 25 16 32) }] }

theorem profile10_node152 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,17] 6 5 profile10_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,17] 6 5 profile10_node152_cert).mp (by decide +kernel))

def profile10_node153_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 11 38 22 28 17 33), lower := (rows 11 38 22 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 10 46 30 28 16 32) }] }

theorem profile10_node153 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,20] 6 1 profile10_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18,20] 6 1 profile10_node153_cert).mp (by decide +kernel))

def profile10_node150_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node150_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node150 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36,18] 6 (by decide) (choices 2) [5,17,20] profile10_node150_route profile10_node150_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node151
  · exact profile10_node152
  · exact profile10_node153

def profile10_node141_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node141_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node141 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,36] 6 (by decide) (choices 2) [3,17,18] profile10_node141_route profile10_node141_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node142
  · exact profile10_node143
  · exact profile10_node150

def profile10_node155_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 11 50 7 29 21 53), lower := (rows 11 50 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 9 48 61 8 16 32) }] }

theorem profile10_node155 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,3] 6 21 profile10_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,3] 6 21 profile10_node155_cert).mp (by decide +kernel))

def profile10_node157_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 50 21 11 20 36), lower := (rows 11 50 21 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 20 36), good := (rows 10 50 54 10 16 32) }] }

theorem profile10_node157 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,3] 6 4 profile10_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,3] 6 4 profile10_node157_cert).mp (by decide +kernel))

def profile10_node158_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 11 50 21 13 22 38), lower := (rows 11 50 21 13 16 32), losses := [{ target := 0, region := (rows 0 15 4 8 28 44), good := (rows 58 50 54 62 16 32) }] }

theorem profile10_node158 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,5] 6 6 profile10_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,5] 6 6 profile10_node158_cert).mp (by decide +kernel))

def profile10_node159_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 11 50 21 14 21 37), lower := (rows 11 50 21 14 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 21 37), good := (rows 61 48 53 60 16 32) }] }

theorem profile10_node159 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,6] 6 5 profile10_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17,6] 6 5 profile10_node159_cert).mp (by decide +kernel))

def profile10_node156_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node156_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node156 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,17] 6 (by decide) (choices 2) [3,5,6] profile10_node156_route profile10_node156_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node157
  · exact profile10_node158
  · exact profile10_node159

def profile10_node160_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 11 50 22 13 21 37), lower := (rows 11 50 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 14 54 22 8 16 32) }] }

theorem profile10_node160 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,18] 6 5 profile10_node160_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48,18] 6 5 profile10_node160_cert).mp (by decide +kernel))

def profile10_node154_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node154_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node154 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10,48] 6 (by decide) (choices 2) [3,17,18] profile10_node154_route profile10_node154_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node155
  · exact profile10_node156
  · exact profile10_node160

def profile10_node85_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node85_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node85 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [10] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile10_node85_route profile10_node85_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node86
  · exact profile10_node99
  · exact profile10_node115
  · exact profile10_node131
  · exact profile10_node141
  · exact profile10_node154

def profile10_node163_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 7 60 60 60), lower := (rows 19 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 58 62 62 8 16 32) }] }

theorem profile10_node163 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,3] 6 60 profile10_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,3] 6 60 profile10_node163_cert).mp (by decide +kernel))

def profile10_node164_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 13 62 54 54), lower := (rows 19 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 12 8 16 32) }] }

theorem profile10_node164 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,9] 6 54 profile10_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,9] 6 54 profile10_node164_cert).mp (by decide +kernel))

def profile10_node165_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 7 14 61 53 53), lower := (rows 19 7 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 34), good := (rows 57 61 60 8 16 32) }] }

theorem profile10_node165 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,10] 6 53 profile10_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,10] 6 53 profile10_node165_cert).mp (by decide +kernel))

def profile10_node166_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 21 46 62 46), lower := (rows 19 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 20 8 16 32) }] }

theorem profile10_node166 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,17] 6 46 profile10_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,17] 6 46 profile10_node166_cert).mp (by decide +kernel))

def profile10_node167_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 7 22 45 61 45), lower := (rows 19 7 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 6 22 8 16 32) }] }

theorem profile10_node167 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,18] 6 45 profile10_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,18] 6 45 profile10_node167_cert).mp (by decide +kernel))

def profile10_node168_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 19 7 28 47 55 39), lower := (rows 19 7 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 43 47 12 8 0 32) }] }

theorem profile10_node168 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,24] 6 39 profile10_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,24] 6 39 profile10_node168_cert).mp (by decide +kernel))

def profile10_node169_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 37 30 30 62), lower := (rows 19 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 36 8 16 32) }] }

theorem profile10_node169 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,33] 6 30 profile10_node169_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,33] 6 30 profile10_node169_cert).mp (by decide +kernel))

def profile10_node170_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 7 38 29 29 61), lower := (rows 19 7 38 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 34), good := (rows 57 61 60 8 16 32) }] }

theorem profile10_node170 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,34] 6 29 profile10_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,34] 6 29 profile10_node170_cert).mp (by decide +kernel))

def profile10_node172_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 7 44 11 20 52), lower := (rows 19 7 44 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 30 46), good := (rows 50 54 60 62 16 32) }] }

theorem profile10_node172 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,3] 6 20 profile10_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,3] 6 20 profile10_node172_cert).mp (by decide +kernel))

def profile10_node173_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 7 44 13 18 50), lower := (rows 19 7 44 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 50 54 44 60 16 32) }] }

theorem profile10_node173 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,5] 6 18 profile10_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,5] 6 18 profile10_node173_cert).mp (by decide +kernel))

def profile10_node174_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 44 14 17 49), lower := (rows 19 7 44 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 26 14 44 14 16 32) }] }

theorem profile10_node174 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,6] 6 17 profile10_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,6] 6 17 profile10_node174_cert).mp (by decide +kernel))

def profile10_node175_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 7 44 25 22 38), lower := (rows 19 7 44 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 25 13 44 25 16 32) }] }

theorem profile10_node175 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,17] 6 6 profile10_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,17] 6 6 profile10_node175_cert).mp (by decide +kernel))

def profile10_node176_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 7 44 26 21 37), lower := (rows 19 7 44 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 26 14 44 26 16 32) }] }

theorem profile10_node176 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,18] 6 5 profile10_node176_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,18] 6 5 profile10_node176_cert).mp (by decide +kernel))

def profile10_node177_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 19 7 44 28 19 35), lower := (rows 19 7 44 28 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 19 35), good := (rows 51 51 40 24 16 32) }] }

theorem profile10_node177 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,20] 6 3 profile10_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40,20] 6 3 profile10_node177_cert).mp (by decide +kernel))

def profile10_node171_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node171_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node171 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,40] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node171_route profile10_node171_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node172
  · exact profile10_node173
  · exact profile10_node174
  · exact profile10_node175
  · exact profile10_node176
  · exact profile10_node177

def profile10_node178_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 19 7 52 15 31 47), lower := (rows 19 7 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 43 47 36 8 0 32) }] }

theorem profile10_node178 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,48] 6 15 profile10_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5,48] 6 15 profile10_node178_cert).mp (by decide +kernel))

def profile10_node162_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile10_node162_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node162 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,5] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48] profile10_node162_route profile10_node162_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node163
  · exact profile10_node164
  · exact profile10_node165
  · exact profile10_node166
  · exact profile10_node167
  · exact profile10_node168
  · exact profile10_node169
  · exact profile10_node170
  · exact profile10_node171
  · exact profile10_node178

def profile10_node180_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 11 7 60 52 52), lower := (rows 19 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 18 10 62 8 16 32) }] }

theorem profile10_node180 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,3] 6 52 profile10_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,3] 6 52 profile10_node180_cert).mp (by decide +kernel))

def profile10_node181_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 11 21 46 54 38), lower := (rows 19 11 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 13 21 8 16 32) }] }

theorem profile10_node181 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,17] 6 38 profile10_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,17] 6 38 profile10_node181_cert).mp (by decide +kernel))

def profile10_node182_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 11 22 45 53 37), lower := (rows 19 11 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 14 22 8 16 32) }] }

theorem profile10_node182 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,18] 6 37 profile10_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,18] 6 37 profile10_node182_cert).mp (by decide +kernel))

def profile10_node184_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 11 37 14 20 52), lower := (rows 19 11 37 14 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 53 61 53 60 16 32) }] }

theorem profile10_node184 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,6] 6 20 profile10_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,6] 6 20 profile10_node184_cert).mp (by decide +kernel))

def profile10_node185_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 11 37 26 20 36), lower := (rows 19 11 37 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 20 36), good := (rows 26 10 60 26 16 32) }] }

theorem profile10_node185 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,18] 6 4 profile10_node185_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,18] 6 4 profile10_node185_cert).mp (by decide +kernel))

def profile10_node186_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 19 11 37 28 22 38), lower := (rows 19 11 37 28 16 32), losses := [{ target := 2, region := (rows 9 10 0 8 16 32), good := (rows 19 11 33 27 16 32) }] }

theorem profile10_node186 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,20] 6 6 profile10_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33,20] 6 6 profile10_node186_cert).mp (by decide +kernel))

def profile10_node183_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node183_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node183 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,33] 6 (by decide) (choices 2) [6,18,20] profile10_node183_route profile10_node183_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node184
  · exact profile10_node185
  · exact profile10_node186

def profile10_node188_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 11 38 13 20 52), lower := (rows 19 11 38 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 54 62 54 60 16 32) }] }

theorem profile10_node188 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,5] 6 20 profile10_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,5] 6 20 profile10_node188_cert).mp (by decide +kernel))

def profile10_node189_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 11 38 25 20 36), lower := (rows 19 11 38 25 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 54 62 54 60 16 32) }] }

theorem profile10_node189 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,17] 6 4 profile10_node189_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,17] 6 4 profile10_node189_cert).mp (by decide +kernel))

def profile10_node190_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 19 11 38 28 21 37), lower := (rows 19 11 38 28 16 32), losses := [{ target := 2, region := (rows 9 10 0 8 16 32), good := (rows 19 11 34 27 16 32) }] }

theorem profile10_node190 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,20] 6 5 profile10_node190_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34,20] 6 5 profile10_node190_cert).mp (by decide +kernel))

def profile10_node187_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node187_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node187 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,34] 6 (by decide) (choices 2) [5,17,20] profile10_node187_route profile10_node187_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node188
  · exact profile10_node189
  · exact profile10_node190

def profile10_node192_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 11 52 11 20 36), lower := (rows 19 11 52 11 16 32), losses := [{ target := 0, region := (rows 0 2 63 8 63 63), good := (rows 54 62 52 62 52 52) }] }

theorem profile10_node192 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,3] 6 4 profile10_node192_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,3] 6 4 profile10_node192_cert).mp (by decide +kernel))

def profile10_node193_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 11 52 13 22 38), lower := (rows 19 11 52 13 16 32), losses := [{ target := 0, region := (rows 0 2 15 8 19 35), good := (rows 54 62 52 60 16 32) }] }

theorem profile10_node193 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,5] 6 6 profile10_node193_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,5] 6 6 profile10_node193_cert).mp (by decide +kernel))

def profile10_node194_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 11 52 14 21 37), lower := (rows 19 11 52 14 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 19 35), good := (rows 53 61 52 60 16 32) }] }

theorem profile10_node194 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,6] 6 5 profile10_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48,6] 6 5 profile10_node194_cert).mp (by decide +kernel))

def profile10_node191_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node191_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node191 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9,48] 6 (by decide) (choices 2) [3,5,6] profile10_node191_route profile10_node191_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node192
  · exact profile10_node193
  · exact profile10_node194

def profile10_node179_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node179_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node179 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,9] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node179_route profile10_node179_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node180
  · exact profile10_node181
  · exact profile10_node182
  · exact profile10_node183
  · exact profile10_node187
  · exact profile10_node191

def profile10_node196_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 14 7 61 53 53), lower := (rows 19 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 17 60 61 8 16 32) }] }

theorem profile10_node196 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,3] 6 53 profile10_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,3] 6 53 profile10_node196_cert).mp (by decide +kernel))

def profile10_node197_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 14 21 47 55 39), lower := (rows 19 14 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 12 21 8 16 32) }] }

theorem profile10_node197 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,17] 6 39 profile10_node197_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,17] 6 39 profile10_node197_cert).mp (by decide +kernel))

def profile10_node198_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 14 22 45 53 37), lower := (rows 19 14 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 14 22 8 16 32) }] }

theorem profile10_node198 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,18] 6 37 profile10_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,18] 6 37 profile10_node198_cert).mp (by decide +kernel))

def profile10_node200_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 14 37 11 20 52), lower := (rows 19 14 37 11 16 32), losses := [{ target := 1, region := (rows 1 0 13 8 31 47), good := (rows 53 60 53 61 16 32) }] }

theorem profile10_node200 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,3] 6 20 profile10_node200_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,3] 6 20 profile10_node200_cert).mp (by decide +kernel))

def profile10_node201_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 14 37 13 18 50), lower := (rows 19 14 37 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 43), good := (rows 50 62 52 62 16 32) }] }

theorem profile10_node201 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,5] 6 18 profile10_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,5] 6 18 profile10_node201_cert).mp (by decide +kernel))

def profile10_node202_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 19 14 37 14 17 49), lower := (rows 19 14 37 14 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 32), good := (rows 26 14 46 14 16 32) }] }

theorem profile10_node202 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,6] 6 17 profile10_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,6] 6 17 profile10_node202_cert).mp (by decide +kernel))

def profile10_node203_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 14 37 25 22 38), lower := (rows 19 14 37 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 25 12 45 25 16 32) }] }

theorem profile10_node203 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,17] 6 6 profile10_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,17] 6 6 profile10_node203_cert).mp (by decide +kernel))

def profile10_node204_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 19 14 37 26 21 37), lower := (rows 19 14 37 26 16 32), losses := [{ target := 0, region := (rows 0 6 4 9 16 32), good := (rows 26 14 46 26 16 32) }] }

theorem profile10_node204 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,18] 6 5 profile10_node204_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,18] 6 5 profile10_node204_cert).mp (by decide +kernel))

def profile10_node205_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 14 37 28 19 35), lower := (rows 19 14 37 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 18 14 36 30 16 32) }] }

theorem profile10_node205 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,20] 6 3 profile10_node205_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33,20] 6 3 profile10_node205_cert).mp (by decide +kernel))

def profile10_node199_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node199_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node199 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,33] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node199_route profile10_node199_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node200
  · exact profile10_node201
  · exact profile10_node202
  · exact profile10_node203
  · exact profile10_node204
  · exact profile10_node205

def profile10_node207_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 14 38 13 17 49), lower := (rows 19 14 38 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 18 14 38 14 16 32) }] }

theorem profile10_node207 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,5] 6 17 profile10_node207_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,5] 6 17 profile10_node207_cert).mp (by decide +kernel))

def profile10_node208_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 14 38 25 21 37), lower := (rows 19 14 38 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 25 12 36 25 16 32) }] }

theorem profile10_node208 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,17] 6 5 profile10_node208_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,17] 6 5 profile10_node208_cert).mp (by decide +kernel))

def profile10_node209_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 14 38 28 17 33), lower := (rows 19 14 38 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 18 14 38 30 16 32) }] }

theorem profile10_node209 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,20] 6 1 profile10_node209_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34,20] 6 1 profile10_node209_cert).mp (by decide +kernel))

def profile10_node206_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node206_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node206 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,34] 6 (by decide) (choices 2) [5,17,20] profile10_node206_route profile10_node206_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node207
  · exact profile10_node208
  · exact profile10_node209

def profile10_node211_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 14 52 11 21 37), lower := (rows 19 14 52 11 16 32), losses := [{ target := 1, region := (rows 1 0 15 8 25 41), good := (rows 53 60 52 61 16 32) }] }

theorem profile10_node211 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,3] 6 5 profile10_node211_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,3] 6 5 profile10_node211_cert).mp (by decide +kernel))

def profile10_node212_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 14 52 13 19 35), lower := (rows 19 14 52 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 18 14 52 14 16 32) }] }

theorem profile10_node212 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,5] 6 3 profile10_node212_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,5] 6 3 profile10_node212_cert).mp (by decide +kernel))

def profile10_node213_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 19 14 52 14 17 33), lower := (rows 19 14 52 14 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 32), good := (rows 26 14 62 14 16 32) }] }

theorem profile10_node213 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,6] 6 1 profile10_node213_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48,6] 6 1 profile10_node213_cert).mp (by decide +kernel))

def profile10_node210_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node210_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node210 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12,48] 6 (by decide) (choices 2) [3,5,6] profile10_node210_route profile10_node210_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node211
  · exact profile10_node212
  · exact profile10_node213

def profile10_node195_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node195_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node195 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,12] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node195_route profile10_node195_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node196
  · exact profile10_node197
  · exact profile10_node198
  · exact profile10_node199
  · exact profile10_node206
  · exact profile10_node210

def profile10_node214_cert : CutBound 6 := { lost := (rows 4 4 0 0 0 0), upper := (rows 19 19 47 47 63 47), lower := (rows 19 19 4 8 16 32), losses := [{ target := 2, region := (rows 19 19 0 8 16 32), good := (rows 19 19 0 8 19 32) }] }

theorem profile10_node214 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,17] 6 47 profile10_node214_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,17] 6 47 profile10_node214_cert).mp (by decide +kernel))

def profile10_node215_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 19 22 47 47 63 47), lower := (rows 19 22 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 32), good := (rows 19 19 0 8 16 32) }] }

theorem profile10_node215 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,20] 6 47 profile10_node215_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,20] 6 47 profile10_node215_cert).mp (by decide +kernel))

def profile10_node216_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 19 26 39 47 55 39), lower := (rows 19 26 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 32), good := (rows 19 27 0 8 16 32) }] }

theorem profile10_node216 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,24] 6 39 profile10_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,24] 6 39 profile10_node216_cert).mp (by decide +kernel))

def profile10_node218_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 35 7 28 28 60), lower := (rows 19 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 18 34 62 8 16 32) }] }

theorem profile10_node218 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,3] 6 28 profile10_node218_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,3] 6 28 profile10_node218_cert).mp (by decide +kernel))

def profile10_node220_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 35 13 14 20 52), lower := (rows 19 35 13 14 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 32), good := (rows 15 47 13 14 0 32) }] }

theorem profile10_node220 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,6] 6 20 profile10_node220_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,6] 6 20 profile10_node220_cert).mp (by decide +kernel))

def profile10_node221_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 35 13 26 20 36), lower := (rows 19 35 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 20 36), good := (rows 26 42 60 26 16 32) }] }

theorem profile10_node221 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,18] 6 4 profile10_node221_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,18] 6 4 profile10_node221_cert).mp (by decide +kernel))

def profile10_node222_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 19 35 13 28 22 38), lower := (rows 19 35 13 28 16 32), losses := [{ target := 1, region := (rows 1 0 7 9 16 32), good := (rows 29 45 13 28 16 32) }] }

theorem profile10_node222 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,20] 6 6 profile10_node222_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9,20] 6 6 profile10_node222_cert).mp (by decide +kernel))

def profile10_node219_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node219_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node219 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,9] 6 (by decide) (choices 2) [6,18,20] profile10_node219_route profile10_node219_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node220
  · exact profile10_node221
  · exact profile10_node222

def profile10_node224_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 19 35 14 13 20 52), lower := (rows 19 35 14 13 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 32), good := (rows 15 47 14 13 0 32) }] }

theorem profile10_node224 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,5] 6 20 profile10_node224_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,5] 6 20 profile10_node224_cert).mp (by decide +kernel))

def profile10_node225_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 35 14 25 20 36), lower := (rows 19 35 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 20 36), good := (rows 25 41 60 25 16 32) }] }

theorem profile10_node225 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,17] 6 4 profile10_node225_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,17] 6 4 profile10_node225_cert).mp (by decide +kernel))

def profile10_node226_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 14 28 21 37), lower := (rows 19 35 14 28 16 32), losses := [{ target := 0, region := (rows 0 2 7 9 16 32), good := (rows 30 46 14 28 16 32) }] }

theorem profile10_node226 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,20] 6 5 profile10_node226_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10,20] 6 5 profile10_node226_cert).mp (by decide +kernel))

def profile10_node223_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node223_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node223 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,10] 6 (by decide) (choices 2) [5,17,20] profile10_node223_route profile10_node223_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node224
  · exact profile10_node225
  · exact profile10_node226

def profile10_node227_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 35 21 14 30 46), lower := (rows 19 35 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 37 21 8 16 32) }] }

theorem profile10_node227 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,17] 6 14 profile10_node227_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,17] 6 14 profile10_node227_cert).mp (by decide +kernel))

def profile10_node228_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 22 13 29 45), lower := (rows 19 35 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) }] }

theorem profile10_node228 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,18] 6 13 profile10_node228_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,18] 6 13 profile10_node228_cert).mp (by decide +kernel))

def profile10_node230_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 35 28 11 20 36), lower := (rows 19 35 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 28 44), good := (rows 18 34 60 62 16 32) }] }

theorem profile10_node230 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,3] 6 4 profile10_node230_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,3] 6 4 profile10_node230_cert).mp (by decide +kernel))

def profile10_node231_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 19 35 28 13 22 38), lower := (rows 19 35 28 13 16 32), losses := [{ target := 1, region := (rows 1 0 5 11 16 32), good := (rows 29 45 28 13 16 32) }] }

theorem profile10_node231 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,5] 6 6 profile10_node231_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,5] 6 6 profile10_node231_cert).mp (by decide +kernel))

def profile10_node232_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 35 28 14 21 37), lower := (rows 19 35 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 5 11 16 32), good := (rows 30 46 28 14 16 32) }] }

theorem profile10_node232 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,6] 6 5 profile10_node232_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24,6] 6 5 profile10_node232_cert).mp (by decide +kernel))

def profile10_node229_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node229_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node229 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33,24] 6 (by decide) (choices 2) [3,5,6] profile10_node229_route profile10_node229_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node230
  · exact profile10_node231
  · exact profile10_node232

def profile10_node217_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node217_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node217 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,33] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node217_route profile10_node217_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node218
  · exact profile10_node219
  · exact profile10_node223
  · exact profile10_node227
  · exact profile10_node228
  · exact profile10_node229

def profile10_node234_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 38 7 29 29 61), lower := (rows 19 38 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 17 60 61 8 16 32) }] }

theorem profile10_node234 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,3] 6 29 profile10_node234_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,3] 6 29 profile10_node234_cert).mp (by decide +kernel))

def profile10_node236_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 13 11 20 52), lower := (rows 19 38 13 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 50 54 62 58 16 32) }] }

theorem profile10_node236 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,3] 6 20 profile10_node236_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,3] 6 20 profile10_node236_cert).mp (by decide +kernel))

def profile10_node237_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 13 13 18 50), lower := (rows 19 38 13 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 47), good := (rows 50 54 62 62 16 32) }] }

theorem profile10_node237 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,5] 6 18 profile10_node237_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,5] 6 18 profile10_node237_cert).mp (by decide +kernel))

def profile10_node238_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 38 13 14 17 49), lower := (rows 19 38 13 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 26 46 12 14 16 32) }] }

theorem profile10_node238 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,6] 6 17 profile10_node238_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,6] 6 17 profile10_node238_cert).mp (by decide +kernel))

def profile10_node239_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 19 38 13 25 22 38), lower := (rows 19 38 13 25 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 50 54 62 24 16 32) }] }

theorem profile10_node239 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,17] 6 6 profile10_node239_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,17] 6 6 profile10_node239_cert).mp (by decide +kernel))

def profile10_node240_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 19 38 13 26 21 37), lower := (rows 19 38 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 9 16 32), good := (rows 26 38 12 26 16 32) }] }

theorem profile10_node240 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,18] 6 5 profile10_node240_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,18] 6 5 profile10_node240_cert).mp (by decide +kernel))

def profile10_node241_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 19 38 13 28 19 35), lower := (rows 19 38 13 28 16 32), losses := [{ target := 1, region := (rows 1 0 5 9 16 32), good := (rows 29 36 13 28 16 32) }] }

theorem profile10_node241 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,20] 6 3 profile10_node241_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9,20] 6 3 profile10_node241_cert).mp (by decide +kernel))

def profile10_node235_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node235_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node235 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,9] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node235_route profile10_node235_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node236
  · exact profile10_node237
  · exact profile10_node238
  · exact profile10_node239
  · exact profile10_node240
  · exact profile10_node241

def profile10_node243_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 19 38 14 13 17 49), lower := (rows 19 38 14 13 16 32), losses := [{ target := 2, region := (rows 7 2 0 8 31 47), good := (rows 51 51 59 57 16 32) }] }

theorem profile10_node243 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,5] 6 17 profile10_node243_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,5] 6 17 profile10_node243_cert).mp (by decide +kernel))

def profile10_node244_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 38 14 25 21 37), lower := (rows 19 38 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 25 36 12 25 16 32) }] }

theorem profile10_node244 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,17] 6 5 profile10_node244_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,17] 6 5 profile10_node244_cert).mp (by decide +kernel))

def profile10_node245_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 38 14 28 17 33), lower := (rows 19 38 14 28 16 32), losses := [{ target := 0, region := (rows 0 2 5 9 16 32), good := (rows 30 38 14 28 16 32) }] }

theorem profile10_node245 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,20] 6 1 profile10_node245_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10,20] 6 1 profile10_node245_cert).mp (by decide +kernel))

def profile10_node242_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node242_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node242 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,10] 6 (by decide) (choices 2) [5,17,20] profile10_node242_route profile10_node242_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node243
  · exact profile10_node244
  · exact profile10_node245

def profile10_node246_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 38 21 15 31 47), lower := (rows 19 38 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 36 21 8 16 32) }] }

theorem profile10_node246 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,17] 6 15 profile10_node246_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,17] 6 15 profile10_node246_cert).mp (by decide +kernel))

def profile10_node247_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 38 22 13 29 45), lower := (rows 19 38 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 38 22 8 16 32) }] }

theorem profile10_node247 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,18] 6 13 profile10_node247_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,18] 6 13 profile10_node247_cert).mp (by decide +kernel))

def profile10_node249_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 38 28 11 21 37), lower := (rows 19 38 28 11 16 32), losses := [{ target := 1, region := (rows 1 0 12 8 24 40), good := (rows 17 36 60 61 16 32) }] }

theorem profile10_node249 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,3] 6 5 profile10_node249_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,3] 6 5 profile10_node249_cert).mp (by decide +kernel))

def profile10_node250_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 19 38 28 13 19 35), lower := (rows 19 38 28 13 16 32), losses := [{ target := 1, region := (rows 1 0 5 9 16 32), good := (rows 29 36 28 13 16 32) }] }

theorem profile10_node250 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,5] 6 3 profile10_node250_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,5] 6 3 profile10_node250_cert).mp (by decide +kernel))

def profile10_node251_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 19 38 28 14 17 33), lower := (rows 19 38 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 5 11 16 32), good := (rows 30 46 28 14 16 32) }] }

theorem profile10_node251 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,6] 6 1 profile10_node251_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24,6] 6 1 profile10_node251_cert).mp (by decide +kernel))

def profile10_node248_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node248_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node248 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36,24] 6 (by decide) (choices 2) [3,5,6] profile10_node248_route profile10_node248_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node249
  · exact profile10_node250
  · exact profile10_node251

def profile10_node233_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node233_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node233 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,36] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node233_route profile10_node233_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node234
  · exact profile10_node235
  · exact profile10_node242
  · exact profile10_node246
  · exact profile10_node247
  · exact profile10_node248

def profile10_node253_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 19 42 7 29 21 53), lower := (rows 19 42 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 17 40 61 8 16 32) }] }

theorem profile10_node253 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,3] 6 21 profile10_node253_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,3] 6 21 profile10_node253_cert).mp (by decide +kernel))

def profile10_node254_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 19 42 21 15 23 39), lower := (rows 19 42 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 21 40 21 8 16 32) }] }

theorem profile10_node254 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,17] 6 7 profile10_node254_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,17] 6 7 profile10_node254_cert).mp (by decide +kernel))

def profile10_node255_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 19 42 22 13 21 37), lower := (rows 19 42 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 22 42 22 8 16 32) }] }

theorem profile10_node255 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,18] 6 5 profile10_node255_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40,18] 6 5 profile10_node255_cert).mp (by decide +kernel))

def profile10_node252_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node252_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node252 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,40] 6 (by decide) (choices 2) [3,17,18] profile10_node252_route profile10_node252_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node253
  · exact profile10_node254
  · exact profile10_node255

def profile10_node256_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 19 50 15 15 31 47), lower := (rows 19 50 4 8 16 32), losses := [{ target := 2, region := (rows 3 2 0 8 16 32), good := (rows 19 51 0 8 16 32) }] }

theorem profile10_node256 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,48] 6 15 profile10_node256_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18,48] 6 15 profile10_node256_cert).mp (by decide +kernel))

def profile10_node161_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile10_node161_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node161 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [18] 6 (by decide) (choices 2) [5,9,12,17,20,24,33,36,40,48] profile10_node161_route profile10_node161_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node162
  · exact profile10_node179
  · exact profile10_node195
  · exact profile10_node214
  · exact profile10_node215
  · exact profile10_node216
  · exact profile10_node217
  · exact profile10_node233
  · exact profile10_node252
  · exact profile10_node256


#print axioms profile10_node161
end Delivery.SmallBudgetTenFinite6
