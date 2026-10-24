import SmallBudgetTenFinite7Profile026Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile26_node132_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 35 14 21 25 80 96 64), lower := (rows 35 14 21 25 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 111 101 105 96 96 96) }] }

theorem profile26_node132 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,17] 6 64 profile26_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,17] 6 64 profile26_node132_cert).mp (by decide +kernel))

def profile26_node133_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 35 14 21 73 80 112 64), lower := (rows 35 14 21 73 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 13 0 32 127), good := (rows 107 78 79 73 64 96 64) }] }

theorem profile26_node133 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,65] 6 80 profile26_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,65] 6 80 profile26_node133_cert).mp (by decide +kernel))

def profile26_node134_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 35 14 21 88 81 97 64), lower := (rows 35 14 21 88 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 28 16 32 127), good := (rows 98 78 94 88 88 96 64) }] }

theorem profile26_node134 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,80] 6 65 profile26_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17,80] 6 65 profile26_node134_cert).mp (by decide +kernel))

def profile26_node131_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node131_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node131 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,17] 6 (by decide) (choices 2) [17,65,80] profile26_node131_route profile26_node131_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node132
  · exact profile26_node133
  · exact profile26_node134

def profile26_node135_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 35 14 69 89 81 113 64), lower := (rows 35 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 103 78 69 72 64 96 64) }] }

theorem profile26_node135 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,65] 6 81 profile26_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,65] 6 81 profile26_node135_cert).mp (by decide +kernel))

def profile26_node136_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 14 84 89 81 113 64), lower := (rows 35 14 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 98 78 84 72 84 96 64) }] }

theorem profile26_node136 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,80] 6 81 profile26_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12,80] 6 81 profile26_node136_cert).mp (by decide +kernel))

def profile26_node130_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node130_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node130 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,12] 6 (by decide) (choices 2) [17,65,80] profile26_node130_route profile26_node130_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node131
  · exact profile26_node135
  · exact profile26_node136

def profile26_node138_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 35 19 13 92 84 116 64), lower := (rows 35 19 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 98 82 124 72 80 96 64) }] }

theorem profile26_node138 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,9] 6 84 profile26_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,9] 6 84 profile26_node138_cert).mp (by decide +kernel))

def profile26_node139_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 35 19 21 76 92 108 64), lower := (rows 35 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 98 82 124 72 80 96 64) }] }

theorem profile26_node139 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,17] 6 76 profile26_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,17] 6 76 profile26_node139_cert).mp (by decide +kernel))

def profile26_node141_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 19 28 13 80 96 64), lower := (rows 35 19 28 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 114 114 124 124 112 112 112) }] }

theorem profile26_node141 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,5] 6 64 profile26_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,5] 6 64 profile26_node141_cert).mp (by decide +kernel))

def profile26_node142_cert : Bound 7 := { allowed := (rows 80 64 65 16 0 0 0), upper := (rows 35 19 28 73 84 100 64), lower := (rows 35 19 28 73 16 32 64), losses := [] }

theorem profile26_node142 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,65] 6 68 profile26_node142_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,65] 6 68 profile26_node142_cert).mp (by decide +kernel))

def profile26_node143_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 35 19 28 76 81 97 64), lower := (rows 35 19 28 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 31 16 32 127), good := (rows 110 94 92 76 92 96 64) }] }

theorem profile26_node143 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,68] 6 65 profile26_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24,68] 6 65 profile26_node143_cert).mp (by decide +kernel))

def profile26_node140_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node140_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node140 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,24] 6 (by decide) (choices 2) [5,65,68] profile26_node140_route profile26_node140_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node141
  · exact profile26_node142
  · exact profile26_node143

def profile26_node144_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 35 19 69 92 92 124 64), lower := (rows 35 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 98 82 124 72 80 96 64) }] }

theorem profile26_node144 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,65] 6 92 profile26_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,65] 6 92 profile26_node144_cert).mp (by decide +kernel))

def profile26_node145_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 19 76 93 85 117 64), lower := (rows 35 19 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 98 82 76 76 80 96 64) }] }

theorem profile26_node145 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,72] 6 85 profile26_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,72] 6 85 profile26_node145_cert).mp (by decide +kernel))

def profile26_node146_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 19 84 77 93 109 64), lower := (rows 35 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 102 86 84 72 84 96 64) }] }

theorem profile26_node146 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,80] 6 77 profile26_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17,80] 6 77 profile26_node146_cert).mp (by decide +kernel))

def profile26_node137_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node137_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node137 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,17] 6 (by decide) (choices 2) [9,17,24,65,72,80] profile26_node137_route profile26_node137_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node138
  · exact profile26_node139
  · exact profile26_node140
  · exact profile26_node144
  · exact profile26_node145
  · exact profile26_node146

def profile26_node149_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 35 22 13 25 80 96 64), lower := (rows 35 22 13 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 126 120 112 112 112) }] }

theorem profile26_node149 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,17] 6 64 profile26_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,17] 6 64 profile26_node149_cert).mp (by decide +kernel))

def profile26_node150_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 35 22 13 73 80 112 64), lower := (rows 35 22 13 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 126 120 112 112 112) }] }

theorem profile26_node150 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,65] 6 80 profile26_node150_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,65] 6 80 profile26_node150_cert).mp (by decide +kernel))

def profile26_node151_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 35 22 13 88 81 97 64), lower := (rows 35 22 13 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 127), good := (rows 106 94 76 88 88 96 64) }] }

theorem profile26_node151 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,80] 6 65 profile26_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9,80] 6 65 profile26_node151_cert).mp (by decide +kernel))

def profile26_node148_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node148_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node148 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,9] 6 (by decide) (choices 2) [17,65,80] profile26_node148_route profile26_node148_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node149
  · exact profile26_node150
  · exact profile26_node151

def profile26_node152_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 35 22 21 73 89 105 64), lower := (rows 35 22 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 98 86 86 72 80 96 64) }] }

theorem profile26_node152 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,17] 6 73 profile26_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,17] 6 73 profile26_node152_cert).mp (by decide +kernel))

def profile26_node153_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 35 22 28 73 81 97 64), lower := (rows 35 22 28 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 98 86 94 72 80 96 64) }] }

theorem profile26_node153 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,24] 6 65 profile26_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,24] 6 65 profile26_node153_cert).mp (by decide +kernel))

def profile26_node154_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 35 22 69 89 89 121 64), lower := (rows 35 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 103 70 69 72 64 96 64) }] }

theorem profile26_node154 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,65] 6 89 profile26_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,65] 6 89 profile26_node154_cert).mp (by decide +kernel))

def profile26_node155_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 35 22 76 89 81 113 64), lower := (rows 35 22 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 98 86 76 76 80 96 64) }] }

theorem profile26_node155 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,72] 6 81 profile26_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,72] 6 81 profile26_node155_cert).mp (by decide +kernel))

def profile26_node156_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 22 84 73 89 105 64), lower := (rows 35 22 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 102 86 86 72 86 96 64) }] }

theorem profile26_node156 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,80] 6 73 profile26_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20,80] 6 73 profile26_node156_cert).mp (by decide +kernel))

def profile26_node147_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node147_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node147 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,20] 6 (by decide) (choices 2) [9,17,24,65,72,80] profile26_node147_route profile26_node147_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node148
  · exact profile26_node152
  · exact profile26_node153
  · exact profile26_node154
  · exact profile26_node155
  · exact profile26_node156

def profile26_node157_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 67 93 93 93 125 64), lower := (rows 35 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 127), good := (rows 99 67 68 72 64 99 64) }] }

theorem profile26_node157 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,65] 6 93 profile26_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,65] 6 93 profile26_node157_cert).mp (by decide +kernel))

def profile26_node158_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 35 70 93 89 89 121 64), lower := (rows 35 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 98 70 70 72 80 96 64) }] }

theorem profile26_node158 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,68] 6 89 profile26_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,68] 6 89 profile26_node158_cert).mp (by decide +kernel))

def profile26_node159_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 35 82 93 93 93 125 64), lower := (rows 35 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 98 82 68 72 82 96 64) }] }

theorem profile26_node159 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,80] 6 93 profile26_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34,80] 6 93 profile26_node159_cert).mp (by decide +kernel))

def profile26_node119_column : Nat → Fin 7 := fun mask => match mask with | 33 => 5 | 36 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node119_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile26_node119 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [34] 6 (by decide) (choices 2) [5,12,17,20,65,68,80] profile26_node119_route profile26_node119_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node120
  · exact profile26_node130
  · exact profile26_node137
  · exact profile26_node147
  · exact profile26_node157
  · exact profile26_node158
  · exact profile26_node159

def profile26_node162_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 49 7 7 88 88 120 64), lower := (rows 49 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 126 126 120 120 120 120) }] }

theorem profile26_node162 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,3] 6 88 profile26_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,3] 6 88 profile26_node162_cert).mp (by decide +kernel))

def profile26_node163_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 49 7 13 90 82 114 64), lower := (rows 49 7 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 76 72 80 96 64) }] }

theorem profile26_node163 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,9] 6 82 profile26_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,9] 6 82 profile26_node163_cert).mp (by decide +kernel))

def profile26_node165_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 7 14 25 80 96 64), lower := (rows 49 7 14 25 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 127 127), good := (rows 97 103 110 111 96 96 96) }] }

theorem profile26_node165 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,17] 6 64 profile26_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,17] 6 64 profile26_node165_cert).mp (by decide +kernel))

def profile26_node166_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 49 7 14 73 80 112 64), lower := (rows 49 7 14 73 16 32 64), losses := [{ target := 4, region := (rows 1 11 15 11 0 32 127), good := (rows 111 79 78 79 64 96 64) }] }

theorem profile26_node166 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,65] 6 80 profile26_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,65] 6 80 profile26_node166_cert).mp (by decide +kernel))

def profile26_node167_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 49 7 14 88 81 97 64), lower := (rows 49 7 14 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 25 16 32 127), good := (rows 120 78 78 88 88 96 64) }] }

theorem profile26_node167 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,80] 6 65 profile26_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10,80] 6 65 profile26_node167_cert).mp (by decide +kernel))

def profile26_node164_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node164_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node164 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,10] 6 (by decide) (choices 2) [17,65,80] profile26_node164_route profile26_node164_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node165
  · exact profile26_node166
  · exact profile26_node167

def profile26_node168_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 49 7 21 74 90 106 64), lower := (rows 49 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 84 72 80 96 64) }] }

theorem profile26_node168 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,17] 6 74 profile26_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,17] 6 74 profile26_node168_cert).mp (by decide +kernel))

def profile26_node169_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 49 7 22 73 89 105 64), lower := (rows 49 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 105 111 110 72 64 96 64) }] }

theorem profile26_node169 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,18] 6 73 profile26_node169_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,18] 6 73 profile26_node169_cert).mp (by decide +kernel))

def profile26_node170_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 49 7 28 75 83 99 64), lower := (rows 49 7 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 97 111 76 72 64 96 64) }] }

theorem profile26_node170 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,24] 6 67 profile26_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,24] 6 67 profile26_node170_cert).mp (by decide +kernel))

def profile26_node171_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 49 7 69 90 90 122 64), lower := (rows 49 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 68 72 80 96 64) }] }

theorem profile26_node171 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,65] 6 90 profile26_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,65] 6 90 profile26_node171_cert).mp (by decide +kernel))

def profile26_node172_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 49 7 70 89 89 121 64), lower := (rows 49 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 112 70 70 72 80 96 64) }] }

theorem profile26_node172 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,66] 6 89 profile26_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,66] 6 89 profile26_node172_cert).mp (by decide +kernel))

def profile26_node173_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 49 7 76 91 83 115 64), lower := (rows 49 7 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 112 70 76 76 80 96 64) }] }

theorem profile26_node173 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,72] 6 83 profile26_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,72] 6 83 profile26_node173_cert).mp (by decide +kernel))

def profile26_node174_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 49 7 84 75 91 107 64), lower := (rows 49 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 116 70 84 72 84 96 64) }] }

theorem profile26_node174 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,80] 6 75 profile26_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5,80] 6 75 profile26_node174_cert).mp (by decide +kernel))

def profile26_node161_column : Nat → Fin 7 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node161_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node161 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,5] 6 (by decide) (choices 2) [3,9,10,17,18,24,65,66,72,80] profile26_node161_route profile26_node161_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node162
  · exact profile26_node163
  · exact profile26_node164
  · exact profile26_node168
  · exact profile26_node169
  · exact profile26_node170
  · exact profile26_node171
  · exact profile26_node172
  · exact profile26_node173
  · exact profile26_node174

def profile26_node177_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 14 7 25 80 96 64), lower := (rows 49 14 7 25 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 127 127), good := (rows 97 110 103 111 96 96 96) }] }

theorem profile26_node177 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,17] 6 64 profile26_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,17] 6 64 profile26_node177_cert).mp (by decide +kernel))

def profile26_node178_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 49 14 7 73 80 112 64), lower := (rows 49 14 7 73 16 32 64), losses := [{ target := 4, region := (rows 1 15 13 13 0 32 127), good := (rows 111 78 79 79 64 96 64) }] }

theorem profile26_node178 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,65] 6 80 profile26_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,65] 6 80 profile26_node178_cert).mp (by decide +kernel))

def profile26_node179_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 49 14 7 88 81 97 64), lower := (rows 49 14 7 88 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 25 16 32 127), good := (rows 120 78 78 88 88 96 64) }] }

theorem profile26_node179 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,80] 6 65 profile26_node179_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3,80] 6 65 profile26_node179_cert).mp (by decide +kernel))

def profile26_node176_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node176_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node176 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,3] 6 (by decide) (choices 2) [17,65,80] profile26_node176_route profile26_node176_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node177
  · exact profile26_node178
  · exact profile26_node179

def profile26_node180_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 49 14 21 75 83 99 64), lower := (rows 49 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 36 127), good := (rows 97 110 111 72 64 96 64) }] }

theorem profile26_node180 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,17] 6 67 profile26_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,17] 6 67 profile26_node180_cert).mp (by decide +kernel))

def profile26_node181_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 49 14 22 73 81 97 64), lower := (rows 49 14 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 78 70 72 64 96 64) }] }

theorem profile26_node181 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,18] 6 65 profile26_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,18] 6 65 profile26_node181_cert).mp (by decide +kernel))

def profile26_node182_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 14 69 91 83 115 64), lower := (rows 49 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 78 69 72 64 96 64) }] }

theorem profile26_node182 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,65] 6 83 profile26_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,65] 6 83 profile26_node182_cert).mp (by decide +kernel))

def profile26_node183_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 49 14 70 89 81 113 64), lower := (rows 49 14 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 14 8 16 32 127), good := (rows 112 78 70 78 80 96 64) }] }

theorem profile26_node183 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,66] 6 81 profile26_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,66] 6 81 profile26_node183_cert).mp (by decide +kernel))

def profile26_node184_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 49 14 84 75 83 99 64), lower := (rows 49 14 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 116 78 84 72 84 96 64) }] }

theorem profile26_node184 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,80] 6 67 profile26_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12,80] 6 67 profile26_node184_cert).mp (by decide +kernel))

def profile26_node175_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node175_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node175 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,12] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile26_node175_route profile26_node175_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node176
  · exact profile26_node180
  · exact profile26_node181
  · exact profile26_node182
  · exact profile26_node183
  · exact profile26_node184

def profile26_node185_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 19 79 79 95 111 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 97 111 68 72 64 96 64) }] }

theorem profile26_node185 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,17] 6 79 profile26_node185_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,17] 6 79 profile26_node185_cert).mp (by decide +kernel))

def profile26_node187_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 49 22 7 73 89 105 64), lower := (rows 49 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 105 110 111 72 64 96 64) }] }

theorem profile26_node187 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,3] 6 73 profile26_node187_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,3] 6 73 profile26_node187_cert).mp (by decide +kernel))

def profile26_node189_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 49 22 13 11 80 96 64), lower := (rows 49 22 13 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 126 122 112 112 112) }] }

theorem profile26_node189 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,3] 6 64 profile26_node189_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,3] 6 64 profile26_node189_cert).mp (by decide +kernel))

def profile26_node190_cert : Bound 7 := { allowed := (rows 64 65 80 16 0 0 0), upper := (rows 49 22 13 73 82 98 64), lower := (rows 49 22 13 73 16 32 64), losses := [] }

theorem profile26_node190 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,65] 6 66 profile26_node190_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,65] 6 66 profile26_node190_cert).mp (by decide +kernel))

def profile26_node191_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 49 22 13 74 81 97 64), lower := (rows 49 22 13 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 112 94 76 74 80 96 64) }] }

theorem profile26_node191 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,66] 6 65 profile26_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9,66] 6 65 profile26_node191_cert).mp (by decide +kernel))

def profile26_node188_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node188_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node188 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,9] 6 (by decide) (choices 2) [3,65,66] profile26_node188_route profile26_node188_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node189
  · exact profile26_node190
  · exact profile26_node191

def profile26_node192_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 49 22 14 73 81 97 64), lower := (rows 49 22 14 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 78 72 64 96 64) }] }

theorem profile26_node192 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,10] 6 65 profile26_node192_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,10] 6 65 profile26_node192_cert).mp (by decide +kernel))

def profile26_node193_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 49 22 69 75 91 107 64), lower := (rows 49 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 70 69 72 64 96 64) }] }

theorem profile26_node193 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,65] 6 75 profile26_node193_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,65] 6 75 profile26_node193_cert).mp (by decide +kernel))

def profile26_node194_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 49 22 70 73 89 105 64), lower := (rows 49 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 118 86 70 72 86 96 64) }] }

theorem profile26_node194 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,66] 6 73 profile26_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,66] 6 73 profile26_node194_cert).mp (by decide +kernel))

def profile26_node195_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 49 22 76 75 83 99 64), lower := (rows 49 22 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 112 86 76 76 80 96 64) }] }

theorem profile26_node195 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,72] 6 67 profile26_node195_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20,72] 6 67 profile26_node195_cert).mp (by decide +kernel))

def profile26_node186_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node186_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node186 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,20] 6 (by decide) (choices 2) [3,9,10,65,66,72] profile26_node186_route profile26_node186_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node187
  · exact profile26_node188
  · exact profile26_node192
  · exact profile26_node193
  · exact profile26_node194
  · exact profile26_node195

def profile26_node196_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 67 95 95 95 127 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) }] }

theorem profile26_node196 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,65] 6 95 profile26_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,65] 6 95 profile26_node196_cert).mp (by decide +kernel))

def profile26_node197_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 49 70 95 91 91 123 64), lower := (rows 49 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 112 70 70 72 80 96 64) }] }

theorem profile26_node197 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,68] 6 91 profile26_node197_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,68] 6 91 profile26_node197_cert).mp (by decide +kernel))

def profile26_node198_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 49 82 79 79 95 111 64), lower := (rows 49 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 68 72 82 96 64) }] }

theorem profile26_node198 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,80] 6 79 profile26_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48,80] 6 79 profile26_node198_cert).mp (by decide +kernel))

def profile26_node160_column : Nat → Fin 7 := fun mask => match mask with | 33 => 5 | 36 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node160_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile26_node160 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [48] 6 (by decide) (choices 2) [5,12,17,20,65,68,80] profile26_node160_route profile26_node160_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node161
  · exact profile26_node175
  · exact profile26_node185
  · exact profile26_node186
  · exact profile26_node196
  · exact profile26_node197
  · exact profile26_node198

def profile26_node199_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 67 127 125 125 125 125 64), lower := (rows 67 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile26_node199 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [66] 6 125 profile26_node199_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [66] 6 125 profile26_node199_cert).mp (by decide +kernel))

def profile26_node202_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 7 7 120 120 120 64), lower := (rows 81 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 126 126 120 120 120 120) }] }

theorem profile26_node202 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,3] 6 120 profile26_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,3] 6 120 profile26_node202_cert).mp (by decide +kernel))

def profile26_node203_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 7 13 122 114 114 64), lower := (rows 81 7 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 76 72 80 96 64) }] }

theorem profile26_node203 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,9] 6 114 profile26_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,9] 6 114 profile26_node203_cert).mp (by decide +kernel))

def profile26_node205_cert : Bound 7 := { allowed := (rows 0 80 81 64 0 0 0), upper := (rows 81 7 14 25 112 96 64), lower := (rows 81 7 14 25 16 32 64), losses := [] }

theorem profile26_node205 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,17] 6 96 profile26_node205_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,17] 6 96 profile26_node205_cert).mp (by decide +kernel))

def profile26_node206_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 7 14 41 80 112 64), lower := (rows 81 7 14 41 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 32 127), good := (rows 65 71 78 111 64 96 64) }] }

theorem profile26_node206 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,33] 6 80 profile26_node206_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,33] 6 80 profile26_node206_cert).mp (by decide +kernel))

def profile26_node208_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 81 7 14 56 17 96 64), lower := (rows 81 7 14 56 17 32 64), losses := [{ target := 0, region := (rows 0 2 6 25 16 127 127), good := (rows 120 110 110 120 120 96 96) }] }

theorem profile26_node208 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48,1] 6 64 profile26_node208_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48,1] 6 64 profile26_node208_cert).mp (by decide +kernel))

def profile26_node209_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 7 14 56 80 33 64), lower := (rows 81 7 14 56 80 32 64), losses := [{ target := 0, region := (rows 0 2 4 40 127 32 127), good := (rows 80 86 94 120 80 120 80) }] }

theorem profile26_node209 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48,64] 6 1 profile26_node209_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48,64] 6 1 profile26_node209_cert).mp (by decide +kernel))

def profile26_node207_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile26_node207_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node207 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,48] 6 (by decide) (choices 1) [1,64] profile26_node207_route profile26_node207_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile26_node208
  · exact profile26_node209

def profile26_node210_cert : Bound 7 := { allowed := (rows 0 80 81 16 0 0 0), upper := (rows 81 7 14 73 48 48 64), lower := (rows 81 7 14 73 16 32 64), losses := [] }

theorem profile26_node210 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,65] 6 48 profile26_node210_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,65] 6 48 profile26_node210_cert).mp (by decide +kernel))

def profile26_node211_cert : Bound 7 := { allowed := (rows 0 80 81 1 0 0 0), upper := (rows 81 7 14 88 49 33 64), lower := (rows 81 7 14 88 16 32 64), losses := [] }

theorem profile26_node211 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,80] 6 33 profile26_node211_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,80] 6 33 profile26_node211_cert).mp (by decide +kernel))

def profile26_node212_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 7 14 104 17 49 64), lower := (rows 81 7 14 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 127), good := (rows 80 70 78 104 80 104 64) }] }

theorem profile26_node212 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,96] 6 17 profile26_node212_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10,96] 6 17 profile26_node212_cert).mp (by decide +kernel))

def profile26_node204_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile26_node204_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node204 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,10] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile26_node204_route profile26_node204_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node205
  · exact profile26_node206
  · exact profile26_node207
  · exact profile26_node210
  · exact profile26_node211
  · exact profile26_node212

def profile26_node213_cert : Bound 7 := { allowed := (rows 0 80 64 81 0 0 0), upper := (rows 81 7 21 106 122 106 64), lower := (rows 81 7 21 8 16 32 64), losses := [] }

theorem profile26_node213 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,17] 6 106 profile26_node213_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,17] 6 106 profile26_node213_cert).mp (by decide +kernel))

def profile26_node214_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 7 22 105 121 105 64), lower := (rows 81 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 105 111 110 72 64 96 64) }] }

theorem profile26_node214 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,18] 6 105 profile26_node214_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,18] 6 105 profile26_node214_cert).mp (by decide +kernel))

def profile26_node215_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 7 28 107 115 99 64), lower := (rows 81 7 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 76 72 64 96 64) }] }

theorem profile26_node215 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,24] 6 99 profile26_node215_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,24] 6 99 profile26_node215_cert).mp (by decide +kernel))

def profile26_node216_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 7 37 90 90 122 64), lower := (rows 81 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 100 72 80 96 64) }] }

theorem profile26_node216 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,33] 6 90 profile26_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,33] 6 90 profile26_node216_cert).mp (by decide +kernel))

def profile26_node218_cert : Bound 7 := { allowed := (rows 0 80 81 64 0 0 0), upper := (rows 81 7 38 25 88 104 64), lower := (rows 81 7 38 25 16 32 64), losses := [] }

theorem profile26_node218 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,17] 6 72 profile26_node218_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,17] 6 72 profile26_node218_cert).mp (by decide +kernel))

def profile26_node219_cert : Bound 7 := { allowed := (rows 0 80 81 16 0 0 0), upper := (rows 81 7 38 73 24 56 64), lower := (rows 81 7 38 73 16 32 64), losses := [] }

theorem profile26_node219 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,65] 6 24 profile26_node219_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,65] 6 24 profile26_node219_cert).mp (by decide +kernel))

def profile26_node220_cert : Bound 7 := { allowed := (rows 0 80 81 1 0 0 0), upper := (rows 81 7 38 88 25 41 64), lower := (rows 81 7 38 88 16 32 64), losses := [] }

theorem profile26_node220 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,80] 6 9 profile26_node220_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34,80] 6 9 profile26_node220_cert).mp (by decide +kernel))

def profile26_node217_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node217_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node217 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,34] 6 (by decide) (choices 2) [17,65,80] profile26_node217_route profile26_node217_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node218
  · exact profile26_node219
  · exact profile26_node220

def profile26_node222_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 7 44 11 80 112 64), lower := (rows 81 7 44 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 112 118 124 126 112 112 112) }] }

theorem profile26_node222 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,3] 6 80 profile26_node222_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,3] 6 80 profile26_node222_cert).mp (by decide +kernel))

def profile26_node223_cert : Bound 7 := { allowed := (rows 0 80 81 64 0 0 0), upper := (rows 81 7 44 25 82 98 64), lower := (rows 81 7 44 25 16 32 64), losses := [] }

theorem profile26_node223 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,17] 6 66 profile26_node223_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,17] 6 66 profile26_node223_cert).mp (by decide +kernel))

def profile26_node224_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 81 7 44 26 81 97 64), lower := (rows 81 7 44 26 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 35 127), good := (rows 97 103 108 110 64 96 64) }] }

theorem profile26_node224 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,18] 6 65 profile26_node224_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,18] 6 65 profile26_node224_cert).mp (by decide +kernel))

def profile26_node225_cert : Bound 7 := { allowed := (rows 0 80 81 16 0 0 0), upper := (rows 81 7 44 73 18 50 64), lower := (rows 81 7 44 73 16 32 64), losses := [] }

theorem profile26_node225 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,65] 6 18 profile26_node225_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,65] 6 18 profile26_node225_cert).mp (by decide +kernel))

def profile26_node226_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 7 44 74 17 49 64), lower := (rows 81 7 44 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 78 108 74 80 96 64) }] }

theorem profile26_node226 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,66] 6 17 profile26_node226_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,66] 6 17 profile26_node226_cert).mp (by decide +kernel))

def profile26_node227_cert : Bound 7 := { allowed := (rows 0 80 81 1 0 0 0), upper := (rows 81 7 44 88 19 35 64), lower := (rows 81 7 44 88 16 32 64), losses := [] }

theorem profile26_node227 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,80] 6 3 profile26_node227_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40,80] 6 3 profile26_node227_cert).mp (by decide +kernel))

def profile26_node221_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node221_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node221 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,40] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile26_node221_route profile26_node221_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node222
  · exact profile26_node223
  · exact profile26_node224
  · exact profile26_node225
  · exact profile26_node226
  · exact profile26_node227

def profile26_node228_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 7 52 75 91 107 64), lower := (rows 81 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 100 72 64 96 64) }] }

theorem profile26_node228 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,48] 6 75 profile26_node228_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,48] 6 75 profile26_node228_cert).mp (by decide +kernel))

def profile26_node229_cert : Bound 7 := { allowed := (rows 0 80 16 81 0 0 0), upper := (rows 81 7 69 58 58 58 64), lower := (rows 81 7 69 8 16 32 64), losses := [] }

theorem profile26_node229 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,65] 6 58 profile26_node229_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,65] 6 58 profile26_node229_cert).mp (by decide +kernel))

def profile26_node230_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 7 70 57 57 57 64), lower := (rows 81 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 70 70 72 80 96 64) }] }

theorem profile26_node230 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,66] 6 57 profile26_node230_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,66] 6 57 profile26_node230_cert).mp (by decide +kernel))

def profile26_node231_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 7 76 59 51 51 64), lower := (rows 81 7 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 80 70 76 76 80 96 64) }] }

theorem profile26_node231 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,72] 6 51 profile26_node231_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,72] 6 51 profile26_node231_cert).mp (by decide +kernel))

def profile26_node232_cert : Bound 7 := { allowed := (rows 0 80 1 81 0 0 0), upper := (rows 81 7 84 43 59 43 64), lower := (rows 81 7 84 8 16 32 64), losses := [] }

theorem profile26_node232 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,80] 6 43 profile26_node232_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,80] 6 43 profile26_node232_cert).mp (by decide +kernel))

def profile26_node233_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 7 100 27 27 59 64), lower := (rows 81 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 80 70 100 72 80 100 64) }] }

theorem profile26_node233 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,96] 6 27 profile26_node233_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5,96] 6 27 profile26_node233_cert).mp (by decide +kernel))

def profile26_node201_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile26_node201_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node201 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,5] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96] profile26_node201_route profile26_node201_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node202
  · exact profile26_node203
  · exact profile26_node204
  · exact profile26_node213
  · exact profile26_node214
  · exact profile26_node215
  · exact profile26_node216
  · exact profile26_node217
  · exact profile26_node221
  · exact profile26_node228
  · exact profile26_node229
  · exact profile26_node230
  · exact profile26_node231
  · exact profile26_node232
  · exact profile26_node233

def profile26_node236_cert : Bound 7 := { allowed := (rows 0 81 80 64 0 0 0), upper := (rows 81 14 7 25 112 96 64), lower := (rows 81 14 7 25 16 32 64), losses := [] }

theorem profile26_node236 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,17] 6 96 profile26_node236_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,17] 6 96 profile26_node236_cert).mp (by decide +kernel))

def profile26_node237_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 14 7 41 80 112 64), lower := (rows 81 14 7 41 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 32 127), good := (rows 65 78 71 111 64 96 64) }] }

theorem profile26_node237 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,33] 6 80 profile26_node237_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,33] 6 80 profile26_node237_cert).mp (by decide +kernel))

def profile26_node239_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 81 14 7 56 17 96 64), lower := (rows 81 14 7 56 17 32 64), losses := [{ target := 0, region := (rows 0 6 4 25 16 127 127), good := (rows 120 110 110 120 120 96 96) }] }

theorem profile26_node239 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48,1] 6 64 profile26_node239_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48,1] 6 64 profile26_node239_cert).mp (by decide +kernel))

def profile26_node240_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 14 7 56 80 33 64), lower := (rows 81 14 7 56 80 32 64), losses := [{ target := 0, region := (rows 0 2 4 40 127 32 127), good := (rows 80 94 86 120 80 120 80) }] }

theorem profile26_node240 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48,64] 6 1 profile26_node240_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48,64] 6 1 profile26_node240_cert).mp (by decide +kernel))

def profile26_node238_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile26_node238_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node238 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,48] 6 (by decide) (choices 1) [1,64] profile26_node238_route profile26_node238_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile26_node239
  · exact profile26_node240

def profile26_node241_cert : Bound 7 := { allowed := (rows 0 81 80 16 0 0 0), upper := (rows 81 14 7 73 48 48 64), lower := (rows 81 14 7 73 16 32 64), losses := [] }

theorem profile26_node241 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,65] 6 48 profile26_node241_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,65] 6 48 profile26_node241_cert).mp (by decide +kernel))

def profile26_node242_cert : Bound 7 := { allowed := (rows 0 81 80 1 0 0 0), upper := (rows 81 14 7 88 49 33 64), lower := (rows 81 14 7 88 16 32 64), losses := [] }

theorem profile26_node242 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,80] 6 33 profile26_node242_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,80] 6 33 profile26_node242_cert).mp (by decide +kernel))

def profile26_node243_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 14 7 104 17 49 64), lower := (rows 81 14 7 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 127), good := (rows 80 78 70 104 80 104 64) }] }

theorem profile26_node243 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,96] 6 17 profile26_node243_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3,96] 6 17 profile26_node243_cert).mp (by decide +kernel))

def profile26_node235_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile26_node235_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node235 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,3] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile26_node235_route profile26_node235_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node236
  · exact profile26_node237
  · exact profile26_node238
  · exact profile26_node241
  · exact profile26_node242
  · exact profile26_node243

def profile26_node244_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 21 107 115 99 64), lower := (rows 81 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 36 127), good := (rows 65 110 111 72 64 96 64) }] }

theorem profile26_node244 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,17] 6 99 profile26_node244_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,17] 6 99 profile26_node244_cert).mp (by decide +kernel))

def profile26_node245_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 14 22 105 113 97 64), lower := (rows 81 14 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 78 70 72 64 96 64) }] }

theorem profile26_node245 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,18] 6 97 profile26_node245_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,18] 6 97 profile26_node245_cert).mp (by decide +kernel))

def profile26_node247_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 37 11 80 112 64), lower := (rows 81 14 37 11 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 32 127), good := (rows 65 78 111 75 64 96 64) }] }

theorem profile26_node247 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,3] 6 80 profile26_node247_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,3] 6 80 profile26_node247_cert).mp (by decide +kernel))

def profile26_node248_cert : Bound 7 := { allowed := (rows 0 81 80 64 0 0 0), upper := (rows 81 14 37 25 82 98 64), lower := (rows 81 14 37 25 16 32 64), losses := [] }

theorem profile26_node248 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,17] 6 66 profile26_node248_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,17] 6 66 profile26_node248_cert).mp (by decide +kernel))

def profile26_node249_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 81 14 37 26 81 97 64), lower := (rows 81 14 37 26 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 37 127), good := (rows 101 110 101 74 64 96 64) }] }

theorem profile26_node249 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,18] 6 65 profile26_node249_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,18] 6 65 profile26_node249_cert).mp (by decide +kernel))

def profile26_node250_cert : Bound 7 := { allowed := (rows 0 81 80 16 0 0 0), upper := (rows 81 14 37 73 18 50 64), lower := (rows 81 14 37 73 16 32 64), losses := [] }

theorem profile26_node250 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,65] 6 18 profile26_node250_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,65] 6 18 profile26_node250_cert).mp (by decide +kernel))

def profile26_node251_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 81 14 37 74 17 49 64), lower := (rows 81 14 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 14 16 32 127), good := (rows 80 78 110 74 80 96 64) }] }

theorem profile26_node251 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,66] 6 17 profile26_node251_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,66] 6 17 profile26_node251_cert).mp (by decide +kernel))

def profile26_node252_cert : Bound 7 := { allowed := (rows 0 81 80 1 0 0 0), upper := (rows 81 14 37 88 19 35 64), lower := (rows 81 14 37 88 16 32 64), losses := [] }

theorem profile26_node252 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,80] 6 3 profile26_node252_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33,80] 6 3 profile26_node252_cert).mp (by decide +kernel))

def profile26_node246_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node246_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node246 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile26_node246_route profile26_node246_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node247
  · exact profile26_node248
  · exact profile26_node249
  · exact profile26_node250
  · exact profile26_node251
  · exact profile26_node252

def profile26_node254_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 14 38 25 81 97 64), lower := (rows 81 14 38 25 16 32 64), losses := [{ target := 4, region := (rows 1 10 14 8 0 41 127), good := (rows 97 110 102 111 64 96 64) }] }

theorem profile26_node254 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,17] 6 65 profile26_node254_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,17] 6 65 profile26_node254_cert).mp (by decide +kernel))

def profile26_node255_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 14 38 73 17 49 64), lower := (rows 81 14 38 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 32 127), good := (rows 73 78 102 73 64 96 64) }] }

theorem profile26_node255 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,65] 6 17 profile26_node255_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,65] 6 17 profile26_node255_cert).mp (by decide +kernel))

def profile26_node256_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 14 38 88 17 33 64), lower := (rows 81 14 38 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 88 78 102 88 88 96 64) }] }

theorem profile26_node256 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,80] 6 1 profile26_node256_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34,80] 6 1 profile26_node256_cert).mp (by decide +kernel))

def profile26_node253_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node253_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node253 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,34] 6 (by decide) (choices 2) [17,65,80] profile26_node253_route profile26_node253_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node254
  · exact profile26_node255
  · exact profile26_node256

def profile26_node259_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 14 52 11 17 96 64), lower := (rows 81 14 52 11 17 32 64), losses := [{ target := 0, region := (rows 0 10 21 8 16 127 127), good := (rows 116 110 116 110 116 96 96) }] }

theorem profile26_node259 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3,1] 6 64 profile26_node259_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3,1] 6 64 profile26_node259_cert).mp (by decide +kernel))

def profile26_node260_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 14 52 11 80 33 64), lower := (rows 81 14 52 11 80 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 127 32 127), good := (rows 80 94 116 90 80 116 80) }] }

theorem profile26_node260 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3,64] 6 1 profile26_node260_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3,64] 6 1 profile26_node260_cert).mp (by decide +kernel))


#print axioms profile26_node260
end Delivery.SmallBudgetTenFinite7
