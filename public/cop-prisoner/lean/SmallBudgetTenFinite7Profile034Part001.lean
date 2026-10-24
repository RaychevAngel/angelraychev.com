import SmallBudgetTenFinite7Profile034Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile34_node132_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 38 13 104 80 112 64), lower := (rows 19 38 13 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 42 0 32 127), good := (rows 79 110 77 104 64 104 64) }] }

theorem profile34_node132 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,96] 6 80 profile34_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9,96] 6 80 profile34_node132_cert).mp (by decide +kernel))

def profile34_node129_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node129_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node129 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,9] 6 (by decide) (choices 2) [48,80,96] profile34_node129_route profile34_node129_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node130
  · exact profile34_node131
  · exact profile34_node132

def profile34_node133_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 38 21 104 120 104 64), lower := (rows 19 38 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 127 0 127 127), good := (rows 107 110 111 104 104 104 104) }] }

theorem profile34_node133 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,17] 6 104 profile34_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,17] 6 104 profile34_node133_cert).mp (by decide +kernel))

def profile34_node135_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 38 28 41 80 96 64), lower := (rows 19 38 28 41 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 9 0 127 127), good := (rows 107 102 110 105 96 96 96) }] }

theorem profile34_node135 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,33] 6 64 profile34_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,33] 6 64 profile34_node135_cert).mp (by decide +kernel))

def profile34_node136_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 38 28 73 112 96 64), lower := (rows 19 38 28 73 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 9 0 127 127), good := (rows 107 102 110 105 96 96 96) }] }

theorem profile34_node136 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,65] 6 96 profile34_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,65] 6 96 profile34_node136_cert).mp (by decide +kernel))

def profile34_node137_cert : Bound 7 := { allowed := (rows 96 80 96 0 0 0 0), upper := (rows 19 38 28 104 81 97 64), lower := (rows 19 38 28 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 43 0 33 127), good := (rows 107 110 76 104 64 104 64) }] }

theorem profile34_node137 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,96] 6 65 profile34_node137_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24,96] 6 65 profile34_node137_cert).mp (by decide +kernel))

def profile34_node134_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node134_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node134 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,24] 6 (by decide) (choices 2) [33,65,96] profile34_node134_route profile34_node134_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node135
  · exact profile34_node136
  · exact profile34_node137

def profile34_node138_cert : CutBound 7 := { lost := (rows 32 16 0 32 0 0 0), upper := (rows 19 38 37 88 88 120 64), lower := (rows 19 38 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 102 103 72 64 96 64) },{ target := 5, region := (rows 3 2 4 127 127 0 127), good := (rows 91 95 93 88 88 88 88) }] }

theorem profile34_node138 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,33] 6 88 profile34_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,33] 6 88 profile34_node138_cert).mp (by decide +kernel))

def profile34_node139_cert : CutBound 7 := { lost := (rows 32 16 0 32 0 0 0), upper := (rows 19 38 44 89 81 113 64), lower := (rows 19 38 44 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 102 110 72 64 96 64) },{ target := 5, region := (rows 3 2 4 11 19 0 127), good := (rows 91 95 76 72 80 64 64) }] }

theorem profile34_node139 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,40] 6 81 profile34_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,40] 6 81 profile34_node139_cert).mp (by decide +kernel))

def profile34_node140_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 38 52 73 89 105 64), lower := (rows 19 38 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 9 0 33 127), good := (rows 107 102 102 72 64 96 64) }] }

theorem profile34_node140 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,48] 6 73 profile34_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,48] 6 73 profile34_node140_cert).mp (by decide +kernel))

def profile34_node141_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 19 38 69 120 120 120 64), lower := (rows 19 38 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 71 102 69 72 64 96 64) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 87 70 69 72 80 64 64) }] }

theorem profile34_node141 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,65] 6 120 profile34_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,65] 6 120 profile34_node141_cert).mp (by decide +kernel))

def profile34_node142_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 19 38 76 121 113 113 64), lower := (rows 19 38 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 67 102 76 76 64 96 64) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 83 70 76 76 80 64 64) }] }

theorem profile34_node142 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,72] 6 113 profile34_node142_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,72] 6 113 profile34_node142_cert).mp (by decide +kernel))

def profile34_node143_cert : CutBound 7 := { lost := (rows 0 0 32 16 0 0 0), upper := (rows 19 38 84 105 121 105 64), lower := (rows 19 38 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 107 102 68 72 64 96 64) },{ target := 5, region := (rows 1 2 21 8 16 0 127), good := (rows 87 70 84 72 84 64 64) }] }

theorem profile34_node143 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,80] 6 105 profile34_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,80] 6 105 profile34_node143_cert).mp (by decide +kernel))

def profile34_node144_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 38 100 89 89 121 64), lower := (rows 19 38 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 71 102 102 72 64 102 64) }] }

theorem profile34_node144 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,96] 6 89 profile34_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36,96] 6 89 profile34_node144_cert).mp (by decide +kernel))

def profile34_node128_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node128_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node128 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,36] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile34_node128_route profile34_node128_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node129
  · exact profile34_node133
  · exact profile34_node134
  · exact profile34_node138
  · exact profile34_node139
  · exact profile34_node140
  · exact profile34_node141
  · exact profile34_node142
  · exact profile34_node143
  · exact profile34_node144

def profile34_node145_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 50 109 109 125 109 64), lower := (rows 19 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 98 68 72 64 96 64) }] }

theorem profile34_node145 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,48] 6 109 profile34_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,48] 6 109 profile34_node145_cert).mp (by decide +kernel))

def profile34_node146_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 19 67 124 124 124 124 64), lower := (rows 19 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile34_node146 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,65] 6 124 profile34_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,65] 6 124 profile34_node146_cert).mp (by decide +kernel))

def profile34_node147_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 19 70 125 121 121 121 64), lower := (rows 19 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 67 70 70 72 64 96 64) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 83 70 70 72 80 64 64) }] }

theorem profile34_node147 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,68] 6 121 profile34_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,68] 6 121 profile34_node147_cert).mp (by decide +kernel))

def profile34_node148_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 19 82 109 109 125 109 64), lower := (rows 19 82 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 127), good := (rows 111 66 68 72 64 96 64) }] }

theorem profile34_node148 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,80] 6 109 profile34_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,80] 6 109 profile34_node148_cert).mp (by decide +kernel))

def profile34_node151_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 19 98 13 28 112 96 64), lower := (rows 19 98 13 28 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 111 110 98 98 98) },{ target := 5, region := (rows 1 2 5 9 16 0 127), good := (rows 95 66 77 92 80 64 64) }] }

theorem profile34_node151 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,20] 6 96 profile34_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,20] 6 96 profile34_node151_cert).mp (by decide +kernel))

def profile34_node152_cert : CutBound 7 := { lost := (rows 32 16 0 0 0 0 0), upper := (rows 19 98 13 44 80 112 64), lower := (rows 19 98 13 44 16 32 64), losses := [{ target := 4, region := (rows 1 42 4 8 0 32 127), good := (rows 67 98 79 110 64 98 64) },{ target := 5, region := (rows 3 2 4 8 127 0 127), good := (rows 83 83 93 92 80 80 80) }] }

theorem profile34_node152 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,36] 6 80 profile34_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,36] 6 80 profile34_node152_cert).mp (by decide +kernel))

def profile34_node153_cert : Bound 7 := { allowed := (rows 96 0 112 64 0 0 0), upper := (rows 19 98 13 56 84 100 64), lower := (rows 19 98 13 56 16 32 64), losses := [{ target := 4, region := (rows 1 46 4 8 0 36 127), good := (rows 67 98 111 106 64 98 64) }] }

theorem profile34_node153 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,48] 6 68 profile34_node153_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,48] 6 68 profile34_node153_cert).mp (by decide +kernel))

def profile34_node154_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 19 98 13 76 48 48 64), lower := (rows 19 98 13 76 16 32 64), losses := [{ target := 4, region := (rows 1 34 5 13 0 32 127), good := (rows 79 98 77 76 64 98 64) }] }

theorem profile34_node154 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,68] 6 48 profile34_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,68] 6 48 profile34_node154_cert).mp (by decide +kernel))

def profile34_node155_cert : Bound 7 := { allowed := (rows 96 0 112 32 0 0 0), upper := (rows 19 98 13 88 52 36 64), lower := (rows 19 98 13 88 16 32 64), losses := [{ target := 4, region := (rows 1 38 4 8 0 36 127), good := (rows 67 98 111 72 64 98 64) }] }

theorem profile34_node155 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,80] 6 36 profile34_node155_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,80] 6 36 profile34_node155_cert).mp (by decide +kernel))

def profile34_node156_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 19 98 13 104 20 52 64), lower := (rows 19 98 13 104 16 32 64), losses := [{ target := 4, region := (rows 1 42 5 42 0 32 127), good := (rows 79 106 79 106 64 106 64) }] }

theorem profile34_node156 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,96] 6 20 profile34_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9,96] 6 20 profile34_node156_cert).mp (by decide +kernel))

def profile34_node150_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node150_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node150 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,9] 6 (by decide) (choices 2) [20,36,48,68,80,96] profile34_node150_route profile34_node150_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node151
  · exact profile34_node152
  · exact profile34_node153
  · exact profile34_node154
  · exact profile34_node155
  · exact profile34_node156

def profile34_node157_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 98 21 108 124 108 64), lower := (rows 19 98 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 4 12 0 36 127), good := (rows 67 98 111 72 64 98 64) }] }

theorem profile34_node157 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,17] 6 108 profile34_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,17] 6 108 profile34_node157_cert).mp (by decide +kernel))

def profile34_node159_cert : CutBound 7 := { lost := (rows 0 16 32 32 0 0 0), upper := (rows 19 98 28 13 112 96 64), lower := (rows 19 98 28 13 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 110 111 98 98 98) },{ target := 5, region := (rows 1 2 5 9 16 0 127), good := (rows 95 66 92 77 80 64 64) }] }

theorem profile34_node159 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,5] 6 96 profile34_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,5] 6 96 profile34_node159_cert).mp (by decide +kernel))

def profile34_node160_cert : Bound 7 := { allowed := (rows 96 0 96 80 0 0 0), upper := (rows 19 98 28 41 84 100 64), lower := (rows 19 98 28 41 16 32 64), losses := [{ target := 4, region := (rows 1 46 4 8 0 36 127), good := (rows 67 98 110 107 64 98 64) }] }

theorem profile34_node160 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,33] 6 68 profile34_node160_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,33] 6 68 profile34_node160_cert).mp (by decide +kernel))

def profile34_node161_cert : Bound 7 := { allowed := (rows 96 0 96 80 0 0 0), upper := (rows 19 98 28 44 81 97 64), lower := (rows 19 98 28 44 16 32 64), losses := [{ target := 4, region := (rows 1 43 4 8 0 33 127), good := (rows 99 98 78 110 64 98 64) }] }

theorem profile34_node161 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,36] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,36] 6 65 profile34_node161_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,36] 6 65 profile34_node161_cert).mp (by decide +kernel))

def profile34_node162_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 98 28 73 52 36 64), lower := (rows 19 98 28 73 16 32 64), losses := [{ target := 4, region := (rows 1 38 4 9 0 36 127), good := (rows 75 98 110 73 64 98 64) }] }

theorem profile34_node162 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,65] 6 36 profile34_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,65] 6 36 profile34_node162_cert).mp (by decide +kernel))

def profile34_node163_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 98 28 76 49 33 64), lower := (rows 19 98 28 76 16 32 64), losses := [{ target := 4, region := (rows 1 35 4 12 0 33 127), good := (rows 99 98 76 76 64 98 64) }] }

theorem profile34_node163 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,68] 6 33 profile34_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,68] 6 33 profile34_node163_cert).mp (by decide +kernel))

def profile34_node164_cert : Bound 7 := { allowed := (rows 96 16 96 16 0 0 0), upper := (rows 19 98 28 104 21 37 64), lower := (rows 19 98 28 104 16 32 64), losses := [] }

theorem profile34_node164 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,96] 6 5 profile34_node164_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24,96] 6 5 profile34_node164_cert).mp (by decide +kernel))

def profile34_node158_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node158_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node158 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,24] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile34_node158_route profile34_node158_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node159
  · exact profile34_node160
  · exact profile34_node161
  · exact profile34_node162
  · exact profile34_node163
  · exact profile34_node164

def profile34_node165_cert : CutBound 7 := { lost := (rows 0 16 0 32 0 0 0), upper := (rows 19 98 37 92 92 124 64), lower := (rows 19 98 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 4 8 0 32 127), good := (rows 67 98 103 72 64 98 64) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 83 66 93 72 80 64 64) }] }

theorem profile34_node165 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,33] 6 92 profile34_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,33] 6 92 profile34_node165_cert).mp (by decide +kernel))

def profile34_node167_cert : CutBound 7 := { lost := (rows 32 16 0 0 0 0 0), upper := (rows 19 98 44 13 80 112 64), lower := (rows 19 98 44 13 16 32 64), losses := [{ target := 4, region := (rows 1 38 4 8 0 32 127), good := (rows 67 98 110 79 64 98 64) },{ target := 5, region := (rows 3 2 4 8 127 0 127), good := (rows 83 83 92 93 80 80 80) }] }

theorem profile34_node167 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,5] 6 80 profile34_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,5] 6 80 profile34_node167_cert).mp (by decide +kernel))

def profile34_node168_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 98 44 25 84 100 64), lower := (rows 19 98 44 25 16 32 64), losses := [{ target := 4, region := (rows 1 46 12 8 0 44 127), good := (rows 67 98 110 111 64 98 64) }] }

theorem profile34_node168 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,17] 6 68 profile34_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,17] 6 68 profile34_node168_cert).mp (by decide +kernel))

def profile34_node169_cert : Bound 7 := { allowed := (rows 96 0 80 96 0 0 0), upper := (rows 19 98 44 28 81 97 64), lower := (rows 19 98 44 28 16 32 64), losses := [{ target := 4, region := (rows 1 39 4 8 0 33 127), good := (rows 99 98 110 78 64 98 64) }] }

theorem profile34_node169 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,20] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,20] 6 65 profile34_node169_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,20] 6 65 profile34_node169_cert).mp (by decide +kernel))

def profile34_node170_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 19 98 44 73 20 52 64), lower := (rows 19 98 44 73 16 32 64), losses := [{ target := 4, region := (rows 1 38 4 9 0 32 127), good := (rows 75 98 110 73 64 98 64) }] }

theorem profile34_node170 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,65] 6 20 profile34_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,65] 6 20 profile34_node170_cert).mp (by decide +kernel))

def profile34_node171_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 19 98 44 76 17 49 64), lower := (rows 19 98 44 76 16 32 64), losses := [{ target := 4, region := (rows 1 38 38 47 0 32 127), good := (rows 79 110 110 78 64 110 64) }] }

theorem profile34_node171 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,68] 6 17 profile34_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,68] 6 17 profile34_node171_cert).mp (by decide +kernel))

def profile34_node172_cert : Bound 7 := { allowed := (rows 96 16 80 32 0 0 0), upper := (rows 19 98 44 88 21 37 64), lower := (rows 19 98 44 88 16 32 64), losses := [] }

theorem profile34_node172 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,80] 6 5 profile34_node172_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40,80] 6 5 profile34_node172_cert).mp (by decide +kernel))

def profile34_node166_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile34_node166_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node166 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,40] 6 (by decide) (choices 2) [5,17,20,65,68,80] profile34_node166_route profile34_node166_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node167
  · exact profile34_node168
  · exact profile34_node169
  · exact profile34_node170
  · exact profile34_node171
  · exact profile34_node172

def profile34_node173_cert : Bound 7 := { allowed := (rows 96 0 64 112 0 0 0), upper := (rows 19 98 52 77 93 109 64), lower := (rows 19 98 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 4 8 0 32 127), good := (rows 67 98 102 72 64 98 64) }] }

theorem profile34_node173 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,48] 6 77 profile34_node173_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,48] 6 77 profile34_node173_cert).mp (by decide +kernel))

def profile34_node174_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 98 69 60 60 60 64), lower := (rows 19 98 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 34 5 8 0 32 127), good := (rows 71 98 69 72 64 98 64) }] }

theorem profile34_node174 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,65] 6 60 profile34_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,65] 6 60 profile34_node174_cert).mp (by decide +kernel))

def profile34_node175_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 98 76 61 53 53 64), lower := (rows 19 98 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 34 12 8 0 32 127), good := (rows 67 98 76 76 64 98 64) }] }

theorem profile34_node175 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,72] 6 53 profile34_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,72] 6 53 profile34_node175_cert).mp (by decide +kernel))

def profile34_node176_cert : Bound 7 := { allowed := (rows 96 0 32 112 0 0 0), upper := (rows 19 98 84 45 61 45 64), lower := (rows 19 98 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 67 98 68 72 64 98 64) }] }

theorem profile34_node176 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,80] 6 45 profile34_node176_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,80] 6 45 profile34_node176_cert).mp (by decide +kernel))

def profile34_node177_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 19 98 100 29 29 61 64), lower := (rows 19 98 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 71 102 102 72 64 102 64) }] }

theorem profile34_node177 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,96] 6 29 profile34_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96,96] 6 29 profile34_node177_cert).mp (by decide +kernel))

def profile34_node149_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node149_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node149 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18,96] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile34_node149_route profile34_node149_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node150
  · exact profile34_node157
  · exact profile34_node158
  · exact profile34_node165
  · exact profile34_node166
  · exact profile34_node173
  · exact profile34_node174
  · exact profile34_node175
  · exact profile34_node176
  · exact profile34_node177

def profile34_node80_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile34_node80_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile34_node80 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [18] 6 (by decide) (choices 2) [5,12,17,20,33,36,48,65,68,80,96] profile34_node80_route profile34_node80_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node81
  · exact profile34_node94
  · exact profile34_node113
  · exact profile34_node114
  · exact profile34_node115
  · exact profile34_node128
  · exact profile34_node145
  · exact profile34_node146
  · exact profile34_node147
  · exact profile34_node148
  · exact profile34_node149

def profile34_node181_cert : CutBound 7 := { lost := (rows 64 64 64 64 0 0 0), upper := (rows 49 7 14 56 80 96 64), lower := (rows 49 7 14 56 16 32 64), losses := [{ target := 6, region := (rows 9 15 15 9 16 32 0), good := (rows 63 15 15 63 16 32 0) }] }

theorem profile34_node181 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10,48] 6 64 profile34_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10,48] 6 64 profile34_node181_cert).mp (by decide +kernel))

def profile34_node182_cert : CutBound 7 := { lost := (rows 0 32 32 32 0 0 0), upper := (rows 49 7 14 88 112 96 64), lower := (rows 49 7 14 88 16 32 64), losses := [{ target := 5, region := (rows 1 3 7 25 16 0 127), good := (rows 95 79 78 88 88 64 64) }] }

theorem profile34_node182 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10,80] 6 96 profile34_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10,80] 6 96 profile34_node182_cert).mp (by decide +kernel))

def profile34_node180_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node180_route : Route 7 := (fun mask => match mask with | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node180 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,10] 6 (by decide) (choices 2) [48,80] profile34_node180_route profile34_node180_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node181
  · exact profile34_node182

def profile34_node183_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 7 22 104 120 104 64), lower := (rows 49 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 105 111 110 104 104 104 104) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 71 86 72 80 64 64) }] }

theorem profile34_node183 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,18] 6 104 profile34_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,18] 6 104 profile34_node183_cert).mp (by decide +kernel))

def profile34_node185_cert : CutBound 7 := { lost := (rows 0 0 32 16 0 0 0), upper := (rows 49 7 28 42 80 96 64), lower := (rows 49 7 28 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 111 108 106 96 96 96) },{ target := 5, region := (rows 1 2 12 8 127 0 127), good := (rows 81 87 92 94 80 80 80) }] }

theorem profile34_node185 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,34] 6 64 profile34_node185_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,34] 6 64 profile34_node185_cert).mp (by decide +kernel))

def profile34_node186_cert : CutBound 7 := { lost := (rows 0 32 32 48 0 0 0), upper := (rows 49 7 28 74 112 96 64), lower := (rows 49 7 28 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 111 108 106 96 96 96) },{ target := 5, region := (rows 1 3 5 11 16 0 127), good := (rows 95 79 92 74 80 64 64) }] }

theorem profile34_node186 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,66] 6 96 profile34_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,66] 6 96 profile34_node186_cert).mp (by decide +kernel))

def profile34_node187_cert : Bound 7 := { allowed := (rows 64 112 96 0 0 0 0), upper := (rows 49 7 28 104 82 98 64), lower := (rows 49 7 28 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 43 0 34 127), good := (rows 105 111 76 104 64 104 64) }] }

theorem profile34_node187 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,96] 6 66 profile34_node187_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24,96] 6 66 profile34_node187_cert).mp (by decide +kernel))

def profile34_node184_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node184_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node184 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,24] 6 (by decide) (choices 2) [34,66,96] profile34_node184_route profile34_node184_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node185
  · exact profile34_node186
  · exact profile34_node187

def profile34_node188_cert : CutBound 7 := { lost := (rows 0 0 0 48 0 0 0), upper := (rows 49 7 52 74 90 106 64), lower := (rows 49 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 97 111 100 72 64 96 64) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 81 95 84 72 80 64 64) }] }

theorem profile34_node188 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,48] 6 74 profile34_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,48] 6 74 profile34_node188_cert).mp (by decide +kernel))

def profile34_node189_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 7 70 120 120 120 64), lower := (rows 49 7 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) }] }

theorem profile34_node189 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,66] 6 120 profile34_node189_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,66] 6 120 profile34_node189_cert).mp (by decide +kernel))

def profile34_node190_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 49 7 76 122 114 114 64), lower := (rows 49 7 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 97 71 76 76 64 96 64) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 81 71 76 76 80 64 64) }] }

theorem profile34_node190 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,72] 6 114 profile34_node190_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,72] 6 114 profile34_node190_cert).mp (by decide +kernel))

def profile34_node191_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 7 84 106 122 106 64), lower := (rows 49 7 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 97 111 68 72 64 96 64) },{ target := 5, region := (rows 1 3 21 8 16 0 127), good := (rows 87 71 84 72 84 64 64) }] }

theorem profile34_node191 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,80] 6 106 profile34_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5,80] 6 106 profile34_node191_cert).mp (by decide +kernel))

def profile34_node179_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | _ => 0

def profile34_node179_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node179 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,5] 6 (by decide) (choices 2) [10,18,24,48,66,72,80] profile34_node179_route profile34_node179_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node180
  · exact profile34_node183
  · exact profile34_node184
  · exact profile34_node188
  · exact profile34_node189
  · exact profile34_node190
  · exact profile34_node191

def profile34_node194_cert : CutBound 7 := { lost := (rows 64 64 64 64 0 0 0), upper := (rows 49 14 7 56 80 96 64), lower := (rows 49 14 7 56 16 32 64), losses := [{ target := 6, region := (rows 9 15 15 9 16 32 0), good := (rows 63 15 15 63 16 32 0) }] }

theorem profile34_node194 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3,48] 6 64 profile34_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3,48] 6 64 profile34_node194_cert).mp (by decide +kernel))

def profile34_node195_cert : CutBound 7 := { lost := (rows 0 32 32 32 0 0 0), upper := (rows 49 14 7 88 112 96 64), lower := (rows 49 14 7 88 16 32 64), losses := [{ target := 5, region := (rows 1 7 5 25 16 0 127), good := (rows 95 78 79 88 88 64 64) }] }

theorem profile34_node195 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3,80] 6 96 profile34_node195_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3,80] 6 96 profile34_node195_cert).mp (by decide +kernel))

def profile34_node193_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node193_route : Route 7 := (fun mask => match mask with | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node193 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,3] 6 (by decide) (choices 2) [48,80] profile34_node193_route profile34_node193_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile34_node194
  · exact profile34_node195

def profile34_node196_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 49 14 21 106 114 98 64), lower := (rows 49 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 14 0 38 127), good := (rows 97 110 111 72 64 96 64) }] }

theorem profile34_node196 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,17] 6 98 profile34_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,17] 6 98 profile34_node196_cert).mp (by decide +kernel))

def profile34_node198_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 14 22 41 80 96 64), lower := (rows 49 14 22 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 105 110 102 105 96 96 96) },{ target := 5, region := (rows 1 10 14 8 127 0 127), good := (rows 81 94 86 95 80 80 80) }] }

theorem profile34_node198 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,33] 6 64 profile34_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,33] 6 64 profile34_node198_cert).mp (by decide +kernel))

def profile34_node199_cert : CutBound 7 := { lost := (rows 0 32 32 48 0 0 0), upper := (rows 49 14 22 73 112 96 64), lower := (rows 49 14 22 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 105 110 102 105 96 96 96) },{ target := 5, region := (rows 1 11 5 9 16 0 127), good := (rows 95 78 86 79 80 64 64) }] }

theorem profile34_node199 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,65] 6 96 profile34_node199_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,65] 6 96 profile34_node199_cert).mp (by decide +kernel))

def profile34_node200_cert : Bound 7 := { allowed := (rows 64 112 96 0 0 0 0), upper := (rows 49 14 22 104 81 97 64), lower := (rows 49 14 22 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 41 0 33 127), good := (rows 105 78 70 104 64 104 64) }] }

theorem profile34_node200 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,96] 6 65 profile34_node200_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18,96] 6 65 profile34_node200_cert).mp (by decide +kernel))

def profile34_node197_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node197_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node197 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,18] 6 (by decide) (choices 2) [33,65,96] profile34_node197_route profile34_node197_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node198
  · exact profile34_node199
  · exact profile34_node200

def profile34_node201_cert : CutBound 7 := { lost := (rows 64 0 64 0 0 0 0), upper := (rows 49 14 52 75 83 99 64), lower := (rows 49 14 52 8 16 32 64), losses := [{ target := 6, region := (rows 5 2 5 8 16 32 0), good := (rows 53 15 53 8 16 32 0) }] }

theorem profile34_node201 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,48] 6 67 profile34_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,48] 6 67 profile34_node201_cert).mp (by decide +kernel))

def profile34_node202_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 49 14 69 122 114 114 64), lower := (rows 49 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 78 69 72 64 96 64) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 85 78 69 72 80 64 64) }] }

theorem profile34_node202 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,65] 6 114 profile34_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,65] 6 114 profile34_node202_cert).mp (by decide +kernel))

def profile34_node203_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 49 14 70 121 113 113 64), lower := (rows 49 14 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 14 8 0 32 127), good := (rows 97 78 70 78 64 96 64) }] }

theorem profile34_node203 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,66] 6 113 profile34_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,66] 6 113 profile34_node203_cert).mp (by decide +kernel))

def profile34_node205_cert : CutBound 7 := { lost := (rows 0 32 32 32 0 0 0), upper := (rows 49 14 84 11 112 96 64), lower := (rows 49 14 84 11 16 32 64), losses := [{ target := 5, region := (rows 1 11 21 9 16 0 127), good := (rows 95 78 84 79 84 64 64) }] }

theorem profile34_node205 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,3] 6 96 profile34_node205_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,3] 6 96 profile34_node205_cert).mp (by decide +kernel))

def profile34_node206_cert : Bound 7 := { allowed := (rows 64 112 32 64 0 0 0), upper := (rows 49 14 84 41 82 98 64), lower := (rows 49 14 84 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 34 127), good := (rows 105 110 68 105 64 96 64) }] }

theorem profile34_node206 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,33] 6 66 profile34_node206_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,33] 6 66 profile34_node206_cert).mp (by decide +kernel))

def profile34_node207_cert : Bound 7 := { allowed := (rows 64 112 0 80 0 0 0), upper := (rows 49 14 84 42 81 97 64), lower := (rows 49 14 84 42 16 32 64), losses := [{ target := 5, region := (rows 1 2 21 8 17 0 127), good := (rows 85 78 84 74 84 64 64) }] }

theorem profile34_node207 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,34] 6 65 profile34_node207_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,34] 6 65 profile34_node207_cert).mp (by decide +kernel))

def profile34_node208_cert : Bound 7 := { allowed := (rows 64 112 32 32 0 0 0), upper := (rows 49 14 84 73 50 34 64), lower := (rows 49 14 84 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 34 127), good := (rows 105 110 68 73 64 96 64) }] }

theorem profile34_node208 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,65] 6 34 profile34_node208_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,65] 6 34 profile34_node208_cert).mp (by decide +kernel))

def profile34_node209_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 49 14 84 74 49 33 64), lower := (rows 49 14 84 74 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 14 0 33 127), good := (rows 97 78 78 74 64 96 64) }] }

theorem profile34_node209 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,66] 6 33 profile34_node209_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,66] 6 33 profile34_node209_cert).mp (by decide +kernel))

def profile34_node210_cert : Bound 7 := { allowed := (rows 64 112 32 16 0 0 0), upper := (rows 49 14 84 104 19 35 64), lower := (rows 49 14 84 104 16 32 64), losses := [] }

theorem profile34_node210 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,96] 6 3 profile34_node210_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80,96] 6 3 profile34_node210_cert).mp (by decide +kernel))

def profile34_node204_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node204_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node204 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12,80] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile34_node204_route profile34_node204_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node205
  · exact profile34_node206
  · exact profile34_node207
  · exact profile34_node208
  · exact profile34_node209
  · exact profile34_node210

def profile34_node192_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile34_node192_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node192 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,12] 6 (by decide) (choices 2) [3,17,18,48,65,66,80] profile34_node192_route profile34_node192_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node193
  · exact profile34_node196
  · exact profile34_node197
  · exact profile34_node201
  · exact profile34_node202
  · exact profile34_node203
  · exact profile34_node204

def profile34_node211_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 19 110 110 126 110 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 97 111 68 72 64 96 64) }] }

theorem profile34_node211 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,17] 6 110 profile34_node211_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,17] 6 110 profile34_node211_cert).mp (by decide +kernel))

def profile34_node213_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 22 7 104 120 104 64), lower := (rows 49 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 105 110 111 104 104 104 104) },{ target := 5, region := (rows 1 3 5 8 16 0 127), good := (rows 87 86 71 72 80 64 64) }] }

theorem profile34_node213 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,3] 6 104 profile34_node213_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,3] 6 104 profile34_node213_cert).mp (by decide +kernel))

def profile34_node215_cert : CutBound 7 := { lost := (rows 0 32 0 16 0 0 0), upper := (rows 49 22 13 42 80 96 64), lower := (rows 49 22 13 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 110 109 106 96 96 96) },{ target := 5, region := (rows 1 6 4 8 127 0 127), good := (rows 81 86 95 90 80 80 80) }] }

theorem profile34_node215 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,34] 6 64 profile34_node215_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,34] 6 64 profile34_node215_cert).mp (by decide +kernel))

def profile34_node216_cert : CutBound 7 := { lost := (rows 0 32 32 48 0 0 0), upper := (rows 49 22 13 74 112 96 64), lower := (rows 49 22 13 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 127 127), good := (rows 97 110 109 106 96 96 96) },{ target := 5, region := (rows 1 3 5 15 16 0 127), good := (rows 95 94 79 74 80 64 64) }] }

theorem profile34_node216 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,66] 6 96 profile34_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,66] 6 96 profile34_node216_cert).mp (by decide +kernel))

def profile34_node217_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 22 13 104 82 98 64), lower := (rows 49 22 13 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 43 0 34 127), good := (rows 109 110 77 104 64 104 64) }] }

theorem profile34_node217 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,96] 6 66 profile34_node217_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9,96] 6 66 profile34_node217_cert).mp (by decide +kernel))

def profile34_node214_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node214_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node214 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,9] 6 (by decide) (choices 2) [34,66,96] profile34_node214_route profile34_node214_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node215
  · exact profile34_node216
  · exact profile34_node217

def profile34_node219_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 22 14 41 80 96 64), lower := (rows 49 22 14 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 105 102 110 105 96 96 96) },{ target := 5, region := (rows 1 14 12 8 127 0 127), good := (rows 81 86 94 95 80 80 80) }] }

theorem profile34_node219 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,33] 6 64 profile34_node219_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,33] 6 64 profile34_node219_cert).mp (by decide +kernel))

def profile34_node220_cert : CutBound 7 := { lost := (rows 0 32 32 48 0 0 0), upper := (rows 49 22 14 73 112 96 64), lower := (rows 49 22 14 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 127 127), good := (rows 105 102 110 105 96 96 96) },{ target := 5, region := (rows 1 3 13 9 16 0 127), good := (rows 95 86 78 79 80 64 64) }] }

theorem profile34_node220 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,65] 6 96 profile34_node220_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,65] 6 96 profile34_node220_cert).mp (by decide +kernel))

def profile34_node221_cert : Bound 7 := { allowed := (rows 64 96 112 0 0 0 0), upper := (rows 49 22 14 104 81 97 64), lower := (rows 49 22 14 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 41 0 33 127), good := (rows 105 70 78 104 64 104 64) }] }

theorem profile34_node221 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,96] 6 65 profile34_node221_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10,96] 6 65 profile34_node221_cert).mp (by decide +kernel))

def profile34_node218_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node218_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node218 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,10] 6 (by decide) (choices 2) [33,65,96] profile34_node218_route profile34_node218_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node219
  · exact profile34_node220
  · exact profile34_node221

def profile34_node222_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 22 37 74 90 106 64), lower := (rows 49 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 127), good := (rows 101 110 101 72 64 96 64) }] }

theorem profile34_node222 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,33] 6 74 profile34_node222_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,33] 6 74 profile34_node222_cert).mp (by decide +kernel))

def profile34_node223_cert : CutBound 7 := { lost := (rows 0 0 0 48 0 0 0), upper := (rows 49 22 38 73 89 105 64), lower := (rows 49 22 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 102 72 64 96 64) },{ target := 5, region := (rows 1 2 4 9 17 0 127), good := (rows 89 86 70 72 80 64 64) }] }

theorem profile34_node223 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,34] 6 73 profile34_node223_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,34] 6 73 profile34_node223_cert).mp (by decide +kernel))

def profile34_node225_cert : CutBound 7 := { lost := (rows 0 32 16 0 0 0 0), upper := (rows 49 22 44 11 80 96 64), lower := (rows 49 22 44 11 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 97 102 108 111 96 96 96) },{ target := 5, region := (rows 1 6 4 8 127 0 127), good := (rows 81 86 94 91 80 80 80) }] }

theorem profile34_node225 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,3] 6 64 profile34_node225_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,3] 6 64 profile34_node225_cert).mp (by decide +kernel))

def profile34_node226_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 22 44 73 82 98 64), lower := (rows 49 22 44 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 34 127), good := (rows 109 102 108 77 64 96 64) }] }

theorem profile34_node226 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,65] 6 66 profile34_node226_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,65] 6 66 profile34_node226_cert).mp (by decide +kernel))

def profile34_node227_cert : Bound 7 := { allowed := (rows 64 96 80 32 0 0 0), upper := (rows 49 22 44 74 81 97 64), lower := (rows 49 22 44 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 33 127), good := (rows 97 78 108 74 64 96 64) }] }

theorem profile34_node227 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,66] 6 65 profile34_node227_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40,66] 6 65 profile34_node227_cert).mp (by decide +kernel))

def profile34_node224_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile34_node224_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node224 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,40] 6 (by decide) (choices 2) [3,65,66] profile34_node224_route profile34_node224_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node225
  · exact profile34_node226
  · exact profile34_node227

def profile34_node228_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 22 69 106 122 106 64), lower := (rows 49 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 127), good := (rows 101 110 69 72 64 96 64) }] }

theorem profile34_node228 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,65] 6 106 profile34_node228_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,65] 6 106 profile34_node228_cert).mp (by decide +kernel))

def profile34_node229_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 22 70 105 121 105 64), lower := (rows 49 22 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 127), good := (rows 105 70 70 72 64 96 64) }] }

theorem profile34_node229 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,66] 6 105 profile34_node229_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,66] 6 105 profile34_node229_cert).mp (by decide +kernel))

def profile34_node230_cert : CutBound 7 := { lost := (rows 0 0 48 0 0 0 0), upper := (rows 49 22 76 107 115 99 64), lower := (rows 49 22 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 97 70 76 76 64 96 64) },{ target := 5, region := (rows 1 2 12 8 16 0 127), good := (rows 81 86 76 76 80 64 64) }] }

theorem profile34_node230 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,72] 6 99 profile34_node230_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,72] 6 99 profile34_node230_cert).mp (by decide +kernel))

def profile34_node231_cert : Bound 7 := { allowed := (rows 64 96 0 112 0 0 0), upper := (rows 49 22 100 75 91 107 64), lower := (rows 49 22 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 101 70 100 72 64 100 64) }] }

theorem profile34_node231 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,96] 6 75 profile34_node231_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20,96] 6 75 profile34_node231_cert).mp (by decide +kernel))

def profile34_node212_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node212_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node212 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,20] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile34_node212_route profile34_node212_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node213
  · exact profile34_node214
  · exact profile34_node218
  · exact profile34_node222
  · exact profile34_node223
  · exact profile34_node224
  · exact profile34_node228
  · exact profile34_node229
  · exact profile34_node230
  · exact profile34_node231

def profile34_node232_cert : CutBound 7 := { lost := (rows 64 64 0 0 0 0 0), upper := (rows 49 50 79 79 95 111 64), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 6, region := (rows 3 3 4 8 16 32 0), good := (rows 51 51 4 8 16 32 0) }] }

theorem profile34_node232 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,48] 6 79 profile34_node232_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,48] 6 79 profile34_node232_cert).mp (by decide +kernel))

def profile34_node233_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 49 67 126 126 126 126 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) },{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 67 68 72 80 64 64) }] }

theorem profile34_node233 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,65] 6 126 profile34_node233_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,65] 6 126 profile34_node233_cert).mp (by decide +kernel))

def profile34_node234_cert : CutBound 7 := { lost := (rows 0 48 0 0 0 0 0), upper := (rows 49 70 127 123 123 123 64), lower := (rows 49 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 97 70 70 72 64 96 64) },{ target := 5, region := (rows 1 6 4 8 16 0 127), good := (rows 81 70 70 72 80 64 64) }] }

theorem profile34_node234 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,68] 6 123 profile34_node234_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,68] 6 123 profile34_node234_cert).mp (by decide +kernel))

def profile34_node236_cert : CutBound 7 := { lost := (rows 0 32 32 16 0 0 0), upper := (rows 49 82 7 108 124 108 64), lower := (rows 49 82 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 97 66 111 72 64 96 64) },{ target := 5, region := (rows 1 19 5 8 16 0 127), good := (rows 87 82 71 72 82 64 64) }] }

theorem profile34_node236 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,3] 6 108 profile34_node236_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,3] 6 108 profile34_node236_cert).mp (by decide +kernel))

def profile34_node238_cert : CutBound 7 := { lost := (rows 0 32 32 32 0 0 0), upper := (rows 49 82 13 14 112 96 64), lower := (rows 49 82 13 14 16 32 64), losses := [{ target := 5, region := (rows 1 19 5 13 16 0 127), good := (rows 95 82 79 78 82 64 64) }] }

theorem profile34_node238 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,6] 6 96 profile34_node238_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,6] 6 96 profile34_node238_cert).mp (by decide +kernel))

def profile34_node239_cert : Bound 7 := { allowed := (rows 64 0 112 80 0 0 0), upper := (rows 49 82 13 42 84 100 64), lower := (rows 49 82 13 42 16 32 64), losses := [{ target := 5, region := (rows 1 23 4 8 20 0 127), good := (rows 83 82 95 74 82 64 64) }] }

theorem profile34_node239 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,34] 6 68 profile34_node239_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,34] 6 68 profile34_node239_cert).mp (by decide +kernel))

def profile34_node240_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 82 13 44 82 98 64), lower := (rows 49 82 13 44 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 34 127), good := (rows 109 98 77 108 64 96 64) }] }

theorem profile34_node240 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,36] 6 66 profile34_node240_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,36] 6 66 profile34_node240_cert).mp (by decide +kernel))

def profile34_node241_cert : Bound 7 := { allowed := (rows 64 32 112 32 0 0 0), upper := (rows 49 82 13 74 52 36 64), lower := (rows 49 82 13 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 36 127), good := (rows 97 74 109 74 64 96 64) }] }

theorem profile34_node241 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,66] 6 36 profile34_node241_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,66] 6 36 profile34_node241_cert).mp (by decide +kernel))

def profile34_node242_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 82 13 76 50 34 64), lower := (rows 49 82 13 76 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 13 0 34 127), good := (rows 109 98 77 76 64 96 64) }] }

theorem profile34_node242 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,68] 6 34 profile34_node242_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,68] 6 34 profile34_node242_cert).mp (by decide +kernel))

def profile34_node243_cert : Bound 7 := { allowed := (rows 64 32 112 16 0 0 0), upper := (rows 49 82 13 104 22 38 64), lower := (rows 49 82 13 104 16 32 64), losses := [] }

theorem profile34_node243 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,96] 6 6 profile34_node243_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9,96] 6 6 profile34_node243_cert).mp (by decide +kernel))

def profile34_node237_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node237_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node237 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,9] 6 (by decide) (choices 2) [6,34,36,66,68,96] profile34_node237_route profile34_node237_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node238
  · exact profile34_node239
  · exact profile34_node240
  · exact profile34_node241
  · exact profile34_node242
  · exact profile34_node243

def profile34_node245_cert : CutBound 7 := { lost := (rows 0 32 32 32 0 0 0), upper := (rows 49 82 14 13 112 96 64), lower := (rows 49 82 14 13 16 32 64), losses := [{ target := 5, region := (rows 1 19 13 9 16 0 127), good := (rows 95 82 78 79 82 64 64) }] }

theorem profile34_node245 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,5] 6 96 profile34_node245_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,5] 6 96 profile34_node245_cert).mp (by decide +kernel))

def profile34_node246_cert : Bound 7 := { allowed := (rows 64 32 112 64 0 0 0), upper := (rows 49 82 14 41 84 100 64), lower := (rows 49 82 14 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 36 127), good := (rows 105 66 110 105 64 96 64) }] }

theorem profile34_node246 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,33] 6 68 profile34_node246_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,33] 6 68 profile34_node246_cert).mp (by decide +kernel))

def profile34_node247_cert : Bound 7 := { allowed := (rows 64 0 112 80 0 0 0), upper := (rows 49 82 14 44 81 97 64), lower := (rows 49 82 14 44 16 32 64), losses := [{ target := 5, region := (rows 1 19 4 8 17 0 127), good := (rows 83 82 78 76 82 64 64) }] }

theorem profile34_node247 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,36] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,36] 6 65 profile34_node247_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,36] 6 65 profile34_node247_cert).mp (by decide +kernel))

def profile34_node248_cert : Bound 7 := { allowed := (rows 64 32 112 32 0 0 0), upper := (rows 49 82 14 73 52 36 64), lower := (rows 49 82 14 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 36 127), good := (rows 105 66 110 73 64 96 64) }] }

theorem profile34_node248 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,65] 6 36 profile34_node248_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,65] 6 36 profile34_node248_cert).mp (by decide +kernel))

def profile34_node249_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 82 14 76 49 33 64), lower := (rows 49 82 14 76 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 14 0 33 127), good := (rows 97 78 78 76 64 96 64) }] }

theorem profile34_node249 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,68] 6 33 profile34_node249_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,68] 6 33 profile34_node249_cert).mp (by decide +kernel))

def profile34_node250_cert : Bound 7 := { allowed := (rows 64 32 112 16 0 0 0), upper := (rows 49 82 14 104 21 37 64), lower := (rows 49 82 14 104 16 32 64), losses := [] }

theorem profile34_node250 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,96] 6 5 profile34_node250_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10,96] 6 5 profile34_node250_cert).mp (by decide +kernel))

def profile34_node244_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node244_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node244 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,10] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile34_node244_route profile34_node244_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node245
  · exact profile34_node246
  · exact profile34_node247
  · exact profile34_node248
  · exact profile34_node249
  · exact profile34_node250

def profile34_node251_cert : Bound 7 := { allowed := (rows 64 32 64 112 0 0 0), upper := (rows 49 82 37 78 94 110 64), lower := (rows 49 82 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 66 101 72 64 96 64) }] }

theorem profile34_node251 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,33] 6 78 profile34_node251_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,33] 6 78 profile34_node251_cert).mp (by decide +kernel))

def profile34_node252_cert : Bound 7 := { allowed := (rows 64 0 80 112 0 0 0), upper := (rows 49 82 38 77 93 109 64), lower := (rows 49 82 38 8 16 32 64), losses := [{ target := 5, region := (rows 1 19 4 8 16 0 127), good := (rows 83 82 70 72 82 64 64) }] }

theorem profile34_node252 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,34] 6 77 profile34_node252_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,34] 6 77 profile34_node252_cert).mp (by decide +kernel))

def profile34_node253_cert : Bound 7 := { allowed := (rows 64 0 80 112 0 0 0), upper := (rows 49 82 44 79 87 103 64), lower := (rows 49 82 44 8 16 32 64), losses := [{ target := 5, region := (rows 1 19 4 8 16 0 127), good := (rows 83 82 76 72 82 64 64) }] }

theorem profile34_node253 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,40] 6 71 profile34_node253_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,40] 6 71 profile34_node253_cert).mp (by decide +kernel))

def profile34_node254_cert : Bound 7 := { allowed := (rows 64 32 32 112 0 0 0), upper := (rows 49 82 69 46 62 46 64), lower := (rows 49 82 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 66 69 72 64 96 64) }] }

theorem profile34_node254 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,65] 6 46 profile34_node254_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,65] 6 46 profile34_node254_cert).mp (by decide +kernel))

def profile34_node255_cert : Bound 7 := { allowed := (rows 64 32 32 112 0 0 0), upper := (rows 49 82 70 45 61 45 64), lower := (rows 49 82 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 97 70 70 72 64 96 64) }] }

theorem profile34_node255 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,66] 6 45 profile34_node255_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,66] 6 45 profile34_node255_cert).mp (by decide +kernel))

def profile34_node256_cert : Bound 7 := { allowed := (rows 64 32 32 112 0 0 0), upper := (rows 49 82 76 47 55 39 64), lower := (rows 49 82 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 97 66 76 76 64 96 64) }] }

theorem profile34_node256 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,72] 6 39 profile34_node256_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,72] 6 39 profile34_node256_cert).mp (by decide +kernel))

def profile34_node257_cert : Bound 7 := { allowed := (rows 64 32 16 112 0 0 0), upper := (rows 49 82 100 15 31 47 64), lower := (rows 49 82 100 8 16 32 64), losses := [] }

theorem profile34_node257 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,96] 6 15 profile34_node257_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80,96] 6 15 profile34_node257_cert).mp (by decide +kernel))

def profile34_node235_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node235_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node235 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48,80] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile34_node235_route profile34_node235_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node236
  · exact profile34_node237
  · exact profile34_node244
  · exact profile34_node251
  · exact profile34_node252
  · exact profile34_node253
  · exact profile34_node254
  · exact profile34_node255
  · exact profile34_node256
  · exact profile34_node257


#print axioms profile34_node235
end Delivery.SmallBudgetTenFinite7
