import SmallBudgetTenFinite7Profile025Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile25_node131_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 21 67 21 106 114 98 64), lower := (rows 21 67 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 84 122 84 72 80 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 69 85 72 85 96 64) }] }

theorem profile25_node131 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,17] 6 98 profile25_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,17] 6 98 profile25_node131_cert).mp (by decide +kernel))

def profile25_node132_cert : CutBound 7 := { lost := (rows 2 16 0 16 0 0 0), upper := (rows 21 67 22 107 115 99 64), lower := (rows 21 67 22 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 32 127), good := (rows 85 65 85 72 80 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 111 107 110 72 64 96 64) }] }

theorem profile25_node132 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,18] 6 99 profile25_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,18] 6 99 profile25_node132_cert).mp (by decide +kernel))

def profile25_node133_cert : CutBound 7 := { lost := (rows 0 16 0 1 0 0 0), upper := (rows 21 67 37 90 82 114 64), lower := (rows 21 67 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 84 122 100 72 80 96 64) },{ target := 4, region := (rows 1 7 4 8 0 32 127), good := (rows 71 67 103 72 64 96 64) }] }

theorem profile25_node133 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,33] 6 82 profile25_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,33] 6 82 profile25_node133_cert).mp (by decide +kernel))

def profile25_node135_cert : CutBound 7 := { lost := (rows 2 0 1 0 0 0 0), upper := (rows 21 67 38 11 80 112 64), lower := (rows 21 67 38 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 8 127 127 127), good := (rows 116 118 118 126 112 112 112) },{ target := 1, region := (rows 5 0 4 8 127 127 127), good := (rows 117 113 117 121 112 112 112) }] }

theorem profile25_node135 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,3] 6 80 profile25_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,3] 6 80 profile25_node135_cert).mp (by decide +kernel))

def profile25_node136_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 21 67 38 25 82 98 64), lower := (rows 21 67 38 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 116 118 118 88 80 96 64) },{ target := 1, region := (rows 1 0 4 9 16 32 127), good := (rows 93 73 100 89 80 96 64) }] }

theorem profile25_node136 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,17] 6 66 profile25_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,17] 6 66 profile25_node136_cert).mp (by decide +kernel))

def profile25_node137_cert : CutBound 7 := { lost := (rows 2 16 16 0 0 0 0), upper := (rows 21 67 38 26 81 97 64), lower := (rows 21 67 38 26 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 23 39 127), good := (rows 117 113 117 120 80 96 64) },{ target := 4, region := (rows 1 3 15 8 0 35 127), good := (rows 103 103 102 110 64 96 64) }] }

theorem profile25_node137 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,18] 6 65 profile25_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,18] 6 65 profile25_node137_cert).mp (by decide +kernel))

def profile25_node138_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 21 67 38 73 18 50 64), lower := (rows 21 67 38 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 116 118 118 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 16 32 127), good := (rows 93 73 108 73 80 96 64) }] }

theorem profile25_node138 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,65] 6 18 profile25_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,65] 6 18 profile25_node138_cert).mp (by decide +kernel))

def profile25_node139_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 21 67 38 74 17 49 64), lower := (rows 21 67 38 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 92 74 110 74 80 96 64) },{ target := 1, region := (rows 5 0 4 8 23 39 127), good := (rows 117 113 117 120 80 96 64) }] }

theorem profile25_node139 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,66] 6 17 profile25_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,66] 6 17 profile25_node139_cert).mp (by decide +kernel))

def profile25_node140_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 21 67 38 88 19 35 64), lower := (rows 21 67 38 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 92 74 102 88 88 96 64) },{ target := 1, region := (rows 1 0 4 25 16 32 127), good := (rows 93 73 100 88 88 96 64) }] }

theorem profile25_node140 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,80] 6 3 profile25_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34,80] 6 3 profile25_node140_cert).mp (by decide +kernel))

def profile25_node134_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node134_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node134 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,34] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node134_route profile25_node134_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node135
  · exact profile25_node136
  · exact profile25_node137
  · exact profile25_node138
  · exact profile25_node139
  · exact profile25_node140

def profile25_node141_cert : CutBound 7 := { lost := (rows 2 16 0 16 0 0 0), upper := (rows 21 67 52 75 83 99 64), lower := (rows 21 67 52 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 32 127), good := (rows 85 65 117 72 80 96 64) },{ target := 4, region := (rows 1 3 4 11 0 35 127), good := (rows 111 107 100 72 64 96 64) }] }

theorem profile25_node141 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,48] 6 67 profile25_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,48] 6 67 profile25_node141_cert).mp (by decide +kernel))

def profile25_node142_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 21 67 69 58 50 50 64), lower := (rows 21 67 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 84 122 68 72 80 96 64) },{ target := 1, region := (rows 17 0 23 8 16 32 127), good := (rows 85 69 69 72 85 96 64) }] }

theorem profile25_node142 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,65] 6 50 profile25_node142_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,65] 6 50 profile25_node142_cert).mp (by decide +kernel))

def profile25_node143_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 21 67 70 59 51 51 64), lower := (rows 21 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 84 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 71 71 70 72 64 96 64) }] }

theorem profile25_node143 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,66] 6 51 profile25_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,66] 6 51 profile25_node143_cert).mp (by decide +kernel))

def profile25_node144_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 21 67 84 43 51 35 64), lower := (rows 21 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 70 84 72 84 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 69 85 72 85 96 64) }] }

theorem profile25_node144 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,80] 6 35 profile25_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,80] 6 35 profile25_node144_cert).mp (by decide +kernel))

def profile25_node145_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 21 67 100 27 19 51 64), lower := (rows 21 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 84 66 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 85 65 100 72 80 100 64) }] }

theorem profile25_node145 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,96] 6 19 profile25_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65,96] 6 19 profile25_node145_cert).mp (by decide +kernel))

def profile25_node129_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node129_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node129 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,65] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node129_route profile25_node129_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node130
  · exact profile25_node131
  · exact profile25_node132
  · exact profile25_node133
  · exact profile25_node134
  · exact profile25_node141
  · exact profile25_node142
  · exact profile25_node143
  · exact profile25_node144
  · exact profile25_node145

def profile25_node147_cert : CutBound 7 := { lost := (rows 0 1 0 16 0 0 0), upper := (rows 21 82 7 107 115 99 64), lower := (rows 21 82 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 86 82 70 72 82 96 64) },{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 109 66 111 72 64 96 64) }] }

theorem profile25_node147 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,3] 6 99 profile25_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,3] 6 99 profile25_node147_cert).mp (by decide +kernel))

def profile25_node149_cert : CutBound 7 := { lost := (rows 0 1 16 0 0 0 0), upper := (rows 21 82 37 11 82 98 64), lower := (rows 21 82 37 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 4, region := (rows 1 2 12 8 0 42 127), good := (rows 69 98 101 111 64 96 64) }] }

theorem profile25_node149 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,3] 6 66 profile25_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,3] 6 66 profile25_node149_cert).mp (by decide +kernel))

def profile25_node150_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 21 82 37 73 18 34 64), lower := (rows 21 82 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 1 0 4 13 16 32 127), good := (rows 93 80 109 73 80 96 64) }] }

theorem profile25_node150 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,65] 6 2 profile25_node150_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,65] 6 2 profile25_node150_cert).mp (by decide +kernel))

def profile25_node151_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 21 82 37 74 19 35 64), lower := (rows 21 82 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 31 16 32 127), good := (rows 94 90 110 74 90 96 64) }] }

theorem profile25_node151 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,66] 6 3 profile25_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33,66] 6 3 profile25_node151_cert).mp (by decide +kernel))

def profile25_node148_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node148_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node148 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,33] 6 (by decide) (choices 2) [3,65,66] profile25_node148_route profile25_node148_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node149
  · exact profile25_node150
  · exact profile25_node151

def profile25_node153_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 21 82 38 11 81 97 64), lower := (rows 21 82 38 11 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 86 82 102 74 82 96 64) },{ target := 1, region := (rows 5 0 4 8 29 45 127), good := (rows 117 80 117 121 80 96 64) }] }

theorem profile25_node153 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,3] 6 65 profile25_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,3] 6 65 profile25_node153_cert).mp (by decide +kernel))

def profile25_node154_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 21 82 38 73 19 35 64), lower := (rows 21 82 38 73 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 86 82 102 74 82 96 64) },{ target := 1, region := (rows 1 0 4 9 16 32 127), good := (rows 93 80 100 73 80 96 64) }] }

theorem profile25_node154 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,65] 6 3 profile25_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,65] 6 3 profile25_node154_cert).mp (by decide +kernel))

def profile25_node155_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 21 82 38 74 17 33 64), lower := (rows 21 82 38 74 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 31 16 32 127), good := (rows 94 90 110 74 90 96 64) }] }

theorem profile25_node155 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,66] 6 1 profile25_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34,66] 6 1 profile25_node155_cert).mp (by decide +kernel))

def profile25_node152_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node152_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node152 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,34] 6 (by decide) (choices 2) [3,65,66] profile25_node152_route profile25_node152_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node153
  · exact profile25_node154
  · exact profile25_node155

def profile25_node156_cert : CutBound 7 := { lost := (rows 2 1 2 0 0 0 0), upper := (rows 21 82 69 43 51 35 64), lower := (rows 21 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 86 82 70 72 82 96 64) },{ target := 1, region := (rows 19 0 23 8 16 32 127), good := (rows 85 85 69 72 85 96 64) }] }

theorem profile25_node156 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,65] 6 35 profile25_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,65] 6 35 profile25_node156_cert).mp (by decide +kernel))

def profile25_node157_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 21 82 70 43 51 35 64), lower := (rows 21 82 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 86 86 70 72 86 96 64) }] }

theorem profile25_node157 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,66] 6 35 profile25_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,66] 6 35 profile25_node157_cert).mp (by decide +kernel))

def profile25_node158_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 21 82 100 11 19 35 64), lower := (rows 21 82 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 36 8 16 32 127), good := (rows 86 82 100 72 82 100 64) }] }

theorem profile25_node158 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,96] 6 3 profile25_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80,96] 6 3 profile25_node158_cert).mp (by decide +kernel))

def profile25_node146_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile25_node146_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node146 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,80] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile25_node146_route profile25_node146_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node147
  · exact profile25_node148
  · exact profile25_node152
  · exact profile25_node156
  · exact profile25_node157
  · exact profile25_node158

def profile25_node159_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 21 98 87 91 83 115 64), lower := (rows 21 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 84 98 68 72 80 98 64) },{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 69 98 68 72 64 98 64) }] }

theorem profile25_node159 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,96] 6 83 profile25_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20,96] 6 83 profile25_node159_cert).mp (by decide +kernel))

def profile25_node116_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node116_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node116 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [20] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile25_node116_route profile25_node116_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node117
  · exact profile25_node118
  · exact profile25_node125
  · exact profile25_node129
  · exact profile25_node146
  · exact profile25_node159

def profile25_node162_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 35 7 7 88 80 112 64), lower := (rows 35 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 122 126 126 120 120 120 120) },{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 125 125 120 120 120 120) }] }

theorem profile25_node162 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,3] 6 80 profile25_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,3] 6 80 profile25_node162_cert).mp (by decide +kernel))

def profile25_node163_cert : CutBound 7 := { lost := (rows 0 16 0 1 0 0 0), upper := (rows 35 7 21 90 82 114 64), lower := (rows 35 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 126 124 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 99 71 71 72 64 96 64) }] }

theorem profile25_node163 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,17] 6 82 profile25_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,17] 6 82 profile25_node163_cert).mp (by decide +kernel))

def profile25_node165_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 35 7 22 25 80 96 64), lower := (rows 35 7 22 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 127 127 127), good := (rows 118 118 118 124 112 112 112) },{ target := 1, region := (rows 1 0 4 11 127 127 127), good := (rows 121 125 124 121 112 112 112) }] }

theorem profile25_node165 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,17] 6 64 profile25_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,17] 6 64 profile25_node165_cert).mp (by decide +kernel))

def profile25_node166_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 35 7 22 73 80 112 64), lower := (rows 35 7 22 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 127 127 127), good := (rows 118 118 118 124 112 112 112) },{ target := 1, region := (rows 1 0 4 11 127 127 127), good := (rows 121 125 124 121 112 112 112) }] }

theorem profile25_node166 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,65] 6 80 profile25_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,65] 6 80 profile25_node166_cert).mp (by decide +kernel))

def profile25_node167_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 35 7 22 88 81 97 64), lower := (rows 35 7 22 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 28 16 32 127), good := (rows 98 78 94 88 88 96 64) },{ target := 1, region := (rows 1 0 4 31 19 35 127), good := (rows 121 125 124 88 88 96 64) }] }

theorem profile25_node167 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,80] 6 65 profile25_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18,80] 6 65 profile25_node167_cert).mp (by decide +kernel))

def profile25_node164_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node164_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node164 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,18] 6 (by decide) (choices 2) [17,65,80] profile25_node164_route profile25_node164_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node165
  · exact profile25_node166
  · exact profile25_node167

def profile25_node168_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 35 7 69 90 82 114 64), lower := (rows 35 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 19 35 127), good := (rows 122 126 124 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 101 69 69 72 80 96 64) }] }

theorem profile25_node168 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,65] 6 82 profile25_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,65] 6 82 profile25_node168_cert).mp (by decide +kernel))

def profile25_node169_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 35 7 70 89 81 113 64), lower := (rows 35 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 102 70 70 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 19 35 127), good := (rows 121 125 124 72 80 96 64) }] }

theorem profile25_node169 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,66] 6 81 profile25_node169_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,66] 6 81 profile25_node169_cert).mp (by decide +kernel))

def profile25_node170_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 35 7 84 91 83 115 64), lower := (rows 35 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 98 70 84 72 84 96 64) },{ target := 1, region := (rows 1 0 20 8 16 32 127), good := (rows 97 69 84 72 84 96 64) }] }

theorem profile25_node170 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,80] 6 83 profile25_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5,80] 6 83 profile25_node170_cert).mp (by decide +kernel))

def profile25_node161_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node161_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node161 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,5] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node161_route profile25_node161_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node162
  · exact profile25_node163
  · exact profile25_node164
  · exact profile25_node168
  · exact profile25_node169
  · exact profile25_node170

def profile25_node172_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 35 19 7 92 84 116 64), lower := (rows 35 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 98 82 126 72 80 96 64) },{ target := 1, region := (rows 1 0 4 12 20 36 127), good := (rows 97 81 125 72 80 96 64) }] }

theorem profile25_node172 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,3] 6 84 profile25_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,3] 6 84 profile25_node172_cert).mp (by decide +kernel))

def profile25_node173_cert : CutBound 7 := { lost := (rows 0 64 66 0 0 0 0), upper := (rows 35 19 21 78 86 102 64), lower := (rows 35 19 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 101 85 85 72 80 96 64) },{ target := 6, region := (rows 1 6 6 8 16 32 0), good := (rows 39 23 23 8 16 32 0) }] }

theorem profile25_node173 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,17] 6 70 profile25_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,17] 6 70 profile25_node173_cert).mp (by decide +kernel))

def profile25_node174_cert : CutBound 7 := { lost := (rows 16 0 1 16 0 0 0), upper := (rows 35 19 22 77 85 101 64), lower := (rows 35 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 102 86 86 72 80 96 64) },{ target := 4, region := (rows 5 2 4 12 0 36 127), good := (rows 99 67 111 72 64 96 64) }] }

theorem profile25_node174 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,18] 6 69 profile25_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,18] 6 69 profile25_node174_cert).mp (by decide +kernel))

def profile25_node175_cert : CutBound 7 := { lost := (rows 0 0 18 0 0 0 0), upper := (rows 35 19 69 94 86 118 64), lower := (rows 35 19 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 101 85 69 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 103 71 69 72 64 96 64) }] }

theorem profile25_node175 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,65] 6 86 profile25_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,65] 6 86 profile25_node175_cert).mp (by decide +kernel))

def profile25_node176_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 35 19 70 93 85 117 64), lower := (rows 35 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 102 86 70 72 80 96 64) },{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) }] }

theorem profile25_node176 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,66] 6 85 profile25_node176_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,66] 6 85 profile25_node176_cert).mp (by decide +kernel))

def profile25_node177_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 35 19 84 79 87 103 64), lower := (rows 35 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 102 86 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 101 85 84 72 84 96 64) }] }

theorem profile25_node177 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,80] 6 71 profile25_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17,80] 6 71 profile25_node177_cert).mp (by decide +kernel))

def profile25_node171_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node171_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node171 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,17] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node171_route profile25_node171_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node172
  · exact profile25_node173
  · exact profile25_node174
  · exact profile25_node175
  · exact profile25_node176
  · exact profile25_node177

def profile25_node179_cert : CutBound 7 := { lost := (rows 0 0 16 2 0 0 0), upper := (rows 35 22 7 89 81 113 64), lower := (rows 35 22 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 121 124 125 72 80 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 103 70 71 72 64 96 64) }] }

theorem profile25_node179 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,3] 6 81 profile25_node179_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,3] 6 81 profile25_node179_cert).mp (by decide +kernel))

def profile25_node180_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 35 22 21 75 83 99 64), lower := (rows 35 22 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 98 86 86 72 80 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 111 109 72 64 96 64) }] }

theorem profile25_node180 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,17] 6 67 profile25_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,17] 6 67 profile25_node180_cert).mp (by decide +kernel))

def profile25_node181_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 22 22 73 81 97 64), lower := (rows 35 22 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 102 86 86 72 86 96 64) }] }

theorem profile25_node181 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,18] 6 65 profile25_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,18] 6 65 profile25_node181_cert).mp (by decide +kernel))

def profile25_node182_cert : CutBound 7 := { lost := (rows 0 0 18 0 0 0 0), upper := (rows 35 22 69 91 83 115 64), lower := (rows 35 22 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 101 84 69 72 80 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 103 70 69 72 64 96 64) }] }

theorem profile25_node182 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,65] 6 83 profile25_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,65] 6 83 profile25_node182_cert).mp (by decide +kernel))

def profile25_node183_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 22 70 89 81 113 64), lower := (rows 35 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 23 8 16 32 127), good := (rows 102 86 70 72 86 96 64) }] }

theorem profile25_node183 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,66] 6 81 profile25_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,66] 6 81 profile25_node183_cert).mp (by decide +kernel))

def profile25_node184_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 22 84 75 83 99 64), lower := (rows 35 22 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 102 86 86 72 86 96 64) }] }

theorem profile25_node184 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,80] 6 67 profile25_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20,80] 6 67 profile25_node184_cert).mp (by decide +kernel))

def profile25_node178_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node178_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node178 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,20] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node178_route profile25_node178_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node179
  · exact profile25_node180
  · exact profile25_node181
  · exact profile25_node182
  · exact profile25_node183
  · exact profile25_node184

def profile25_node185_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 35 67 87 95 87 119 64), lower := (rows 35 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 127), good := (rows 99 67 68 72 64 99 64) }] }

theorem profile25_node185 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,65] 6 87 profile25_node185_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,65] 6 87 profile25_node185_cert).mp (by decide +kernel))

def profile25_node186_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 35 70 87 91 83 115 64), lower := (rows 35 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 98 70 70 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 99 70 70 72 64 96 64) }] }

theorem profile25_node186 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,68] 6 83 profile25_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,68] 6 83 profile25_node186_cert).mp (by decide +kernel))

def profile25_node188_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 35 82 7 93 85 117 64), lower := (rows 35 82 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 98 82 70 72 82 96 64) },{ target := 1, region := (rows 1 0 4 12 20 36 127), good := (rows 97 80 125 72 80 96 64) }] }

theorem profile25_node188 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,3] 6 85 profile25_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,3] 6 85 profile25_node188_cert).mp (by decide +kernel))

def profile25_node190_cert : Bound 7 := { allowed := (rows 80 0 66 80 0 0 0), upper := (rows 35 82 21 11 84 100 64), lower := (rows 35 82 21 11 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 8 20 36 127), good := (rows 98 82 118 74 82 96 64) }] }

theorem profile25_node190 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,3] 6 68 profile25_node190_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,3] 6 68 profile25_node190_cert).mp (by decide +kernel))

def profile25_node191_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 35 82 21 13 82 98 64), lower := (rows 35 82 21 13 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 126 114 114 114) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 97 80 93 77 80 96 64) }] }

theorem profile25_node191 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,5] 6 66 profile25_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,5] 6 66 profile25_node191_cert).mp (by decide +kernel))

def profile25_node192_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 35 82 21 14 81 97 64), lower := (rows 35 82 21 14 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 12 16 32 127), good := (rows 98 82 94 78 82 96 64) }] }

theorem profile25_node192 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,6] 6 65 profile25_node192_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,6] 6 65 profile25_node192_cert).mp (by decide +kernel))

def profile25_node193_cert : Bound 7 := { allowed := (rows 80 0 66 18 0 0 0), upper := (rows 35 82 21 73 22 38 64), lower := (rows 35 82 21 73 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 8 20 36 127), good := (rows 98 82 118 72 82 96 64) }] }

theorem profile25_node193 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,65] 6 6 profile25_node193_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,65] 6 6 profile25_node193_cert).mp (by decide +kernel))

def profile25_node194_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 35 82 21 74 21 37 64), lower := (rows 35 82 21 74 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 31 16 32 127), good := (rows 106 90 94 74 90 96 64) }] }

theorem profile25_node194 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,66] 6 5 profile25_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,66] 6 5 profile25_node194_cert).mp (by decide +kernel))

def profile25_node195_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 35 82 21 76 19 35 64), lower := (rows 35 82 21 76 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 12 16 32 127), good := (rows 98 82 94 78 82 96 64) }] }

theorem profile25_node195 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,68] 6 3 profile25_node195_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17,68] 6 3 profile25_node195_cert).mp (by decide +kernel))

def profile25_node189_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node189_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node189 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,17] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile25_node189_route profile25_node189_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node190
  · exact profile25_node191
  · exact profile25_node192
  · exact profile25_node193
  · exact profile25_node194
  · exact profile25_node195

def profile25_node196_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 82 22 77 85 101 64), lower := (rows 35 82 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 102 86 86 72 86 96 64) }] }

theorem profile25_node196 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,18] 6 69 profile25_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,18] 6 69 profile25_node196_cert).mp (by decide +kernel))

def profile25_node197_cert : CutBound 7 := { lost := (rows 0 1 2 0 0 0 0), upper := (rows 35 82 69 31 23 55 64), lower := (rows 35 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 98 82 68 72 82 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 101 80 69 72 80 96 64) }] }

theorem profile25_node197 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,65] 6 23 profile25_node197_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,65] 6 23 profile25_node197_cert).mp (by decide +kernel))

def profile25_node198_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 82 70 29 21 53 64), lower := (rows 35 82 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 23 8 16 32 127), good := (rows 102 86 70 72 86 96 64) }] }

theorem profile25_node198 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,66] 6 21 profile25_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,66] 6 21 profile25_node198_cert).mp (by decide +kernel))

def profile25_node199_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 35 82 84 15 23 39 64), lower := (rows 35 82 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 102 86 86 72 86 96 64) }] }

theorem profile25_node199 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,80] 6 7 profile25_node199_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80,80] 6 7 profile25_node199_cert).mp (by decide +kernel))

def profile25_node187_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node187_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node187 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34,80] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node187_route profile25_node187_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node188
  · exact profile25_node189
  · exact profile25_node196
  · exact profile25_node197
  · exact profile25_node198
  · exact profile25_node199

def profile25_node160_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 12 => 3 | 36 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node160_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node160 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [34] 6 (by decide) (choices 2) [5,17,20,65,68,80] profile25_node160_route profile25_node160_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node161
  · exact profile25_node171
  · exact profile25_node178
  · exact profile25_node185
  · exact profile25_node186
  · exact profile25_node187

def profile25_node202_cert : CutBound 7 := { lost := (rows 0 0 16 1 0 0 0), upper := (rows 37 19 7 90 82 114 64), lower := (rows 37 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 124 122 126 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 101 71 71 72 64 96 64) }] }

theorem profile25_node202 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,3] 6 82 profile25_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,3] 6 82 profile25_node202_cert).mp (by decide +kernel))

def profile25_node203_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 37 19 21 74 82 98 64), lower := (rows 37 19 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 100 122 84 72 80 96 64) },{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 101 85 85 72 80 96 64) }] }

theorem profile25_node203 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,17] 6 66 profile25_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,17] 6 66 profile25_node203_cert).mp (by decide +kernel))

def profile25_node204_cert : CutBound 7 := { lost := (rows 16 0 1 16 0 0 0), upper := (rows 37 19 22 75 83 99 64), lower := (rows 37 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 100 86 86 72 80 96 64) },{ target := 4, region := (rows 5 2 4 14 0 38 127), good := (rows 109 107 111 72 64 96 64) }] }

theorem profile25_node204 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,18] 6 67 profile25_node204_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,18] 6 67 profile25_node204_cert).mp (by decide +kernel))

def profile25_node205_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 37 19 69 90 82 114 64), lower := (rows 37 19 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 100 122 68 72 80 96 64) },{ target := 1, region := (rows 33 0 39 8 16 32 127), good := (rows 101 85 69 72 80 101 64) }] }

theorem profile25_node205 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,65] 6 82 profile25_node205_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,65] 6 82 profile25_node205_cert).mp (by decide +kernel))

def profile25_node206_cert : CutBound 7 := { lost := (rows 0 0 17 0 0 0 0), upper := (rows 37 19 70 91 83 115 64), lower := (rows 37 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 100 86 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 101 71 70 72 64 96 64) }] }

theorem profile25_node206 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,66] 6 83 profile25_node206_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,66] 6 83 profile25_node206_cert).mp (by decide +kernel))

def profile25_node207_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 37 19 84 75 83 99 64), lower := (rows 37 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 100 86 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 101 85 84 72 84 96 64) }] }

theorem profile25_node207 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,80] 6 67 profile25_node207_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17,80] 6 67 profile25_node207_cert).mp (by decide +kernel))

def profile25_node201_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node201_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node201 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,17] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node201_route profile25_node201_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node202
  · exact profile25_node203
  · exact profile25_node204
  · exact profile25_node205
  · exact profile25_node206
  · exact profile25_node207

def profile25_node209_cert : CutBound 7 := { lost := (rows 16 16 16 1 0 0 0), upper := (rows 37 67 7 90 82 114 64), lower := (rows 37 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 124 122 126 72 80 96 64) },{ target := 4, region := (rows 33 39 39 8 0 32 127), good := (rows 103 71 71 72 64 103 64) }] }

theorem profile25_node209 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,3] 6 82 profile25_node209_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,3] 6 82 profile25_node209_cert).mp (by decide +kernel))

def profile25_node210_cert : CutBound 7 := { lost := (rows 0 16 0 1 0 0 0), upper := (rows 37 67 21 90 82 114 64), lower := (rows 37 67 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 100 122 84 72 80 96 64) },{ target := 4, region := (rows 1 7 4 8 0 32 127), good := (rows 103 67 71 72 64 96 64) }] }

theorem profile25_node210 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,17] 6 82 profile25_node210_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,17] 6 82 profile25_node210_cert).mp (by decide +kernel))

def profile25_node212_cert : CutBound 7 := { lost := (rows 2 0 1 0 0 0 0), upper := (rows 37 67 22 11 80 112 64), lower := (rows 37 67 22 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 8 127 127 127), good := (rows 116 118 118 126 112 112 112) },{ target := 1, region := (rows 5 0 4 8 127 127 127), good := (rows 117 113 117 121 112 112 112) }] }

theorem profile25_node212 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,3] 6 80 profile25_node212_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,3] 6 80 profile25_node212_cert).mp (by decide +kernel))

def profile25_node213_cert : CutBound 7 := { lost := (rows 16 16 1 0 0 0 0), upper := (rows 37 67 22 25 82 98 64), lower := (rows 37 67 22 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 116 118 118 88 80 96 64) },{ target := 4, region := (rows 5 15 4 8 0 47 127), good := (rows 103 99 103 107 64 96 64) }] }

theorem profile25_node213 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,17] 6 66 profile25_node213_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,17] 6 66 profile25_node213_cert).mp (by decide +kernel))

def profile25_node214_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 37 67 22 26 81 97 64), lower := (rows 37 67 22 26 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 12 16 32 127), good := (rows 108 66 94 94 80 96 64) }] }

theorem profile25_node214 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,18] 6 65 profile25_node214_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,18] 6 65 profile25_node214_cert).mp (by decide +kernel))

def profile25_node215_cert : CutBound 7 := { lost := (rows 0 0 1 2 0 0 0), upper := (rows 37 67 22 73 18 50 64), lower := (rows 37 67 22 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 116 118 118 72 80 96 64) },{ target := 1, region := (rows 1 0 4 11 16 32 127), good := (rows 109 73 92 73 80 96 64) }] }

theorem profile25_node215 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,65] 6 18 profile25_node215_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,65] 6 18 profile25_node215_cert).mp (by decide +kernel))

def profile25_node216_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 37 67 22 74 17 49 64), lower := (rows 37 67 22 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 108 74 94 74 80 96 64) },{ target := 1, region := (rows 5 0 4 8 23 39 127), good := (rows 117 113 117 120 80 96 64) }] }

theorem profile25_node216 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,66] 6 17 profile25_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,66] 6 17 profile25_node216_cert).mp (by decide +kernel))

def profile25_node217_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 37 67 22 88 19 35 64), lower := (rows 37 67 22 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 28 16 32 127), good := (rows 108 66 94 88 88 96 64) },{ target := 1, region := (rows 1 0 4 28 16 32 127), good := (rows 109 65 92 88 88 96 64) }] }

theorem profile25_node217 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,80] 6 3 profile25_node217_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18,80] 6 3 profile25_node217_cert).mp (by decide +kernel))

def profile25_node211_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node211_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node211 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,18] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node211_route profile25_node211_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node212
  · exact profile25_node213
  · exact profile25_node214
  · exact profile25_node215
  · exact profile25_node216
  · exact profile25_node217

def profile25_node218_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 37 67 69 26 18 50 64), lower := (rows 37 67 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 100 122 68 72 80 96 64) },{ target := 1, region := (rows 33 0 39 8 16 32 127), good := (rows 101 69 69 72 80 101 64) }] }

theorem profile25_node218 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,65] 6 18 profile25_node218_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,65] 6 18 profile25_node218_cert).mp (by decide +kernel))

def profile25_node219_cert : CutBound 7 := { lost := (rows 16 16 17 0 0 0 0), upper := (rows 37 67 70 27 19 51 64), lower := (rows 37 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 100 70 70 72 80 96 64) },{ target := 4, region := (rows 33 35 39 8 0 32 127), good := (rows 103 71 70 72 64 103 64) }] }

theorem profile25_node219 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,66] 6 19 profile25_node219_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,66] 6 19 profile25_node219_cert).mp (by decide +kernel))

def profile25_node220_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 37 67 84 27 19 51 64), lower := (rows 37 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 100 66 84 72 84 96 64) },{ target := 1, region := (rows 1 0 20 8 16 32 127), good := (rows 101 65 84 72 84 96 64) }] }

theorem profile25_node220 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,80] 6 19 profile25_node220_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65,80] 6 19 profile25_node220_cert).mp (by decide +kernel))

def profile25_node208_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node208_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node208 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,65] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node208_route profile25_node208_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node209
  · exact profile25_node210
  · exact profile25_node211
  · exact profile25_node218
  · exact profile25_node219
  · exact profile25_node220

def profile25_node223_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 37 82 7 11 80 112 64), lower := (rows 37 82 7 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 5 0 4 8 127 127 127), good := (rows 117 112 117 121 112 112 112) }] }

theorem profile25_node223 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,3] 6 80 profile25_node223_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,3] 6 80 profile25_node223_cert).mp (by decide +kernel))

def profile25_node224_cert : CutBound 7 := { lost := (rows 16 1 16 0 0 0 0), upper := (rows 37 82 7 25 82 98 64), lower := (rows 37 82 7 25 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 4, region := (rows 7 2 6 8 0 38 127), good := (rows 101 103 103 73 64 96 64) }] }

theorem profile25_node224 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,17] 6 66 profile25_node224_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,17] 6 66 profile25_node224_cert).mp (by decide +kernel))

def profile25_node225_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 37 82 7 26 81 97 64), lower := (rows 37 82 7 26 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 127), good := (rows 100 90 78 90 90 96 64) }] }

theorem profile25_node225 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,18] 6 65 profile25_node225_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,18] 6 65 profile25_node225_cert).mp (by decide +kernel))

def profile25_node226_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 37 82 7 73 18 50 64), lower := (rows 37 82 7 73 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 1 0 4 13 16 32 127), good := (rows 109 80 77 73 80 96 64) }] }

theorem profile25_node226 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,65] 6 18 profile25_node226_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,65] 6 18 profile25_node226_cert).mp (by decide +kernel))

def profile25_node227_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 37 82 7 74 17 49 64), lower := (rows 37 82 7 74 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 30 16 32 127), good := (rows 108 90 78 74 90 96 64) }] }

theorem profile25_node227 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,66] 6 17 profile25_node227_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,66] 6 17 profile25_node227_cert).mp (by decide +kernel))

def profile25_node228_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 37 82 7 88 19 35 64), lower := (rows 37 82 7 88 16 32 64), losses := [{ target := 0, region := (rows 0 26 4 26 16 32 127), good := (rows 100 90 78 90 90 96 64) }] }

theorem profile25_node228 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,80] 6 3 profile25_node228_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3,80] 6 3 profile25_node228_cert).mp (by decide +kernel))

def profile25_node222_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node222_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node222 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,3] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node222_route profile25_node222_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node223
  · exact profile25_node224
  · exact profile25_node225
  · exact profile25_node226
  · exact profile25_node227
  · exact profile25_node228

def profile25_node231_cert : CutBound 7 := { lost := (rows 2 1 2 0 0 0 0), upper := (rows 37 82 21 11 18 96 64), lower := (rows 37 82 21 11 18 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 31 0 22 8 16 127 127), good := (rows 101 117 117 109 117 96 96) }] }

theorem profile25_node231 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3,2] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3,2] 6 64 profile25_node231_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3,2] 6 64 profile25_node231_cert).mp (by decide +kernel))

def profile25_node232_cert : CutBound 7 := { lost := (rows 2 1 2 0 0 0 0), upper := (rows 37 82 21 11 80 34 64), lower := (rows 37 82 21 11 80 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 33 0 45 8 127 32 127), good := (rows 117 80 85 93 80 117 80) }] }

theorem profile25_node232 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3,64] 6 2 profile25_node232_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3,64] 6 2 profile25_node232_cert).mp (by decide +kernel))

def profile25_node230_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile25_node230_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node230 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,3] 6 (by decide) (choices 1) [2,64] profile25_node230_route profile25_node230_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile25_node231
  · exact profile25_node232

def profile25_node233_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 37 82 21 73 18 34 64), lower := (rows 37 82 21 73 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) },{ target := 1, region := (rows 1 0 4 13 16 32 127), good := (rows 109 80 93 73 80 96 64) }] }

theorem profile25_node233 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,65] 6 2 profile25_node233_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,65] 6 2 profile25_node233_cert).mp (by decide +kernel))

def profile25_node234_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 37 82 21 74 19 35 64), lower := (rows 37 82 21 74 16 32 64), losses := [{ target := 0, region := (rows 0 22 4 31 16 32 127), good := (rows 110 90 94 74 90 96 64) }] }

theorem profile25_node234 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,66] 6 3 profile25_node234_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17,66] 6 3 profile25_node234_cert).mp (by decide +kernel))

def profile25_node229_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node229_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node229 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,17] 6 (by decide) (choices 2) [3,65,66] profile25_node229_route profile25_node229_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node230
  · exact profile25_node233
  · exact profile25_node234

def profile25_node235_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 37 82 22 75 83 99 64), lower := (rows 37 82 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 102 86 86 72 86 96 64) }] }

theorem profile25_node235 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,18] 6 67 profile25_node235_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,18] 6 67 profile25_node235_cert).mp (by decide +kernel))

def profile25_node236_cert : CutBound 7 := { lost := (rows 2 1 2 0 0 0 0), upper := (rows 37 82 69 27 19 51 64), lower := (rows 37 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 100 82 68 72 82 96 64) },{ target := 1, region := (rows 33 0 37 8 16 32 127), good := (rows 101 80 69 72 80 101 64) }] }

theorem profile25_node236 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,65] 6 19 profile25_node236_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,65] 6 19 profile25_node236_cert).mp (by decide +kernel))

def profile25_node237_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 37 82 70 27 19 51 64), lower := (rows 37 82 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 22 8 16 32 127), good := (rows 100 86 70 72 86 96 64) }] }

theorem profile25_node237 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,66] 6 19 profile25_node237_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,66] 6 19 profile25_node237_cert).mp (by decide +kernel))

def profile25_node238_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 37 82 84 11 19 35 64), lower := (rows 37 82 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 102 86 86 72 86 96 64) }] }

theorem profile25_node238 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,80] 6 3 profile25_node238_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80,80] 6 3 profile25_node238_cert).mp (by decide +kernel))

def profile25_node221_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node221_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node221 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36,80] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node221_route profile25_node221_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node222
  · exact profile25_node229
  · exact profile25_node235
  · exact profile25_node236
  · exact profile25_node237
  · exact profile25_node238

def profile25_node200_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node200_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node200 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [36] 6 (by decide) (choices 2) [17,65,80] profile25_node200_route profile25_node200_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node201
  · exact profile25_node208
  · exact profile25_node221

def profile25_node241_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 49 7 7 90 82 114 64), lower := (rows 49 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 112 126 126 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) }] }

theorem profile25_node241 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,3] 6 82 profile25_node241_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,3] 6 82 profile25_node241_cert).mp (by decide +kernel))

def profile25_node242_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 49 7 21 74 82 98 64), lower := (rows 49 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 84 72 80 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 117 69 85 72 80 96 64) }] }

theorem profile25_node242 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,17] 6 66 profile25_node242_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,17] 6 66 profile25_node242_cert).mp (by decide +kernel))

def profile25_node243_cert : CutBound 7 := { lost := (rows 0 64 64 16 0 0 0), upper := (rows 49 7 22 75 83 99 64), lower := (rows 49 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 97 111 110 72 64 96 64) },{ target := 6, region := (rows 1 3 5 8 16 32 0), good := (rows 55 7 22 8 16 32 0) }] }

theorem profile25_node243 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,18] 6 67 profile25_node243_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,18] 6 67 profile25_node243_cert).mp (by decide +kernel))

def profile25_node244_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 49 7 69 90 82 114 64), lower := (rows 49 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 112 126 68 72 80 96 64) },{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 117 69 69 72 80 96 64) }] }

theorem profile25_node244 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,65] 6 82 profile25_node244_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,65] 6 82 profile25_node244_cert).mp (by decide +kernel))

def profile25_node245_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 49 7 70 91 83 115 64), lower := (rows 49 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 112 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) }] }

theorem profile25_node245 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,66] 6 83 profile25_node245_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,66] 6 83 profile25_node245_cert).mp (by decide +kernel))

def profile25_node246_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 49 7 84 75 83 99 64), lower := (rows 49 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 116 70 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 117 69 84 72 84 96 64) }] }

theorem profile25_node246 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,80] 6 67 profile25_node246_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5,80] 6 67 profile25_node246_cert).mp (by decide +kernel))

def profile25_node240_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node240_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node240 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,5] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node240_route profile25_node240_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node241
  · exact profile25_node242
  · exact profile25_node243
  · exact profile25_node244
  · exact profile25_node245
  · exact profile25_node246

def profile25_node247_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 49 19 71 79 87 103 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 97 111 68 72 64 96 64) }] }

theorem profile25_node247 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,17] 6 71 profile25_node247_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,17] 6 71 profile25_node247_cert).mp (by decide +kernel))

def profile25_node249_cert : CutBound 7 := { lost := (rows 0 64 64 16 0 0 0), upper := (rows 49 22 7 75 83 99 64), lower := (rows 49 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 97 110 111 72 64 96 64) },{ target := 6, region := (rows 1 3 5 8 16 32 0), good := (rows 55 22 7 8 16 32 0) }] }

theorem profile25_node249 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,3] 6 67 profile25_node249_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,3] 6 67 profile25_node249_cert).mp (by decide +kernel))

def profile25_node250_cert : CutBound 7 := { lost := (rows 0 0 18 0 0 0 0), upper := (rows 49 22 69 75 83 99 64), lower := (rows 49 22 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 117 84 69 72 80 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 70 69 72 64 96 64) }] }

theorem profile25_node250 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,65] 6 67 profile25_node250_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,65] 6 67 profile25_node250_cert).mp (by decide +kernel))

def profile25_node251_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 49 22 70 75 83 99 64), lower := (rows 49 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 118 86 70 72 86 96 64) }] }

theorem profile25_node251 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,66] 6 67 profile25_node251_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20,66] 6 67 profile25_node251_cert).mp (by decide +kernel))

def profile25_node248_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node248_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node248 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,20] 6 (by decide) (choices 2) [3,65,66] profile25_node248_route profile25_node248_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node249
  · exact profile25_node250
  · exact profile25_node251

def profile25_node253_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 49 67 7 94 86 118 64), lower := (rows 49 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 112 66 126 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) }] }

theorem profile25_node253 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,3] 6 86 profile25_node253_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,3] 6 86 profile25_node253_cert).mp (by decide +kernel))

def profile25_node254_cert : CutBound 7 := { lost := (rows 0 16 2 16 0 0 0), upper := (rows 49 67 21 78 86 102 64), lower := (rows 49 67 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 117 69 85 72 80 96 64) },{ target := 4, region := (rows 1 7 4 12 0 36 127), good := (rows 99 67 111 72 64 96 64) }] }

theorem profile25_node254 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,17] 6 70 profile25_node254_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,17] 6 70 profile25_node254_cert).mp (by decide +kernel))

def profile25_node256_cert : Bound 7 := { allowed := (rows 66 16 64 80 0 0 0), upper := (rows 49 67 22 11 84 100 64), lower := (rows 49 67 22 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 8 30 46 127), good := (rows 112 118 118 126 80 96 64) }] }

theorem profile25_node256 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,3] 6 68 profile25_node256_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,3] 6 68 profile25_node256_cert).mp (by decide +kernel))

def profile25_node257_cert : CutBound 7 := { lost := (rows 0 16 1 0 0 0 0), upper := (rows 49 67 22 13 82 98 64), lower := (rows 49 67 22 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 112 118 118 124 80 96 64) },{ target := 4, region := (rows 1 11 4 8 0 47 127), good := (rows 99 99 102 111 64 96 64) }] }

theorem profile25_node257 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,5] 6 66 profile25_node257_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,5] 6 66 profile25_node257_cert).mp (by decide +kernel))

def profile25_node258_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 49 67 22 14 81 97 64), lower := (rows 49 67 22 14 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 112 66 94 78 80 96 64) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 113 117 125 113 113 113) }] }

theorem profile25_node258 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,6] 6 65 profile25_node258_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,6] 6 65 profile25_node258_cert).mp (by decide +kernel))

def profile25_node259_cert : Bound 7 := { allowed := (rows 66 16 64 18 0 0 0), upper := (rows 49 67 22 73 22 38 64), lower := (rows 49 67 22 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 112 118 118 72 80 96 64) }] }

theorem profile25_node259 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,65] 6 6 profile25_node259_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,65] 6 6 profile25_node259_cert).mp (by decide +kernel))


#print axioms profile25_node259
end Delivery.SmallBudgetTenFinite7
