import SmallBudgetTenFinite7Profile021Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile21_node114_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node114_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node114 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,68] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile21_node114_route profile21_node114_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node115
  · exact profile21_node116
  · exact profile21_node123
  · exact profile21_node124
  · exact profile21_node125
  · exact profile21_node126
  · exact profile21_node127
  · exact profile21_node128
  · exact profile21_node129
  · exact profile21_node130

def profile21_node131_cert : CutBound 7 := { lost := (rows 0 1 32 32 32 0 0), upper := (rows 35 98 79 79 95 32 64), lower := (rows 35 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 66 68 72 80 64 64) }] }

theorem profile21_node131 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,96] 6 79 profile21_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34,96] 6 79 profile21_node131_cert).mp (by decide +kernel))

def profile21_node64_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node64_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile21_node64 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [34] 6 (by decide) (choices 2) [5,12,33,36,65,68,96] profile21_node64_route profile21_node64_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node65
  · exact profile21_node76
  · exact profile21_node89
  · exact profile21_node90
  · exact profile21_node91
  · exact profile21_node114
  · exact profile21_node131

def profile21_node134_cert : CutBound 7 := { lost := (rows 2 0 32 1 1 0 0), upper := (rows 37 11 7 106 114 32 64), lower := (rows 37 11 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 127 127), good := (rows 124 122 126 104 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 105 101 104 112 96 96) },{ target := 5, region := (rows 1 2 6 8 16 0 127), good := (rows 69 79 71 72 80 64 64) }] }

theorem profile21_node134 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,3] 6 98 profile21_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,3] 6 98 profile21_node134_cert).mp (by decide +kernel))

def profile21_node135_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 37 11 37 74 82 32 64), lower := (rows 37 11 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 100 122 100 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 109 101 109 117 101 101) }] }

theorem profile21_node135 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,33] 6 66 profile21_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,33] 6 66 profile21_node135_cert).mp (by decide +kernel))

def profile21_node136_cert : CutBound 7 := { lost := (rows 2 32 1 32 32 0 0), upper := (rows 37 11 38 75 83 32 64), lower := (rows 37 11 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 100 110 102 104 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 105 101 104 112 96 96) },{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 95 91 94 72 80 64 64) }] }

theorem profile21_node136 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,34] 6 67 profile21_node136_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,34] 6 67 profile21_node136_cert).mp (by decide +kernel))

def profile21_node137_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 37 11 69 106 114 32 64), lower := (rows 37 11 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 100 122 100 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 109 101 109 117 101 101) }] }

theorem profile21_node137 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,65] 6 98 profile21_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,65] 6 98 profile21_node137_cert).mp (by decide +kernel))

def profile21_node138_cert : CutBound 7 := { lost := (rows 66 0 33 0 0 0 0), upper := (rows 37 11 70 107 115 32 64), lower := (rows 37 11 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 100 110 102 104 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 105 101 104 112 96 96) },{ target := 5, region := (rows 1 2 6 8 16 0 127), good := (rows 69 79 70 72 80 64 64) },{ target := 6, region := (rows 5 2 4 8 16 127 0), good := (rows 37 43 39 40 48 32 32) }] }

theorem profile21_node138 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,66] 6 99 profile21_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,66] 6 99 profile21_node138_cert).mp (by decide +kernel))

def profile21_node139_cert : CutBound 7 := { lost := (rows 2 32 3 32 32 0 0), upper := (rows 37 11 100 75 83 32 64), lower := (rows 37 11 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 100 110 100 108 116 100 100) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 109 101 109 117 101 101) },{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 95 91 68 72 80 64 64) }] }

theorem profile21_node139 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,96] 6 67 profile21_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9,96] 6 67 profile21_node139_cert).mp (by decide +kernel))

def profile21_node133_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node133_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node133 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,9] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node133_route profile21_node133_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node134
  · exact profile21_node135
  · exact profile21_node136
  · exact profile21_node137
  · exact profile21_node138
  · exact profile21_node139

def profile21_node140_cert : CutBound 7 := { lost := (rows 2 0 32 32 32 0 0), upper := (rows 37 35 79 75 91 32 64), lower := (rows 37 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 97 101 104 112 96 96) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 69 95 68 72 80 64 64) }] }

theorem profile21_node140 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,33] 6 75 profile21_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,33] 6 75 profile21_node140_cert).mp (by decide +kernel))

def profile21_node141_cert : CutBound 7 := { lost := (rows 66 65 0 0 0 0 0), upper := (rows 37 42 71 75 83 32 64), lower := (rows 37 42 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 127 127), good := (rows 100 106 100 106 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 104 101 104 112 96 96) },{ target := 6, region := (rows 5 10 4 8 16 127 0), good := (rows 37 42 37 42 48 32 32) }] }

theorem profile21_node141 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,40] 6 67 profile21_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,40] 6 67 profile21_node141_cert).mp (by decide +kernel))

def profile21_node143_cert : CutBound 7 := { lost := (rows 2 32 32 1 1 0 0), upper := (rows 37 67 7 106 122 32 64), lower := (rows 37 67 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 127 127), good := (rows 124 122 126 104 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 97 101 104 112 96 96) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile21_node143 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,3] 6 106 profile21_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,3] 6 106 profile21_node143_cert).mp (by decide +kernel))

def profile21_node144_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 37 67 13 106 114 32 64), lower := (rows 37 67 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 100 122 108 104 112 96 96) },{ target := 1, region := (rows 13 0 12 8 16 127 127), good := (rows 101 97 109 109 112 96 96) }] }

theorem profile21_node144 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,9] 6 98 profile21_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,9] 6 98 profile21_node144_cert).mp (by decide +kernel))

def profile21_node146_cert : CutBound 7 := { lost := (rows 2 0 1 0 3 0 0), upper := (rows 37 67 14 11 112 32 64), lower := (rows 37 67 14 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 116 114 126 126 112 112 112) },{ target := 1, region := (rows 5 0 4 8 127 127 127), good := (rows 117 113 125 121 112 112 112) }] }

theorem profile21_node146 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,3] 6 96 profile21_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,3] 6 96 profile21_node146_cert).mp (by decide +kernel))

def profile21_node147_cert : CutBound 7 := { lost := (rows 2 32 32 2 33 0 0), upper := (rows 37 67 14 41 82 32 64), lower := (rows 37 67 14 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 22 127 127), good := (rows 116 114 126 104 112 96 96) },{ target := 1, region := (rows 5 0 4 15 16 127 127), good := (rows 109 105 109 105 112 96 96) },{ target := 5, region := (rows 1 11 12 8 31 0 127), good := (rows 87 83 94 95 80 64 64) }] }

theorem profile21_node147 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,33] 6 66 profile21_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,33] 6 66 profile21_node147_cert).mp (by decide +kernel))

def profile21_node148_cert : CutBound 7 := { lost := (rows 2 0 1 1 2 0 0), upper := (rows 37 67 14 42 81 32 64), lower := (rows 37 67 14 42 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 14 16 127 127), good := (rows 108 110 110 110 112 96 96) },{ target := 1, region := (rows 5 0 4 8 23 127 127), good := (rows 117 113 125 120 112 96 96) }] }

theorem profile21_node148 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,34] 6 65 profile21_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,34] 6 65 profile21_node148_cert).mp (by decide +kernel))

def profile21_node149_cert : CutBound 7 := { lost := (rows 2 32 32 34 1 0 0), upper := (rows 37 67 14 73 50 32 64), lower := (rows 37 67 14 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 22 127 127), good := (rows 116 114 126 104 112 96 96) },{ target := 1, region := (rows 5 0 4 15 16 127 127), good := (rows 109 105 109 105 112 96 96) },{ target := 5, region := (rows 1 11 15 11 16 0 127), good := (rows 79 79 78 79 80 64 64) }] }

theorem profile21_node149 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,65] 6 34 profile21_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,65] 6 34 profile21_node149_cert).mp (by decide +kernel))

def profile21_node150_cert : CutBound 7 := { lost := (rows 2 0 1 1 2 0 0), upper := (rows 37 67 14 74 49 32 64), lower := (rows 37 67 14 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 14 16 127 127), good := (rows 108 110 110 110 112 96 96) },{ target := 1, region := (rows 5 0 4 8 23 127 127), good := (rows 117 113 125 120 112 96 96) }] }

theorem profile21_node150 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,66] 6 33 profile21_node150_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,66] 6 33 profile21_node150_cert).mp (by decide +kernel))

def profile21_node151_cert : CutBound 7 := { lost := (rows 2 0 1 3 0 0 0), upper := (rows 37 67 14 104 19 32 64), lower := (rows 37 67 14 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 127 16 127 127), good := (rows 108 110 110 104 120 104 104) },{ target := 1, region := (rows 5 0 4 127 16 127 127), good := (rows 109 105 109 104 120 104 104) }] }

theorem profile21_node151 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,96] 6 3 profile21_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10,96] 6 3 profile21_node151_cert).mp (by decide +kernel))

def profile21_node145_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node145_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node145 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,10] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile21_node145_route profile21_node145_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node146
  · exact profile21_node147
  · exact profile21_node148
  · exact profile21_node149
  · exact profile21_node150
  · exact profile21_node151

def profile21_node152_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 37 67 37 74 90 32 64), lower := (rows 37 67 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 100 122 100 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) }] }

theorem profile21_node152 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,33] 6 74 profile21_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,33] 6 74 profile21_node152_cert).mp (by decide +kernel))

def profile21_node153_cert : CutBound 7 := { lost := (rows 2 32 1 32 32 0 0), upper := (rows 37 67 38 75 91 32 64), lower := (rows 37 67 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 100 102 102 104 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 97 101 104 112 96 96) },{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 95 91 94 72 80 64 64) }] }

theorem profile21_node153 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,34] 6 75 profile21_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,34] 6 75 profile21_node153_cert).mp (by decide +kernel))

def profile21_node154_cert : CutBound 7 := { lost := (rows 2 32 3 32 32 0 0), upper := (rows 37 67 44 75 83 32 64), lower := (rows 37 67 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 100 98 108 108 112 96 96) },{ target := 1, region := (rows 13 0 12 8 16 127 127), good := (rows 101 97 109 109 112 96 96) },{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 95 91 76 72 80 64 64) }] }

theorem profile21_node154 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,40] 6 67 profile21_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,40] 6 67 profile21_node154_cert).mp (by decide +kernel))

def profile21_node155_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 37 67 69 42 58 32 64), lower := (rows 37 67 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 100 122 100 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) }] }

theorem profile21_node155 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,65] 6 42 profile21_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,65] 6 42 profile21_node155_cert).mp (by decide +kernel))

def profile21_node156_cert : CutBound 7 := { lost := (rows 2 32 33 0 0 0 0), upper := (rows 37 67 70 43 59 32 64), lower := (rows 37 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 100 102 102 104 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 97 101 104 112 96 96) },{ target := 5, region := (rows 1 3 7 8 16 0 127), good := (rows 71 71 70 72 80 64 64) }] }

theorem profile21_node156 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,66] 6 43 profile21_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,66] 6 43 profile21_node156_cert).mp (by decide +kernel))

def profile21_node157_cert : CutBound 7 := { lost := (rows 2 32 35 0 0 0 0), upper := (rows 37 67 76 43 51 32 64), lower := (rows 37 67 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 100 98 108 108 112 96 96) },{ target := 1, region := (rows 13 0 12 8 16 127 127), good := (rows 101 97 109 109 112 96 96) },{ target := 5, region := (rows 1 3 12 8 16 0 127), good := (rows 71 67 76 76 80 64 64) }] }

theorem profile21_node157 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,72] 6 35 profile21_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,72] 6 35 profile21_node157_cert).mp (by decide +kernel))

def profile21_node158_cert : CutBound 7 := { lost := (rows 2 32 3 32 32 0 0), upper := (rows 37 67 100 11 27 32 64), lower := (rows 37 67 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 100 102 100 108 116 100 100) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 5, region := (rows 1 3 4 11 19 0 127), good := (rows 95 91 68 72 80 64 64) }] }

theorem profile21_node158 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,96] 6 11 profile21_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65,96] 6 11 profile21_node158_cert).mp (by decide +kernel))

def profile21_node142_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node142_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node142 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,65] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile21_node142_route profile21_node142_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node143
  · exact profile21_node144
  · exact profile21_node145
  · exact profile21_node152
  · exact profile21_node153
  · exact profile21_node154
  · exact profile21_node155
  · exact profile21_node156
  · exact profile21_node157
  · exact profile21_node158

def profile21_node159_cert : CutBound 7 := { lost := (rows 66 33 0 0 0 0 0), upper := (rows 37 74 103 107 115 32 64), lower := (rows 37 74 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 4 8 16 127 127), good := (rows 100 106 100 106 112 96 96) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 104 101 104 112 96 96) },{ target := 5, region := (rows 1 10 4 8 16 0 127), good := (rows 69 74 68 74 80 64 64) },{ target := 6, region := (rows 5 2 4 8 16 127 0), good := (rows 37 42 37 40 48 32 32) }] }

theorem profile21_node159 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,72] 6 99 profile21_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,72] 6 99 profile21_node159_cert).mp (by decide +kernel))

def profile21_node161_cert : CutBound 7 := { lost := (rows 2 1 0 32 32 0 0), upper := (rows 37 98 7 75 91 32 64), lower := (rows 37 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 96 101 104 112 96 96) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 93 66 95 72 80 64 64) }] }

theorem profile21_node161 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,3] 6 75 profile21_node161_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,3] 6 75 profile21_node161_cert).mp (by decide +kernel))

def profile21_node162_cert : CutBound 7 := { lost := (rows 66 1 66 0 0 0 0), upper := (rows 37 98 13 75 83 32 64), lower := (rows 37 98 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 110 106 114 98 98) },{ target := 1, region := (rows 13 0 12 8 16 127 127), good := (rows 101 96 109 109 112 96 96) },{ target := 6, region := (rows 13 2 12 8 16 127 0), good := (rows 37 34 45 45 48 32 32) }] }

theorem profile21_node162 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,9] 6 67 profile21_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,9] 6 67 profile21_node162_cert).mp (by decide +kernel))

def profile21_node163_cert : CutBound 7 := { lost := (rows 66 1 1 0 0 0 0), upper := (rows 37 98 14 75 83 32 64), lower := (rows 37 98 14 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 102 98 110 110 114 98 98) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 96 109 104 112 96 96) },{ target := 6, region := (rows 5 2 4 8 16 127 0), good := (rows 37 34 47 40 48 32 32) }] }

theorem profile21_node163 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,10] 6 67 profile21_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,10] 6 67 profile21_node163_cert).mp (by decide +kernel))

def profile21_node164_cert : CutBound 7 := { lost := (rows 2 1 34 0 0 0 0), upper := (rows 37 98 69 11 27 32 64), lower := (rows 37 98 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 102 98 102 106 114 98 98) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 69 66 69 72 80 64 64) }] }

theorem profile21_node164 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,65] 6 11 profile21_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,65] 6 11 profile21_node164_cert).mp (by decide +kernel))

def profile21_node165_cert : CutBound 7 := { lost := (rows 2 1 33 0 0 0 0), upper := (rows 37 98 70 11 27 32 64), lower := (rows 37 98 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 5 0 4 8 16 127 127), good := (rows 101 96 101 104 112 96 96) },{ target := 5, region := (rows 1 2 6 8 16 0 127), good := (rows 69 70 70 72 80 64 64) }] }

theorem profile21_node165 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,66] 6 11 profile21_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,66] 6 11 profile21_node165_cert).mp (by decide +kernel))

def profile21_node166_cert : CutBound 7 := { lost := (rows 2 1 3 0 0 0 0), upper := (rows 37 98 76 11 19 32 64), lower := (rows 37 98 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 102 98 110 110 114 98 98) },{ target := 1, region := (rows 13 0 12 8 16 127 127), good := (rows 101 96 109 109 112 96 96) }] }

theorem profile21_node166 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,72] 6 3 profile21_node166_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96,72] 6 3 profile21_node166_cert).mp (by decide +kernel))

def profile21_node160_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile21_node160_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node160 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36,96] 6 (by decide) (choices 2) [3,9,10,65,66,72] profile21_node160_route profile21_node160_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node161
  · exact profile21_node162
  · exact profile21_node163
  · exact profile21_node164
  · exact profile21_node165
  · exact profile21_node166

def profile21_node132_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node132_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node132 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [36] 6 (by decide) (choices 2) [9,33,40,65,72,96] profile21_node132_route profile21_node132_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node133
  · exact profile21_node140
  · exact profile21_node141
  · exact profile21_node142
  · exact profile21_node159
  · exact profile21_node160

def profile21_node169_cert : CutBound 7 := { lost := (rows 2 32 32 1 1 0 0), upper := (rows 97 7 7 106 122 32 64), lower := (rows 97 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 127 127), good := (rows 96 126 126 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 5, region := (rows 1 7 7 8 16 0 127), good := (rows 71 71 71 72 80 64 64) }] }

theorem profile21_node169 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,3] 6 106 profile21_node169_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,3] 6 106 profile21_node169_cert).mp (by decide +kernel))

def profile21_node170_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 97 7 13 106 114 32 64), lower := (rows 97 7 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 96 126 108 104 112 96 96) },{ target := 1, region := (rows 127 0 12 8 16 127 127), good := (rows 97 101 109 109 113 97 97) }] }

theorem profile21_node170 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,9] 6 98 profile21_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,9] 6 98 profile21_node170_cert).mp (by decide +kernel))

def profile21_node172_cert : CutBound 7 := { lost := (rows 2 0 1 0 3 0 0), upper := (rows 97 7 14 11 112 32 64), lower := (rows 97 7 14 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 127 127 127), good := (rows 112 118 126 126 112 112 112) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 125 121 113 113 113) }] }

theorem profile21_node172 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,3] 6 96 profile21_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,3] 6 96 profile21_node172_cert).mp (by decide +kernel))

def profile21_node173_cert : CutBound 7 := { lost := (rows 2 32 32 2 33 0 0), upper := (rows 97 7 14 41 82 32 64), lower := (rows 97 7 14 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 22 127 127), good := (rows 96 118 126 104 112 96 96) },{ target := 1, region := (rows 127 0 4 127 16 127 127), good := (rows 105 109 109 105 121 105 105) },{ target := 5, region := (rows 1 10 12 8 30 0 127), good := (rows 65 87 94 95 80 64 64) }] }

theorem profile21_node173 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,33] 6 66 profile21_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,33] 6 66 profile21_node173_cert).mp (by decide +kernel))

def profile21_node174_cert : CutBound 7 := { lost := (rows 2 0 1 1 2 0 0), upper := (rows 97 7 14 42 81 32 64), lower := (rows 97 7 14 42 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 14 16 127 127), good := (rows 96 110 110 110 112 96 96) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 125 121 113 113 113) }] }

theorem profile21_node174 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,34] 6 65 profile21_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,34] 6 65 profile21_node174_cert).mp (by decide +kernel))

def profile21_node175_cert : CutBound 7 := { lost := (rows 2 0 1 3 0 0 0), upper := (rows 97 7 14 104 19 32 64), lower := (rows 97 7 14 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 127 16 127 127), good := (rows 104 110 110 104 120 104 104) },{ target := 1, region := (rows 127 0 4 127 16 127 127), good := (rows 105 109 109 105 121 105 105) }] }

theorem profile21_node175 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,96] 6 3 profile21_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10,96] 6 3 profile21_node175_cert).mp (by decide +kernel))

def profile21_node171_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node171_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node171 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,10] 6 (by decide) (choices 2) [3,33,34,96] profile21_node171_route profile21_node171_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node172
  · exact profile21_node173
  · exact profile21_node174
  · exact profile21_node175

def profile21_node176_cert : CutBound 7 := { lost := (rows 2 0 2 1 1 0 0), upper := (rows 97 7 37 74 90 32 64), lower := (rows 97 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 127 127), good := (rows 96 126 100 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) }] }

theorem profile21_node176 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,33] 6 74 profile21_node176_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,33] 6 74 profile21_node176_cert).mp (by decide +kernel))

def profile21_node177_cert : CutBound 7 := { lost := (rows 2 0 1 32 32 0 0), upper := (rows 97 7 38 75 91 32 64), lower := (rows 97 7 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 94 72 80 64 64) }] }

theorem profile21_node177 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,34] 6 75 profile21_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,34] 6 75 profile21_node177_cert).mp (by decide +kernel))

def profile21_node178_cert : CutBound 7 := { lost := (rows 2 0 3 32 32 0 0), upper := (rows 97 7 44 75 83 32 64), lower := (rows 97 7 44 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 127 127), good := (rows 96 102 108 108 112 96 96) },{ target := 1, region := (rows 127 0 12 8 16 127 127), good := (rows 97 101 109 109 113 97 97) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 76 72 80 64 64) }] }

theorem profile21_node178 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,40] 6 67 profile21_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,40] 6 67 profile21_node178_cert).mp (by decide +kernel))

def profile21_node179_cert : CutBound 7 := { lost := (rows 2 0 3 32 32 0 0), upper := (rows 97 7 100 11 27 32 64), lower := (rows 97 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 16 127 127), good := (rows 100 102 100 108 116 100 100) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 5, region := (rows 1 2 4 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile21_node179 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,96] 6 11 profile21_node179_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5,96] 6 11 profile21_node179_cert).mp (by decide +kernel))

def profile21_node168_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node168_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node168 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,5] 6 (by decide) (choices 2) [3,9,10,33,34,40,96] profile21_node168_route profile21_node168_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node169
  · exact profile21_node170
  · exact profile21_node171
  · exact profile21_node176
  · exact profile21_node177
  · exact profile21_node178
  · exact profile21_node179

def profile21_node182_cert : CutBound 7 := { lost := (rows 2 32 32 32 3 0 0), upper := (rows 97 14 7 11 112 32 64), lower := (rows 97 14 7 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 127 127 127), good := (rows 112 126 118 122 112 112 112) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 125 117 121 113 113 113) },{ target := 5, region := (rows 1 15 13 13 16 0 127), good := (rows 79 78 79 79 80 64 64) }] }

theorem profile21_node182 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,3] 6 96 profile21_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,3] 6 96 profile21_node182_cert).mp (by decide +kernel))

def profile21_node183_cert : CutBound 7 := { lost := (rows 2 32 32 2 33 0 0), upper := (rows 97 14 7 41 82 32 64), lower := (rows 97 14 7 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 8 22 127 127), good := (rows 96 126 118 104 112 96 96) },{ target := 1, region := (rows 127 0 4 127 16 127 127), good := (rows 105 109 109 105 121 105 105) },{ target := 5, region := (rows 1 10 12 8 30 0 127), good := (rows 65 94 87 95 80 64 64) }] }

theorem profile21_node183 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,33] 6 66 profile21_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,33] 6 66 profile21_node183_cert).mp (by decide +kernel))

def profile21_node184_cert : CutBound 7 := { lost := (rows 2 1 0 1 2 0 0), upper := (rows 97 14 7 42 81 32 64), lower := (rows 97 14 7 42 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 14 16 127 127), good := (rows 96 110 110 106 112 96 96) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 125 117 121 113 113 113) }] }

theorem profile21_node184 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,34] 6 65 profile21_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,34] 6 65 profile21_node184_cert).mp (by decide +kernel))

def profile21_node185_cert : CutBound 7 := { lost := (rows 2 1 0 3 0 0 0), upper := (rows 97 14 7 104 19 32 64), lower := (rows 97 14 7 104 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 127 16 127 127), good := (rows 104 110 110 104 120 104 104) },{ target := 1, region := (rows 127 0 4 127 16 127 127), good := (rows 105 109 109 105 121 105 105) }] }

theorem profile21_node185 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,96] 6 3 profile21_node185_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3,96] 6 3 profile21_node185_cert).mp (by decide +kernel))

def profile21_node181_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node181_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node181 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,3] 6 (by decide) (choices 2) [3,33,34,96] profile21_node181_route profile21_node181_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node182
  · exact profile21_node183
  · exact profile21_node184
  · exact profile21_node185

def profile21_node186_cert : CutBound 7 := { lost := (rows 2 32 2 32 32 0 0), upper := (rows 97 14 37 75 83 32 64), lower := (rows 97 14 37 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 109 101 109 117 101 101) },{ target := 5, region := (rows 1 6 4 12 20 0 127), good := (rows 65 94 95 72 80 64 64) }] }

theorem profile21_node186 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,33] 6 67 profile21_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,33] 6 67 profile21_node186_cert).mp (by decide +kernel))

def profile21_node187_cert : CutBound 7 := { lost := (rows 2 65 65 0 0 0 0), upper := (rows 97 14 38 75 83 32 64), lower := (rows 97 14 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 14 8 16 127 127), good := (rows 96 110 102 110 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 109 101 105 113 97 97) },{ target := 6, region := (rows 1 10 14 8 16 127 0), good := (rows 33 46 38 46 48 32 32) }] }

theorem profile21_node187 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,34] 6 67 profile21_node187_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,34] 6 67 profile21_node187_cert).mp (by decide +kernel))

def profile21_node188_cert : CutBound 7 := { lost := (rows 2 1 3 0 0 0 0), upper := (rows 97 14 100 11 19 32 64), lower := (rows 97 14 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 127 8 16 127 127), good := (rows 100 110 100 110 116 100 100) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 109 101 109 117 101 101) }] }

theorem profile21_node188 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,96] 6 3 profile21_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12,96] 6 3 profile21_node188_cert).mp (by decide +kernel))

def profile21_node180_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node180_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node180 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,12] 6 (by decide) (choices 2) [3,33,34,96] profile21_node180_route profile21_node180_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile21_node181
  · exact profile21_node186
  · exact profile21_node187
  · exact profile21_node188

def profile21_node189_cert : CutBound 7 := { lost := (rows 2 0 32 32 32 0 0), upper := (rows 97 35 79 79 95 32 64), lower := (rows 97 35 4 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) },{ target := 5, region := (rows 1 2 6 10 18 0 127), good := (rows 65 95 68 72 80 64 64) }] }

theorem profile21_node189 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,33] 6 79 profile21_node189_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,33] 6 79 profile21_node189_cert).mp (by decide +kernel))

def profile21_node191_cert : CutBound 7 := { lost := (rows 2 1 0 32 32 0 0), upper := (rows 97 38 7 75 91 32 64), lower := (rows 97 38 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 65 94 95 72 80 64 64) }] }

theorem profile21_node191 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,3] 6 75 profile21_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,3] 6 75 profile21_node191_cert).mp (by decide +kernel))

def profile21_node192_cert : CutBound 7 := { lost := (rows 2 65 2 0 0 0 0), upper := (rows 97 38 13 75 83 32 64), lower := (rows 97 38 13 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 110 104 112 96 96) },{ target := 1, region := (rows 127 0 12 8 16 127 127), good := (rows 97 101 109 109 113 97 97) },{ target := 6, region := (rows 1 6 4 8 16 127 0), good := (rows 33 38 47 40 48 32 32) }] }

theorem profile21_node192 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,9] 6 67 profile21_node192_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,9] 6 67 profile21_node192_cert).mp (by decide +kernel))

def profile21_node193_cert : CutBound 7 := { lost := (rows 2 65 65 0 0 0 0), upper := (rows 97 38 14 75 83 32 64), lower := (rows 97 38 14 8 16 32 64), losses := [{ target := 0, region := (rows 0 14 12 8 16 127 127), good := (rows 96 102 110 110 112 96 96) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 109 105 113 97 97) },{ target := 6, region := (rows 1 14 12 8 16 127 0), good := (rows 33 38 46 46 48 32 32) }] }

theorem profile21_node193 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,10] 6 67 profile21_node193_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,10] 6 67 profile21_node193_cert).mp (by decide +kernel))

def profile21_node194_cert : CutBound 7 := { lost := (rows 2 1 34 0 0 0 0), upper := (rows 97 38 69 11 27 32 64), lower := (rows 97 38 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 127 127), good := (rows 96 102 102 104 112 96 96) },{ target := 1, region := (rows 127 0 127 8 16 127 127), good := (rows 101 101 101 109 117 101 101) },{ target := 5, region := (rows 1 2 5 8 16 0 127), good := (rows 69 70 69 72 80 64 64) }] }

theorem profile21_node194 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,65] 6 11 profile21_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,65] 6 11 profile21_node194_cert).mp (by decide +kernel))

def profile21_node195_cert : CutBound 7 := { lost := (rows 2 1 33 0 0 0 0), upper := (rows 97 38 70 11 27 32 64), lower := (rows 97 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 8 16 127 127), good := (rows 102 102 102 110 118 102 102) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 101 101 105 113 97 97) },{ target := 5, region := (rows 1 2 6 8 16 0 127), good := (rows 65 70 70 72 80 64 64) }] }

theorem profile21_node195 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,66] 6 11 profile21_node195_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,66] 6 11 profile21_node195_cert).mp (by decide +kernel))

def profile21_node196_cert : CutBound 7 := { lost := (rows 2 1 3 0 0 0 0), upper := (rows 97 38 76 11 19 32 64), lower := (rows 97 38 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 14 12 8 16 127 127), good := (rows 96 102 110 110 112 96 96) },{ target := 1, region := (rows 127 0 12 8 16 127 127), good := (rows 97 101 109 109 113 97 97) }] }

theorem profile21_node196 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,72] 6 3 profile21_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36,72] 6 3 profile21_node196_cert).mp (by decide +kernel))

def profile21_node190_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile21_node190_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node190 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,36] 6 (by decide) (choices 2) [3,9,10,65,66,72] profile21_node190_route profile21_node190_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile21_node191
  · exact profile21_node192
  · exact profile21_node193
  · exact profile21_node194
  · exact profile21_node195
  · exact profile21_node196

def profile21_node198_cert : CutBound 7 := { lost := (rows 2 1 0 32 32 0 0), upper := (rows 97 98 7 15 31 32 64), lower := (rows 97 98 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 98 98 102 106 114 98 98) },{ target := 1, region := (rows 127 0 4 8 16 127 127), good := (rows 97 97 101 105 113 97 97) },{ target := 5, region := (rows 1 2 4 12 20 0 127), good := (rows 65 66 95 72 80 64 64) }] }

theorem profile21_node198 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,3] 6 15 profile21_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,3] 6 15 profile21_node198_cert).mp (by decide +kernel))

def profile21_node200_cert : CutBound 7 := { lost := (rows 2 1 2 0 1 0 0), upper := (rows 97 98 13 11 22 32 64), lower := (rows 97 98 13 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 20 127 127), good := (rows 98 98 126 106 114 98 98) },{ target := 1, region := (rows 127 0 12 8 16 127 127), good := (rows 97 97 109 109 113 97 97) }] }

theorem profile21_node200 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,3] 6 6 profile21_node200_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,3] 6 6 profile21_node200_cert).mp (by decide +kernel))

def profile21_node201_cert : CutBound 7 := { lost := (rows 2 1 2 2 1 0 0), upper := (rows 97 98 13 13 18 32 64), lower := (rows 97 98 13 13 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 126 126 114 114 114) },{ target := 1, region := (rows 127 0 127 127 16 127 127), good := (rows 109 109 109 109 125 109 109) }] }

theorem profile21_node201 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,5] 6 2 profile21_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,5] 6 2 profile21_node201_cert).mp (by decide +kernel))

def profile21_node202_cert : CutBound 7 := { lost := (rows 2 1 2 1 0 0 0), upper := (rows 97 98 13 14 19 32 64), lower := (rows 97 98 13 14 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 12 16 127 127), good := (rows 98 98 110 110 114 98 98) },{ target := 1, region := (rows 127 0 12 8 16 127 127), good := (rows 97 97 109 109 113 97 97) }] }

theorem profile21_node202 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,6] 6 3 profile21_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9,6] 6 3 profile21_node202_cert).mp (by decide +kernel))

def profile21_node199_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile21_node199_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node199 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,9] 6 (by decide) (choices 2) [3,5,6] profile21_node199_route profile21_node199_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node200
  · exact profile21_node201
  · exact profile21_node202

def profile21_node204_cert : CutBound 7 := { lost := (rows 2 1 1 0 2 0 0), upper := (rows 97 98 14 11 21 32 64), lower := (rows 97 98 14 11 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 98 98 110 110 114 98 98) },{ target := 1, region := (rows 127 0 4 8 20 127 127), good := (rows 97 97 125 105 113 97 97) }] }

theorem profile21_node204 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,3] 6 5 profile21_node204_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,3] 6 5 profile21_node204_cert).mp (by decide +kernel))

def profile21_node205_cert : CutBound 7 := { lost := (rows 2 1 1 2 0 0 0), upper := (rows 97 98 14 13 19 32 64), lower := (rows 97 98 14 13 16 32 64), losses := [{ target := 0, region := (rows 0 127 12 8 16 127 127), good := (rows 98 98 110 110 114 98 98) },{ target := 1, region := (rows 127 0 4 12 16 127 127), good := (rows 97 97 109 109 113 97 97) }] }

theorem profile21_node205 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,5] 6 3 profile21_node205_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,5] 6 3 profile21_node205_cert).mp (by decide +kernel))

def profile21_node206_cert : CutBound 7 := { lost := (rows 2 1 1 1 2 0 0), upper := (rows 97 98 14 14 17 32 64), lower := (rows 97 98 14 14 16 32 64), losses := [{ target := 0, region := (rows 0 127 127 127 16 127 127), good := (rows 110 110 110 110 126 110 110) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 113 125 125 113 113 113) }] }

theorem profile21_node206 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,6] 6 1 profile21_node206_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10,6] 6 1 profile21_node206_cert).mp (by decide +kernel))

def profile21_node203_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile21_node203_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node203 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96,10] 6 (by decide) (choices 2) [3,5,6] profile21_node203_route profile21_node203_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node204
  · exact profile21_node205
  · exact profile21_node206

def profile21_node197_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 4 | 40 => 5 | 72 => 6 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile21_node197_route : Route 7 := (fun mask => (mask,id))

theorem profile21_node197 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96,96] 6 (by decide) (choices 2) [3,9,10] profile21_node197_route profile21_node197_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile21_node198
  · exact profile21_node199
  · exact profile21_node203

def profile21_node167_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node167_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node167 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [96] 6 (by decide) (choices 2) [5,12,33,36,96] profile21_node167_route profile21_node167_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile21_node168
  · exact profile21_node180
  · exact profile21_node189
  · exact profile21_node190
  · exact profile21_node197

def profile21_node0_column : Nat → Fin 7 := fun mask => match mask with | 18 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile21_node0_route : Route 7 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile21_node0 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [] 6 (by decide) (choices 2) [6,12,34,36,96] profile21_node0_route profile21_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile21_node1
  · exact profile21_node41
  · exact profile21_node64
  · exact profile21_node132
  · exact profile21_node167

theorem profile21 : Upper (D (n:=7) [34,34,33,33,32,2,2]) (R (n:=7) [34,34,33,33,32,2,2]) [] 6 := profile21_node0


#print axioms profile21
end Delivery.SmallBudgetTenFinite7
