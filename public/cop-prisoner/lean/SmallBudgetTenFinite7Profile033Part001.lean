import SmallBudgetTenFinite7Profile033Part000

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile33_node131_cert : CutBound 7 := { lost := (rows 0 33 16 32 0 0 0), upper := (rows 49 82 37 79 87 103 64), lower := (rows 49 82 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 102 72 82 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 66 101 72 64 96 64) },{ target := 5, region := (rows 1 23 4 12 20 0 127), good := (rows 83 82 95 72 82 64 64) }] }

theorem profile33_node131 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,33] 6 71 profile33_node131_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,33] 6 71 profile33_node131_cert).mp (by decide +kernel))

def profile33_node132_cert : CutBound 7 := { lost := (rows 0 33 1 0 0 0 0), upper := (rows 49 82 38 77 85 101 64), lower := (rows 49 82 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 5 8 16 32 127), good := (rows 118 82 102 72 82 96 64) },{ target := 5, region := (rows 1 19 4 8 16 0 127), good := (rows 83 82 70 72 82 64 64) }] }

theorem profile33_node132 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,34] 6 69 profile33_node132_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,34] 6 69 profile33_node132_cert).mp (by decide +kernel))

def profile33_node133_cert : CutBound 7 := { lost := (rows 0 33 48 0 0 0 0), upper := (rows 49 82 69 47 55 39 64), lower := (rows 49 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 70 72 82 96 64) },{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 101 66 69 72 64 96 64) },{ target := 5, region := (rows 1 19 5 8 16 0 127), good := (rows 87 82 71 72 82 64 64) }] }

theorem profile33_node133 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,65] 6 39 profile33_node133_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,65] 6 39 profile33_node133_cert).mp (by decide +kernel))

def profile33_node134_cert : CutBound 7 := { lost := (rows 0 1 17 0 0 0 0), upper := (rows 49 82 70 45 53 37 64), lower := (rows 49 82 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 118 86 70 72 86 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 97 70 70 72 64 96 64) }] }

theorem profile33_node134 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,66] 6 37 profile33_node134_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,66] 6 37 profile33_node134_cert).mp (by decide +kernel))

def profile33_node135_cert : CutBound 7 := { lost := (rows 0 1 17 0 0 0 0), upper := (rows 49 82 100 15 23 39 64), lower := (rows 49 82 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 37 8 16 32 127), good := (rows 118 82 100 72 82 100 64) },{ target := 4, region := (rows 1 2 37 8 0 32 127), good := (rows 101 66 100 72 64 100 64) }] }

theorem profile33_node135 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,96] 6 7 profile33_node135_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80,96] 6 7 profile33_node135_cert).mp (by decide +kernel))

def profile33_node129_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node129_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node129 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48,80] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile33_node129_route profile33_node129_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node130
  · exact profile33_node131
  · exact profile33_node132
  · exact profile33_node133
  · exact profile33_node134
  · exact profile33_node135

def profile33_node102_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node102_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node102 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [48] 6 (by decide) (choices 2) [5,17,20,48,65,68,80] profile33_node102_route profile33_node102_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node103
  · exact profile33_node111
  · exact profile33_node112
  · exact profile33_node119
  · exact profile33_node120
  · exact profile33_node128
  · exact profile33_node129

def profile33_node137_cert : CutBound 7 := { lost := (rows 48 48 0 0 0 0 0), upper := (rows 67 7 117 121 113 113 64), lower := (rows 67 7 4 8 16 32 64), losses := [{ target := 4, region := (rows 7 6 4 8 0 32 127), good := (rows 67 71 71 72 64 96 64) },{ target := 5, region := (rows 7 6 4 8 16 0 127), good := (rows 67 71 71 72 80 64 64) }] }

theorem profile33_node137 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,5] 6 113 profile33_node137_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,5] 6 113 profile33_node137_cert).mp (by decide +kernel))

def profile33_node138_cert : CutBound 7 := { lost := (rows 48 32 0 0 0 0 0), upper := (rows 67 19 117 125 117 117 64), lower := (rows 67 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 19 18 4 8 16 0 127), good := (rows 67 83 68 72 83 64 64) }] }

theorem profile33_node138 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,17] 6 117 profile33_node138_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,17] 6 117 profile33_node138_cert).mp (by decide +kernel))

def profile33_node140_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 67 22 21 105 113 97 64), lower := (rows 67 22 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 66 86 86 72 80 96 64) },{ target := 4, region := (rows 3 2 4 15 0 39 127), good := (rows 107 111 109 72 64 96 64) }] }

theorem profile33_node140 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,17] 6 97 profile33_node140_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,17] 6 97 profile33_node140_cert).mp (by decide +kernel))

def profile33_node142_cert : CutBound 7 := { lost := (rows 16 1 16 0 0 0 0), upper := (rows 67 22 37 25 112 96 64), lower := (rows 67 22 37 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 120 112 112 112) },{ target := 4, region := (rows 3 2 15 8 0 127 127), good := (rows 103 103 101 109 96 96 96) }] }

theorem profile33_node142 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,17] 6 96 profile33_node142_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,17] 6 96 profile33_node142_cert).mp (by decide +kernel))

def profile33_node143_cert : CutBound 7 := { lost := (rows 16 1 16 16 0 0 0), upper := (rows 67 22 37 41 80 112 64), lower := (rows 67 22 37 41 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 120 112 112 112) },{ target := 4, region := (rows 3 2 12 12 0 32 127), good := (rows 67 79 109 109 64 96 64) }] }

theorem profile33_node143 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,33] 6 80 profile33_node143_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,33] 6 80 profile33_node143_cert).mp (by decide +kernel))

def profile33_node144_cert : CutBound 7 := { lost := (rows 48 32 16 0 0 0 0), upper := (rows 67 22 37 56 81 97 64), lower := (rows 67 22 37 56 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 39 127), good := (rows 103 103 101 104 64 96 64) },{ target := 5, region := (rows 7 6 4 8 23 0 127), good := (rows 83 87 87 88 80 64 64) }] }

theorem profile33_node144 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,48] 6 65 profile33_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,48] 6 65 profile33_node144_cert).mp (by decide +kernel))

def profile33_node145_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 67 22 37 73 48 48 64), lower := (rows 67 22 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 120 112 112 112) },{ target := 4, region := (rows 3 2 4 15 0 32 127), good := (rows 75 79 109 73 64 96 64) }] }

theorem profile33_node145 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,65] 6 48 profile33_node145_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,65] 6 48 profile33_node145_cert).mp (by decide +kernel))

def profile33_node146_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 67 22 37 88 49 33 64), lower := (rows 67 22 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 127), good := (rows 74 94 100 88 88 96 64) },{ target := 4, region := (rows 3 2 7 8 0 39 127), good := (rows 103 103 101 72 64 96 64) }] }

theorem profile33_node146 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,80] 6 33 profile33_node146_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,80] 6 33 profile33_node146_cert).mp (by decide +kernel))

def profile33_node147_cert : CutBound 7 := { lost := (rows 16 0 0 17 0 0 0), upper := (rows 67 22 37 104 17 49 64), lower := (rows 67 22 37 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 44 16 32 127), good := (rows 66 94 108 104 80 104 64) },{ target := 4, region := (rows 3 2 4 44 0 32 127), good := (rows 67 79 109 104 64 104 64) }] }

theorem profile33_node147 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,96] 6 17 profile33_node147_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33,96] 6 17 profile33_node147_cert).mp (by decide +kernel))

def profile33_node141_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node141_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node141 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,33] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node141_route profile33_node141_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node142
  · exact profile33_node143
  · exact profile33_node144
  · exact profile33_node145
  · exact profile33_node146
  · exact profile33_node147

def profile33_node148_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 67 22 52 105 113 97 64), lower := (rows 67 22 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 66 86 118 72 80 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 111 100 72 64 96 64) }] }

theorem profile33_node148 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,48] 6 97 profile33_node148_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,48] 6 97 profile33_node148_cert).mp (by decide +kernel))

def profile33_node149_cert : CutBound 7 := { lost := (rows 48 32 48 0 0 0 0), upper := (rows 67 22 69 57 49 49 64), lower := (rows 67 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 71 69 72 64 96 64) },{ target := 5, region := (rows 19 18 23 8 16 0 127), good := (rows 71 87 69 72 87 64 64) }] }

theorem profile33_node149 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,65] 6 49 profile33_node149_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,65] 6 49 profile33_node149_cert).mp (by decide +kernel))

def profile33_node150_cert : CutBound 7 := { lost := (rows 16 1 1 16 0 0 0), upper := (rows 67 22 84 41 49 33 64), lower := (rows 67 22 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 70 86 86 72 86 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 111 68 72 64 96 64) }] }

theorem profile33_node150 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,80] 6 33 profile33_node150_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,80] 6 33 profile33_node150_cert).mp (by decide +kernel))

def profile33_node151_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 67 22 100 57 49 49 64), lower := (rows 67 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 66 86 100 72 80 100 64) },{ target := 4, region := (rows 3 2 36 8 0 32 127), good := (rows 67 71 100 72 64 100 64) }] }

theorem profile33_node151 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,96] 6 49 profile33_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20,96] 6 49 profile33_node151_cert).mp (by decide +kernel))

def profile33_node139_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node139_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node139 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,20] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node139_route profile33_node139_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node140
  · exact profile33_node141
  · exact profile33_node148
  · exact profile33_node149
  · exact profile33_node150
  · exact profile33_node151

def profile33_node153_cert : CutBound 7 := { lost := (rows 48 0 32 16 0 0 0), upper := (rows 67 50 21 109 117 101 64), lower := (rows 67 50 21 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 12 0 36 127), good := (rows 67 99 109 72 64 96 64) },{ target := 5, region := (rows 3 2 6 8 16 0 127), good := (rows 71 87 85 72 80 64 64) }] }

theorem profile33_node153 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,17] 6 101 profile33_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,17] 6 101 profile33_node153_cert).mp (by decide +kernel))

def profile33_node154_cert : CutBound 7 := { lost := (rows 16 1 1 0 0 0 0), upper := (rows 67 50 52 77 85 101 64), lower := (rows 67 50 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 127), good := (rows 70 118 118 72 80 96 64) },{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 99 100 72 64 96 64) }] }

theorem profile33_node154 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,48] 6 69 profile33_node154_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,48] 6 69 profile33_node154_cert).mp (by decide +kernel))

def profile33_node155_cert : CutBound 7 := { lost := (rows 48 0 48 0 0 0 0), upper := (rows 67 50 69 61 53 53 64), lower := (rows 67 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) },{ target := 5, region := (rows 3 2 7 8 16 0 127), good := (rows 71 87 69 72 80 64 64) }] }

theorem profile33_node155 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,65] 6 53 profile33_node155_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,65] 6 53 profile33_node155_cert).mp (by decide +kernel))

def profile33_node156_cert : CutBound 7 := { lost := (rows 48 0 33 0 0 0 0), upper := (rows 67 50 84 45 53 37 64), lower := (rows 67 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 118 84 72 84 96 64) },{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 99 68 72 64 96 64) },{ target := 5, region := (rows 3 2 22 8 16 0 127), good := (rows 71 87 84 72 84 64 64) }] }

theorem profile33_node156 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,80] 6 37 profile33_node156_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48,80] 6 37 profile33_node156_cert).mp (by decide +kernel))

def profile33_node152_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node152_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node152 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,48] 6 (by decide) (choices 2) [17,48,65,80] profile33_node152_route profile33_node152_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile33_node153
  · exact profile33_node154
  · exact profile33_node155
  · exact profile33_node156

def profile33_node157_cert : CutBound 7 := { lost := (rows 48 48 0 0 0 0 0), upper := (rows 67 67 53 61 53 53 64), lower := (rows 67 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 127 127 4 8 0 32 127), good := (rows 67 67 71 75 67 99 67) },{ target := 5, region := (rows 127 127 4 8 16 0 127), good := (rows 67 67 71 75 83 67 67) }] }

theorem profile33_node157 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,65] 6 53 profile33_node157_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,65] 6 53 profile33_node157_cert).mp (by decide +kernel))

def profile33_node158_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 67 70 53 57 49 49 64), lower := (rows 67 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 66 70 70 72 80 96 64) },{ target := 4, region := (rows 7 6 4 8 0 32 127), good := (rows 67 71 71 72 64 96 64) }] }

theorem profile33_node158 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,68] 6 49 profile33_node158_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,68] 6 49 profile33_node158_cert).mp (by decide +kernel))

def profile33_node159_cert : CutBound 7 := { lost := (rows 48 33 0 0 0 0 0), upper := (rows 67 82 53 61 53 53 64), lower := (rows 67 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 66 82 68 72 82 96 64) },{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 19 18 4 8 16 0 127), good := (rows 67 83 68 72 83 64 64) }] }

theorem profile33_node159 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,80] 6 53 profile33_node159_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66,80] 6 53 profile33_node159_cert).mp (by decide +kernel))

def profile33_node136_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node136_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile33_node136 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [66] 6 (by decide) (choices 2) [5,17,20,48,65,68,80] profile33_node136_route profile33_node136_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node137
  · exact profile33_node138
  · exact profile33_node139
  · exact profile33_node152
  · exact profile33_node157
  · exact profile33_node158
  · exact profile33_node159

def profile33_node162_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 81 7 7 120 112 112 64), lower := (rows 81 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 127 127 127 127), good := (rows 120 126 126 120 120 120 120) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile33_node162 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,3] 6 112 profile33_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,3] 6 112 profile33_node162_cert).mp (by decide +kernel))

def profile33_node163_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 81 7 21 106 114 98 64), lower := (rows 81 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 84 72 80 96 64) },{ target := 4, region := (rows 1 6 4 14 0 38 127), good := (rows 65 111 111 72 64 96 64) }] }

theorem profile33_node163 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,17] 6 98 profile33_node163_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,17] 6 98 profile33_node163_cert).mp (by decide +kernel))

def profile33_node164_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 81 7 22 105 113 97 64), lower := (rows 81 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 11 0 35 127), good := (rows 105 111 110 72 64 96 64) },{ target := 5, region := (rows 21 23 21 8 16 0 127), good := (rows 87 71 87 72 87 64 64) }] }

theorem profile33_node164 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,18] 6 97 profile33_node164_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,18] 6 97 profile33_node164_cert).mp (by decide +kernel))

def profile33_node165_cert : CutBound 7 := { lost := (rows 32 48 0 1 0 0 0), upper := (rows 81 7 37 122 114 114 64), lower := (rows 81 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 100 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 71 103 72 64 96 64) },{ target := 5, region := (rows 17 6 4 8 16 0 127), good := (rows 81 71 71 72 81 64 64) }] }

theorem profile33_node165 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,33] 6 114 profile33_node165_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,33] 6 114 profile33_node165_cert).mp (by decide +kernel))

def profile33_node167_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 81 7 38 25 112 96 64), lower := (rows 81 7 38 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 11 15 8 0 127 127), good := (rows 103 103 102 111 96 96 96) }] }

theorem profile33_node167 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,17] 6 96 profile33_node167_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,17] 6 96 profile33_node167_cert).mp (by decide +kernel))

def profile33_node168_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 81 7 38 41 80 112 64), lower := (rows 81 7 38 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 10 12 8 0 32 127), good := (rows 65 71 102 111 64 96 64) }] }

theorem profile33_node168 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,33] 6 80 profile33_node168_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,33] 6 80 profile33_node168_cert).mp (by decide +kernel))

def profile33_node169_cert : CutBound 7 := { lost := (rows 32 48 16 0 0 0 0), upper := (rows 81 7 38 56 81 97 64), lower := (rows 81 7 38 56 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 35 127), good := (rows 103 103 102 104 64 96 64) },{ target := 5, region := (rows 127 6 4 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node169 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,48] 6 65 profile33_node169_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,48] 6 65 profile33_node169_cert).mp (by decide +kernel))

def profile33_node170_cert : CutBound 7 := { lost := (rows 32 0 1 48 0 0 0), upper := (rows 81 7 38 73 48 48 64), lower := (rows 81 7 38 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 2 4 11 0 32 127), good := (rows 73 79 110 73 64 96 64) },{ target := 5, region := (rows 17 2 4 27 16 0 127), good := (rows 89 79 78 73 89 64 64) }] }

theorem profile33_node170 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,65] 6 48 profile33_node170_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,65] 6 48 profile33_node170_cert).mp (by decide +kernel))

def profile33_node171_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 81 7 38 88 49 33 64), lower := (rows 81 7 38 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 88 78 102 88 88 96 64) },{ target := 4, region := (rows 1 3 7 8 0 35 127), good := (rows 103 103 102 72 64 96 64) }] }

theorem profile33_node171 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,80] 6 33 profile33_node171_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,80] 6 33 profile33_node171_cert).mp (by decide +kernel))

def profile33_node172_cert : CutBound 7 := { lost := (rows 32 32 0 17 0 0 0), upper := (rows 81 7 38 104 17 49 64), lower := (rows 81 7 38 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 44 16 32 127), good := (rows 80 78 110 104 80 104 64) },{ target := 4, region := (rows 1 2 4 44 0 32 127), good := (rows 65 79 110 104 64 104 64) },{ target := 5, region := (rows 127 6 4 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node172 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,96] 6 17 profile33_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34,96] 6 17 profile33_node172_cert).mp (by decide +kernel))

def profile33_node166_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node166_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node166 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,34] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node166_route profile33_node166_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node167
  · exact profile33_node168
  · exact profile33_node169
  · exact profile33_node170
  · exact profile33_node171
  · exact profile33_node172

def profile33_node173_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 81 7 52 107 115 99 64), lower := (rows 81 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 100 72 64 96 64) },{ target := 5, region := (rows 21 6 4 8 16 0 127), good := (rows 81 71 87 72 81 64 64) }] }

theorem profile33_node173 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,48] 6 99 profile33_node173_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,48] 6 99 profile33_node173_cert).mp (by decide +kernel))

def profile33_node174_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 81 7 69 58 50 50 64), lower := (rows 81 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 68 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile33_node174 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,65] 6 50 profile33_node174_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,65] 6 50 profile33_node174_cert).mp (by decide +kernel))

def profile33_node175_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 81 7 70 57 49 49 64), lower := (rows 81 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 71 71 70 72 64 96 64) }] }

theorem profile33_node175 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,66] 6 49 profile33_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,66] 6 49 profile33_node175_cert).mp (by decide +kernel))

def profile33_node176_cert : CutBound 7 := { lost := (rows 32 32 33 16 0 0 0), upper := (rows 81 7 84 43 51 35 64), lower := (rows 81 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 70 84 72 84 96 64) },{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 68 72 64 96 64) },{ target := 5, region := (rows 21 23 21 8 16 0 127), good := (rows 87 71 87 72 87 64 64) }] }

theorem profile33_node176 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,80] 6 35 profile33_node176_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,80] 6 35 profile33_node176_cert).mp (by decide +kernel))

def profile33_node177_cert : CutBound 7 := { lost := (rows 32 0 17 0 0 0 0), upper := (rows 81 7 100 59 51 51 64), lower := (rows 81 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 80 70 100 72 80 100 64) },{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 65 71 100 72 64 100 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 71 68 72 81 64 64) }] }

theorem profile33_node177 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,96] 6 51 profile33_node177_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5,96] 6 51 profile33_node177_cert).mp (by decide +kernel))

def profile33_node161_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node161_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node161 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,5] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile33_node161_route profile33_node161_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node162
  · exact profile33_node163
  · exact profile33_node164
  · exact profile33_node165
  · exact profile33_node166
  · exact profile33_node173
  · exact profile33_node174
  · exact profile33_node175
  · exact profile33_node176
  · exact profile33_node177

def profile33_node178_cert : CutBound 7 := { lost := (rows 32 32 16 16 0 0 0), upper := (rows 81 19 103 111 119 103 64), lower := (rows 81 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 65 111 68 72 64 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile33_node178 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,17] 6 103 profile33_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,17] 6 103 profile33_node178_cert).mp (by decide +kernel))

def profile33_node180_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 81 22 7 105 113 97 64), lower := (rows 81 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 105 110 111 72 64 96 64) },{ target := 5, region := (rows 19 19 23 8 16 0 127), good := (rows 87 87 71 72 87 64 64) }] }

theorem profile33_node180 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,3] 6 97 profile33_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,3] 6 97 profile33_node180_cert).mp (by decide +kernel))

def profile33_node182_cert : CutBound 7 := { lost := (rows 32 1 16 32 0 0 0), upper := (rows 81 22 37 11 112 96 64), lower := (rows 81 22 37 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 118 122 112 112 112) },{ target := 4, region := (rows 1 2 13 8 0 127 127), good := (rows 101 102 101 111 96 96 96) },{ target := 5, region := (rows 19 2 4 10 16 0 127), good := (rows 81 95 69 75 81 64 64) }] }

theorem profile33_node182 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,3] 6 96 profile33_node182_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,3] 6 96 profile33_node182_cert).mp (by decide +kernel))

def profile33_node183_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 81 22 37 41 82 98 64), lower := (rows 81 22 37 41 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 22 38 127), good := (rows 80 118 118 104 80 96 64) },{ target := 4, region := (rows 1 2 12 12 0 34 127), good := (rows 65 110 109 109 64 96 64) }] }

theorem profile33_node183 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,33] 6 66 profile33_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,33] 6 66 profile33_node183_cert).mp (by decide +kernel))

def profile33_node184_cert : CutBound 7 := { lost := (rows 32 32 16 16 0 0 0), upper := (rows 81 22 37 42 81 97 64), lower := (rows 81 22 37 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 10 0 37 127), good := (rows 101 110 101 106 64 96 64) },{ target := 5, region := (rows 127 6 4 8 127 0 127), good := (rows 81 87 87 91 81 81 81) }] }

theorem profile33_node184 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,34] 6 65 profile33_node184_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,34] 6 65 profile33_node184_cert).mp (by decide +kernel))

def profile33_node185_cert : Bound 7 := { allowed := (rows 32 96 80 32 0 0 0), upper := (rows 81 22 37 73 50 34 64), lower := (rows 81 22 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 22 38 127), good := (rows 80 118 118 72 80 96 64) },{ target := 4, region := (rows 1 2 4 13 0 34 127), good := (rows 73 110 109 73 64 96 64) }] }

theorem profile33_node185 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,65] 6 34 profile33_node185_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,65] 6 34 profile33_node185_cert).mp (by decide +kernel))

def profile33_node186_cert : CutBound 7 := { lost := (rows 0 0 16 17 0 0 0), upper := (rows 81 22 37 74 49 33 64), lower := (rows 81 22 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 94 100 74 80 96 64) },{ target := 4, region := (rows 1 2 5 10 0 37 127), good := (rows 101 110 101 74 64 96 64) }] }

theorem profile33_node186 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,66] 6 33 profile33_node186_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,66] 6 33 profile33_node186_cert).mp (by decide +kernel))

def profile33_node187_cert : Bound 7 := { allowed := (rows 32 97 80 0 0 0 0), upper := (rows 81 22 37 104 19 35 64), lower := (rows 81 22 37 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 44 16 32 127), good := (rows 80 94 108 104 80 104 64) },{ target := 4, region := (rows 1 2 4 44 0 32 127), good := (rows 65 78 109 104 64 104 64) }] }

theorem profile33_node187 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,96] 6 3 profile33_node187_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33,96] 6 3 profile33_node187_cert).mp (by decide +kernel))

def profile33_node181_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node181_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node181 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,33] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile33_node181_route profile33_node181_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node182
  · exact profile33_node183
  · exact profile33_node184
  · exact profile33_node185
  · exact profile33_node186
  · exact profile33_node187

def profile33_node189_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 81 22 38 41 81 97 64), lower := (rows 81 22 38 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 41 127), good := (rows 105 70 102 105 64 96 64) },{ target := 5, region := (rows 127 6 4 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node189 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,33] 6 65 profile33_node189_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,33] 6 65 profile33_node189_cert).mp (by decide +kernel))

def profile33_node190_cert : CutBound 7 := { lost := (rows 32 0 0 48 0 0 0), upper := (rows 81 22 38 73 49 33 64), lower := (rows 81 22 38 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 41 127), good := (rows 105 70 102 105 64 96 64) },{ target := 5, region := (rows 19 2 4 31 16 0 127), good := (rows 89 95 79 73 89 64 64) }] }

theorem profile33_node190 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,65] 6 33 profile33_node190_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,65] 6 33 profile33_node190_cert).mp (by decide +kernel))

def profile33_node191_cert : CutBound 7 := { lost := (rows 32 32 0 17 0 0 0), upper := (rows 81 22 38 104 17 33 64), lower := (rows 81 22 38 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 44 16 32 127), good := (rows 80 94 110 104 80 104 64) },{ target := 4, region := (rows 1 2 4 45 0 33 127), good := (rows 105 78 110 104 64 104 64) },{ target := 5, region := (rows 127 6 4 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node191 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,96] 6 1 profile33_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34,96] 6 1 profile33_node191_cert).mp (by decide +kernel))

def profile33_node188_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node188_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node188 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,34] 6 (by decide) (choices 2) [33,65,96] profile33_node188_route profile33_node188_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile33_node189
  · exact profile33_node190
  · exact profile33_node191

def profile33_node192_cert : CutBound 7 := { lost := (rows 32 32 48 0 0 0 0), upper := (rows 81 22 69 43 51 35 64), lower := (rows 81 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 70 69 72 64 96 64) },{ target := 5, region := (rows 19 19 23 8 16 0 127), good := (rows 87 87 71 72 87 64 64) }] }

theorem profile33_node192 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,65] 6 35 profile33_node192_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,65] 6 35 profile33_node192_cert).mp (by decide +kernel))

def profile33_node193_cert : CutBound 7 := { lost := (rows 0 1 17 16 0 0 0), upper := (rows 81 22 70 41 49 33 64), lower := (rows 81 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 86 86 70 72 86 96 64) },{ target := 4, region := (rows 1 2 6 9 0 33 127), good := (rows 105 70 70 72 64 96 64) }] }

theorem profile33_node193 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,66] 6 33 profile33_node193_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,66] 6 33 profile33_node193_cert).mp (by decide +kernel))

def profile33_node194_cert : CutBound 7 := { lost := (rows 32 0 17 0 0 0 0), upper := (rows 81 22 100 43 51 35 64), lower := (rows 81 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 80 86 100 72 80 100 64) },{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 65 70 100 72 64 100 64) },{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 87 68 72 81 64 64) }] }

theorem profile33_node194 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,96] 6 35 profile33_node194_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20,96] 6 35 profile33_node194_cert).mp (by decide +kernel))

def profile33_node179_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node179_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node179 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,20] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile33_node179_route profile33_node179_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node180
  · exact profile33_node181
  · exact profile33_node188
  · exact profile33_node192
  · exact profile33_node193
  · exact profile33_node194

def profile33_node196_cert : CutBound 7 := { lost := (rows 32 0 48 1 0 0 0), upper := (rows 81 35 7 124 116 116 64), lower := (rows 81 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 80 98 126 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 71 72 64 96 64) },{ target := 5, region := (rows 17 2 6 8 16 0 127), good := (rows 81 71 71 72 81 64 64) }] }

theorem profile33_node196 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,3] 6 116 profile33_node196_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,3] 6 116 profile33_node196_cert).mp (by decide +kernel))

def profile33_node197_cert : CutBound 7 := { lost := (rows 32 16 32 16 0 0 0), upper := (rows 81 35 21 110 118 102 64), lower := (rows 81 35 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 36 127), good := (rows 65 99 111 72 64 96 64) },{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile33_node197 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,17] 6 102 profile33_node197_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,17] 6 102 profile33_node197_cert).mp (by decide +kernel))

def profile33_node199_cert : CutBound 7 := { lost := (rows 32 16 1 32 0 0 0), upper := (rows 81 35 22 13 112 96 64), lower := (rows 81 35 22 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 127 127 127), good := (rows 112 118 118 124 112 112 112) },{ target := 4, region := (rows 1 11 4 8 0 127 127), good := (rows 99 99 102 111 96 96 96) },{ target := 5, region := (rows 21 2 4 12 16 0 127), good := (rows 81 67 95 77 81 64 64) }] }

theorem profile33_node199 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,5] 6 96 profile33_node199_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,5] 6 96 profile33_node199_cert).mp (by decide +kernel))

def profile33_node200_cert : CutBound 7 := { lost := (rows 0 16 1 16 0 0 0), upper := (rows 81 35 22 41 84 100 64), lower := (rows 81 35 22 41 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 80 118 118 104 80 96 64) },{ target := 4, region := (rows 1 10 4 10 0 36 127), good := (rows 65 107 110 107 64 96 64) }] }

theorem profile33_node200 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,33] 6 68 profile33_node200_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,33] 6 68 profile33_node200_cert).mp (by decide +kernel))

def profile33_node201_cert : CutBound 7 := { lost := (rows 32 16 32 16 0 0 0), upper := (rows 81 35 22 44 81 97 64), lower := (rows 81 35 22 44 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 12 0 35 127), good := (rows 99 99 110 108 64 96 64) },{ target := 5, region := (rows 127 2 6 8 127 0 127), good := (rows 81 87 87 93 81 81 81) }] }

theorem profile33_node201 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,36] 6 65 profile33_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,36] 6 65 profile33_node201_cert).mp (by decide +kernel))

def profile33_node202_cert : Bound 7 := { allowed := (rows 32 80 96 32 0 0 0), upper := (rows 81 35 22 73 52 36 64), lower := (rows 81 35 22 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 80 118 118 72 80 96 64) },{ target := 4, region := (rows 1 2 4 11 0 36 127), good := (rows 73 107 110 73 64 96 64) }] }

theorem profile33_node202 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,65] 6 36 profile33_node202_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,65] 6 36 profile33_node202_cert).mp (by decide +kernel))

def profile33_node203_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 81 35 22 76 49 33 64), lower := (rows 81 35 22 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 80 98 94 76 80 96 64) },{ target := 4, region := (rows 1 3 4 12 0 35 127), good := (rows 99 99 110 76 64 96 64) }] }

theorem profile33_node203 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,68] 6 33 profile33_node203_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,68] 6 33 profile33_node203_cert).mp (by decide +kernel))

def profile33_node204_cert : Bound 7 := { allowed := (rows 32 80 97 0 0 0 0), upper := (rows 81 35 22 104 21 37 64), lower := (rows 81 35 22 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 42 16 32 127), good := (rows 80 106 94 104 80 104 64) },{ target := 4, region := (rows 1 2 4 42 0 32 127), good := (rows 65 107 78 104 64 104 64) }] }

theorem profile33_node204 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,96] 6 5 profile33_node204_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18,96] 6 5 profile33_node204_cert).mp (by decide +kernel))

def profile33_node198_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node198_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node198 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,18] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile33_node198_route profile33_node198_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node199
  · exact profile33_node200
  · exact profile33_node201
  · exact profile33_node202
  · exact profile33_node203
  · exact profile33_node204

def profile33_node205_cert : CutBound 7 := { lost := (rows 32 16 16 0 0 0 0), upper := (rows 81 35 37 94 86 118 64), lower := (rows 81 35 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 6 8 0 32 127), good := (rows 65 103 103 72 64 96 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 67 69 72 81 64 64) }] }

theorem profile33_node205 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,33] 6 86 profile33_node205_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,33] 6 86 profile33_node205_cert).mp (by decide +kernel))

def profile33_node206_cert : CutBound 7 := { lost := (rows 32 0 17 32 0 0 0), upper := (rows 81 35 38 93 85 117 64), lower := (rows 81 35 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 102 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 102 72 64 96 64) },{ target := 5, region := (rows 21 2 4 12 20 0 127), good := (rows 81 67 95 72 81 64 64) }] }

theorem profile33_node206 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,34] 6 85 profile33_node206_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,34] 6 85 profile33_node206_cert).mp (by decide +kernel))

def profile33_node208_cert : Bound 7 := { allowed := (rows 32 80 64 96 0 0 0), upper := (rows 81 35 52 11 84 100 64), lower := (rows 81 35 52 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 116 118 116 126 116 116 116) },{ target := 4, region := (rows 1 2 4 10 0 36 127), good := (rows 65 107 100 75 64 96 64) }] }

theorem profile33_node208 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,3] 6 68 profile33_node208_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,3] 6 68 profile33_node208_cert).mp (by decide +kernel))

def profile33_node209_cert : Bound 7 := { allowed := (rows 32 64 64 112 0 0 0), upper := (rows 81 35 52 13 82 98 64), lower := (rows 81 35 52 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 18 34 127), good := (rows 80 118 116 76 80 96 64) },{ target := 4, region := (rows 1 11 4 8 0 43 127), good := (rows 99 99 100 111 64 96 64) }] }

theorem profile33_node209 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,5] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,5] 6 66 profile33_node209_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,5] 6 66 profile33_node209_cert).mp (by decide +kernel))

def profile33_node211_cert : CutBound 7 := { lost := (rows 0 16 1 17 0 0 0), upper := (rows 81 35 52 14 17 96 64), lower := (rows 81 35 52 14 17 32 64), losses := [{ target := 0, region := (rows 0 2 21 10 16 127 127), good := (rows 116 110 116 110 116 96 96) },{ target := 4, region := (rows 1 19 4 12 0 127 127), good := (rows 99 99 110 110 99 96 96) }] }

theorem profile33_node211 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6,1] 6 64 profile33_node211_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6,1] 6 64 profile33_node211_cert).mp (by decide +kernel))

def profile33_node212_cert : CutBound 7 := { lost := (rows 0 16 1 1 0 0 0), upper := (rows 81 35 52 14 80 33 64), lower := (rows 81 35 52 14 80 32 64), losses := [{ target := 0, region := (rows 0 2 38 10 127 32 127), good := (rows 80 126 116 94 80 116 80) },{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 100 110 64 96 64) }] }

theorem profile33_node212 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6,64] 6 1 profile33_node212_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6,64] 6 1 profile33_node212_cert).mp (by decide +kernel))

def profile33_node210_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile33_node210_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node210 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,6] 6 (by decide) (choices 1) [1,64] profile33_node210_route profile33_node210_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node211
  · exact profile33_node212

def profile33_node213_cert : Bound 7 := { allowed := (rows 32 80 64 48 0 0 0), upper := (rows 81 35 52 73 22 38 64), lower := (rows 81 35 52 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 18 34 127), good := (rows 80 118 116 72 80 96 64) }] }

theorem profile33_node213 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,65] 6 6 profile33_node213_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,65] 6 6 profile33_node213_cert).mp (by decide +kernel))

def profile33_node214_cert : Bound 7 := { allowed := (rows 32 80 65 32 0 0 0), upper := (rows 81 35 52 74 21 37 64), lower := (rows 81 35 52 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 106 116 74 80 96 64) },{ target := 4, region := (rows 1 2 4 10 0 32 127), good := (rows 65 107 100 74 64 96 64) }] }

theorem profile33_node214 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,66] 6 5 profile33_node214_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,66] 6 5 profile33_node214_cert).mp (by decide +kernel))

def profile33_node215_cert : CutBound 7 := { lost := (rows 0 16 0 17 0 0 0), upper := (rows 81 35 52 76 19 35 64), lower := (rows 81 35 52 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 80 98 124 76 80 96 64) },{ target := 4, region := (rows 1 3 4 12 0 35 127), good := (rows 99 99 108 76 64 96 64) }] }

theorem profile33_node215 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,68] 6 3 profile33_node215_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48,68] 6 3 profile33_node215_cert).mp (by decide +kernel))

def profile33_node207_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile33_node207_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node207 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,48] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile33_node207_route profile33_node207_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node208
  · exact profile33_node209
  · exact profile33_node210
  · exact profile33_node213
  · exact profile33_node214
  · exact profile33_node215

def profile33_node216_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 35 69 62 54 54 64), lower := (rows 81 35 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 8 0 32 127), good := (rows 69 103 69 72 64 96 64) },{ target := 5, region := (rows 17 2 23 8 16 0 127), good := (rows 85 71 69 72 85 64 64) }] }

theorem profile33_node216 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,65] 6 54 profile33_node216_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,65] 6 54 profile33_node216_cert).mp (by decide +kernel))

def profile33_node217_cert : CutBound 7 := { lost := (rows 32 0 49 0 0 0 0), upper := (rows 81 35 70 61 53 53 64), lower := (rows 81 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 70 72 64 96 64) },{ target := 5, region := (rows 17 2 6 8 16 0 127), good := (rows 81 71 70 72 81 64 64) }] }

theorem profile33_node217 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,66] 6 53 profile33_node217_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,66] 6 53 profile33_node217_cert).mp (by decide +kernel))

def profile33_node218_cert : CutBound 7 := { lost := (rows 32 0 33 0 0 0 0), upper := (rows 81 35 84 47 55 39 64), lower := (rows 81 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile33_node218 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,80] 6 39 profile33_node218_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,80] 6 39 profile33_node218_cert).mp (by decide +kernel))

def profile33_node219_cert : CutBound 7 := { lost := (rows 32 0 17 0 0 0 0), upper := (rows 81 35 100 31 23 55 64), lower := (rows 81 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 102 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 103 100 72 64 100 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 67 68 72 81 64 64) }] }

theorem profile33_node219 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,96] 6 23 profile33_node219_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33,96] 6 23 profile33_node219_cert).mp (by decide +kernel))

def profile33_node195_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node195_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node195 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,33] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile33_node195_route profile33_node195_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node196
  · exact profile33_node197
  · exact profile33_node198
  · exact profile33_node205
  · exact profile33_node206
  · exact profile33_node207
  · exact profile33_node216
  · exact profile33_node217
  · exact profile33_node218
  · exact profile33_node219

def profile33_node222_cert : CutBound 7 := { lost := (rows 0 17 16 0 0 0 0), upper := (rows 81 38 7 25 112 96 64), lower := (rows 81 38 7 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 15 13 8 0 127 127), good := (rows 103 102 103 111 96 96 96) }] }

theorem profile33_node222 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,17] 6 96 profile33_node222_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,17] 6 96 profile33_node222_cert).mp (by decide +kernel))

def profile33_node223_cert : CutBound 7 := { lost := (rows 0 17 16 0 0 0 0), upper := (rows 81 38 7 41 80 112 64), lower := (rows 81 38 7 41 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 10 12 8 0 32 127), good := (rows 65 102 71 111 64 96 64) }] }

theorem profile33_node223 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,33] 6 80 profile33_node223_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,33] 6 80 profile33_node223_cert).mp (by decide +kernel))

def profile33_node224_cert : CutBound 7 := { lost := (rows 32 16 48 0 0 0 0), upper := (rows 81 38 7 56 81 97 64), lower := (rows 81 38 7 56 16 32 64), losses := [{ target := 4, region := (rows 1 7 5 8 0 37 127), good := (rows 103 102 103 104 64 96 64) },{ target := 5, region := (rows 127 2 6 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node224 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,48] 6 65 profile33_node224_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,48] 6 65 profile33_node224_cert).mp (by decide +kernel))

def profile33_node225_cert : CutBound 7 := { lost := (rows 32 1 0 48 0 0 0), upper := (rows 81 38 7 73 48 48 64), lower := (rows 81 38 7 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 118 120 112 112 112) },{ target := 4, region := (rows 1 2 4 13 0 32 127), good := (rows 73 110 79 73 64 96 64) },{ target := 5, region := (rows 17 2 4 29 16 0 127), good := (rows 89 78 79 73 89 64 64) }] }

theorem profile33_node225 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,65] 6 48 profile33_node225_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,65] 6 48 profile33_node225_cert).mp (by decide +kernel))

def profile33_node226_cert : CutBound 7 := { lost := (rows 0 16 16 1 0 0 0), upper := (rows 81 38 7 88 49 33 64), lower := (rows 81 38 7 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 88 102 78 88 88 96 64) },{ target := 4, region := (rows 1 7 5 8 0 37 127), good := (rows 103 102 103 72 64 96 64) }] }

theorem profile33_node226 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,80] 6 33 profile33_node226_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,80] 6 33 profile33_node226_cert).mp (by decide +kernel))

def profile33_node227_cert : CutBound 7 := { lost := (rows 32 0 32 17 0 0 0), upper := (rows 81 38 7 104 17 49 64), lower := (rows 81 38 7 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 42 16 32 127), good := (rows 80 110 78 104 80 104 64) },{ target := 4, region := (rows 1 2 4 42 0 32 127), good := (rows 65 110 79 104 64 104 64) },{ target := 5, region := (rows 127 2 6 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node227 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,96] 6 17 profile33_node227_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3,96] 6 17 profile33_node227_cert).mp (by decide +kernel))

def profile33_node221_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile33_node221_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node221 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,3] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile33_node221_route profile33_node221_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node222
  · exact profile33_node223
  · exact profile33_node224
  · exact profile33_node225
  · exact profile33_node226
  · exact profile33_node227

def profile33_node228_cert : CutBound 7 := { lost := (rows 32 16 32 16 0 0 0), upper := (rows 81 38 21 107 115 99 64), lower := (rows 81 38 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 36 127), good := (rows 65 110 111 72 64 96 64) },{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile33_node228 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,17] 6 99 profile33_node228_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,17] 6 99 profile33_node228_cert).mp (by decide +kernel))

def profile33_node230_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 81 38 22 41 81 97 64), lower := (rows 81 38 22 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 41 127), good := (rows 105 102 70 105 64 96 64) },{ target := 5, region := (rows 127 2 6 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node230 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,33] 6 65 profile33_node230_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,33] 6 65 profile33_node230_cert).mp (by decide +kernel))

def profile33_node231_cert : CutBound 7 := { lost := (rows 32 0 0 48 0 0 0), upper := (rows 81 38 22 73 49 33 64), lower := (rows 81 38 22 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 41 127), good := (rows 105 102 70 105 64 96 64) },{ target := 5, region := (rows 21 2 4 31 16 0 127), good := (rows 89 79 95 73 89 64 64) }] }

theorem profile33_node231 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,65] 6 33 profile33_node231_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,65] 6 33 profile33_node231_cert).mp (by decide +kernel))

def profile33_node232_cert : CutBound 7 := { lost := (rows 32 0 32 17 0 0 0), upper := (rows 81 38 22 104 17 33 64), lower := (rows 81 38 22 104 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 42 16 32 127), good := (rows 80 110 94 104 80 104 64) },{ target := 4, region := (rows 1 2 4 43 0 33 127), good := (rows 105 110 78 104 64 104 64) },{ target := 5, region := (rows 127 2 6 8 127 0 127), good := (rows 81 87 87 89 81 81 81) }] }

theorem profile33_node232 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,96] 6 1 profile33_node232_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18,96] 6 1 profile33_node232_cert).mp (by decide +kernel))

def profile33_node229_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node229_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node229 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,18] 6 (by decide) (choices 2) [33,65,96] profile33_node229_route profile33_node229_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile33_node230
  · exact profile33_node231
  · exact profile33_node232

def profile33_node233_cert : CutBound 7 := { lost := (rows 32 17 0 32 0 0 0), upper := (rows 81 38 37 91 83 115 64), lower := (rows 81 38 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 80 102 102 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 102 103 72 64 96 64) },{ target := 5, region := (rows 19 2 4 10 18 0 127), good := (rows 81 95 69 72 81 64 64) }] }

theorem profile33_node233 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,33] 6 83 profile33_node233_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,33] 6 83 profile33_node233_cert).mp (by decide +kernel))

def profile33_node234_cert : CutBound 7 := { lost := (rows 0 17 17 0 0 0 0), upper := (rows 81 38 38 89 81 113 64), lower := (rows 81 38 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 38 8 16 32 127), good := (rows 80 102 102 72 80 102 64) },{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 65 102 102 72 64 102 64) }] }

theorem profile33_node234 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,34] 6 81 profile33_node234_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,34] 6 81 profile33_node234_cert).mp (by decide +kernel))

def profile33_node235_cert : CutBound 7 := { lost := (rows 32 17 0 32 0 0 0), upper := (rows 81 38 52 75 83 99 64), lower := (rows 81 38 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 80 102 118 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 102 102 72 64 96 64) },{ target := 5, region := (rows 23 2 4 10 18 0 127), good := (rows 81 95 85 72 81 64 64) }] }

theorem profile33_node235 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,48] 6 67 profile33_node235_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,48] 6 67 profile33_node235_cert).mp (by decide +kernel))

def profile33_node236_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 38 69 59 51 51 64), lower := (rows 81 38 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 102 69 72 64 96 64) },{ target := 5, region := (rows 17 2 21 8 16 0 127), good := (rows 85 70 69 72 85 64 64) }] }

theorem profile33_node236 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,65] 6 51 profile33_node236_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,65] 6 51 profile33_node236_cert).mp (by decide +kernel))

def profile33_node237_cert : CutBound 7 := { lost := (rows 0 17 17 0 0 0 0), upper := (rows 81 38 70 57 49 49 64), lower := (rows 81 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 38 8 16 32 127), good := (rows 80 102 70 72 80 102 64) },{ target := 4, region := (rows 1 34 38 8 0 32 127), good := (rows 65 102 70 72 64 102 64) }] }

theorem profile33_node237 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,66] 6 49 profile33_node237_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,66] 6 49 profile33_node237_cert).mp (by decide +kernel))

def profile33_node238_cert : CutBound 7 := { lost := (rows 32 0 33 0 0 0 0), upper := (rows 81 38 84 43 51 35 64), lower := (rows 81 38 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile33_node238 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,80] 6 35 profile33_node238_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,80] 6 35 profile33_node238_cert).mp (by decide +kernel))

def profile33_node239_cert : CutBound 7 := { lost := (rows 0 17 17 0 0 0 0), upper := (rows 81 38 100 27 19 51 64), lower := (rows 81 38 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 38 38 8 16 32 127), good := (rows 80 102 102 72 80 102 64) },{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 65 102 102 72 64 102 64) }] }

theorem profile33_node239 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,96] 6 19 profile33_node239_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36,96] 6 19 profile33_node239_cert).mp (by decide +kernel))

def profile33_node220_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile33_node220_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node220 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,36] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile33_node220_route profile33_node220_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node221
  · exact profile33_node228
  · exact profile33_node229
  · exact profile33_node233
  · exact profile33_node234
  · exact profile33_node235
  · exact profile33_node236
  · exact profile33_node237
  · exact profile33_node238
  · exact profile33_node239

def profile33_node241_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 81 50 7 109 117 101 64), lower := (rows 81 50 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 65 98 111 72 64 96 64) },{ target := 5, region := (rows 19 2 6 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile33_node241 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,3] 6 101 profile33_node241_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,3] 6 101 profile33_node241_cert).mp (by decide +kernel))

def profile33_node243_cert : Bound 7 := { allowed := (rows 32 64 64 112 0 0 0), upper := (rows 81 50 37 11 84 100 64), lower := (rows 81 50 37 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 20 36 127), good := (rows 80 114 118 74 80 96 64) },{ target := 4, region := (rows 1 2 13 8 0 45 127), good := (rows 101 98 101 111 64 96 64) }] }

theorem profile33_node243 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,3] 6 68 profile33_node243_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,3] 6 68 profile33_node243_cert).mp (by decide +kernel))

def profile33_node244_cert : Bound 7 := { allowed := (rows 32 64 80 96 0 0 0), upper := (rows 81 50 37 13 82 98 64), lower := (rows 81 50 37 13 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 126 114 114 114) },{ target := 4, region := (rows 1 2 4 12 0 34 127), good := (rows 65 98 109 77 64 96 64) }] }

theorem profile33_node244 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,5] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,5] 6 66 profile33_node244_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,5] 6 66 profile33_node244_cert).mp (by decide +kernel))

def profile33_node246_cert : CutBound 7 := { lost := (rows 0 1 16 17 0 0 0), upper := (rows 81 50 37 14 17 96 64), lower := (rows 81 50 37 14 17 32 64), losses := [{ target := 0, region := (rows 0 19 4 12 16 127 127), good := (rows 114 114 110 110 114 96 96) },{ target := 4, region := (rows 1 2 21 10 0 127 127), good := (rows 101 110 101 110 101 96 96) }] }

theorem profile33_node246 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6,1] 6 64 profile33_node246_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6,1] 6 64 profile33_node246_cert).mp (by decide +kernel))

def profile33_node247_cert : CutBound 7 := { lost := (rows 0 1 16 1 0 0 0), upper := (rows 81 50 37 14 80 33 64), lower := (rows 81 50 37 14 80 32 64), losses := [{ target := 0, region := (rows 0 38 4 12 127 32 127), good := (rows 80 114 126 94 80 114 80) },{ target := 4, region := (rows 1 2 5 8 0 37 127), good := (rows 101 98 101 110 64 96 64) }] }

theorem profile33_node247 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6,64] 6 1 profile33_node247_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6,64] 6 1 profile33_node247_cert).mp (by decide +kernel))

def profile33_node245_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile33_node245_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node245 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,6] 6 (by decide) (choices 1) [1,64] profile33_node245_route profile33_node245_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile33_node246
  · exact profile33_node247

def profile33_node248_cert : Bound 7 := { allowed := (rows 32 64 80 48 0 0 0), upper := (rows 81 50 37 73 22 38 64), lower := (rows 81 50 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 20 36 127), good := (rows 80 114 118 72 80 96 64) }] }

theorem profile33_node248 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,65] 6 6 profile33_node248_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,65] 6 6 profile33_node248_cert).mp (by decide +kernel))

def profile33_node249_cert : CutBound 7 := { lost := (rows 0 0 16 17 0 0 0), upper := (rows 81 50 37 74 21 37 64), lower := (rows 81 50 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 122 100 74 80 96 64) },{ target := 4, region := (rows 1 2 5 10 0 37 127), good := (rows 101 106 101 74 64 96 64) }] }

theorem profile33_node249 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,66] 6 5 profile33_node249_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,66] 6 5 profile33_node249_cert).mp (by decide +kernel))

def profile33_node250_cert : Bound 7 := { allowed := (rows 32 65 80 32 0 0 0), upper := (rows 81 50 37 76 19 35 64), lower := (rows 81 50 37 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 80 114 108 76 80 96 64) },{ target := 4, region := (rows 1 2 4 12 0 32 127), good := (rows 65 98 109 76 64 96 64) }] }

theorem profile33_node250 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,68] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,68] 6 3 profile33_node250_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33,68] 6 3 profile33_node250_cert).mp (by decide +kernel))

def profile33_node242_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile33_node242_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node242 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,33] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile33_node242_route profile33_node242_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node243
  · exact profile33_node244
  · exact profile33_node245
  · exact profile33_node248
  · exact profile33_node249
  · exact profile33_node250

def profile33_node251_cert : CutBound 7 := { lost := (rows 32 0 17 32 0 0 0), upper := (rows 81 50 38 77 85 101 64), lower := (rows 81 50 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 102 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 102 72 64 96 64) },{ target := 5, region := (rows 23 2 4 12 20 0 127), good := (rows 81 83 95 72 81 64 64) }] }

theorem profile33_node251 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,34] 6 69 profile33_node251_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,34] 6 69 profile33_node251_cert).mp (by decide +kernel))

def profile33_node252_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 50 69 47 55 39 64), lower := (rows 81 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 98 69 72 64 96 64) },{ target := 5, region := (rows 19 2 23 8 16 0 127), good := (rows 85 87 69 72 85 64 64) }] }

theorem profile33_node252 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,65] 6 39 profile33_node252_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,65] 6 39 profile33_node252_cert).mp (by decide +kernel))

def profile33_node253_cert : CutBound 7 := { lost := (rows 32 0 49 0 0 0 0), upper := (rows 81 50 70 45 53 37 64), lower := (rows 81 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 70 72 80 96 64) },{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 70 72 64 96 64) },{ target := 5, region := (rows 19 2 6 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile33_node253 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,66] 6 37 profile33_node253_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,66] 6 37 profile33_node253_cert).mp (by decide +kernel))

def profile33_node254_cert : CutBound 7 := { lost := (rows 32 0 17 0 0 0 0), upper := (rows 81 50 100 15 23 39 64), lower := (rows 81 50 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 80 118 100 72 80 100 64) },{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 102 100 72 64 100 64) },{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 83 68 72 81 64 64) }] }

theorem profile33_node254 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,96] 6 7 profile33_node254_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48,96] 6 7 profile33_node254_cert).mp (by decide +kernel))

def profile33_node240_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile33_node240_route : Route 7 := (fun mask => (mask,id))

theorem profile33_node240 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,48] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile33_node240_route profile33_node240_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile33_node241
  · exact profile33_node242
  · exact profile33_node251
  · exact profile33_node252
  · exact profile33_node253
  · exact profile33_node254

def profile33_node255_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 81 67 55 63 55 55 64), lower := (rows 81 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile33_node255 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,65] 6 55 profile33_node255_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,65] 6 55 profile33_node255_cert).mp (by decide +kernel))

def profile33_node256_cert : CutBound 7 := { lost := (rows 32 49 0 0 0 0 0), upper := (rows 81 70 55 59 51 51 64), lower := (rows 81 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 80 70 70 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 70 70 72 64 96 64) },{ target := 5, region := (rows 17 6 4 8 16 0 127), good := (rows 81 70 70 72 81 64 64) }] }

theorem profile33_node256 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,68] 6 51 profile33_node256_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,68] 6 51 profile33_node256_cert).mp (by decide +kernel))

def profile33_node257_cert : CutBound 7 := { lost := (rows 32 33 0 0 0 0 0), upper := (rows 81 82 39 47 55 39 64), lower := (rows 81 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile33_node257 : Upper (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,80] 6 39 profile33_node257_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,32,18,18,2]) (R (n:=7) [34,33,33,32,18,18,2]) [80,80] 6 39 profile33_node257_cert).mp (by decide +kernel))


#print axioms profile33_node257
end Delivery.SmallBudgetTenFinite7
