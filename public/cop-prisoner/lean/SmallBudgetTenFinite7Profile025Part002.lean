import SmallBudgetTenFinite7Profile025Part001

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile25_node260_cert : Bound 7 := { allowed := (rows 66 16 65 16 0 0 0), upper := (rows 49 67 22 74 21 37 64), lower := (rows 49 67 22 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 112 74 94 74 80 96 64) }] }

theorem profile25_node260 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,66] 6 5 profile25_node260_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,66] 6 5 profile25_node260_cert).mp (by decide +kernel))

def profile25_node261_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 49 67 22 76 19 35 64), lower := (rows 49 67 22 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 112 66 94 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 113 65 92 76 80 96 64) }] }

theorem profile25_node261 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,68] 6 3 profile25_node261_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18,68] 6 3 profile25_node261_cert).mp (by decide +kernel))

def profile25_node255_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node255_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node255 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,18] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile25_node255_route profile25_node255_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node256
  · exact profile25_node257
  · exact profile25_node258
  · exact profile25_node259
  · exact profile25_node260
  · exact profile25_node261

def profile25_node262_cert : CutBound 7 := { lost := (rows 0 16 18 0 0 0 0), upper := (rows 49 67 69 30 22 54 64), lower := (rows 49 67 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 117 69 69 72 80 96 64) },{ target := 4, region := (rows 1 7 7 8 0 32 127), good := (rows 103 71 71 72 64 96 64) }] }

theorem profile25_node262 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,65] 6 22 profile25_node262_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,65] 6 22 profile25_node262_cert).mp (by decide +kernel))

def profile25_node263_cert : CutBound 7 := { lost := (rows 0 16 17 0 0 0 0), upper := (rows 49 67 70 31 23 55 64), lower := (rows 49 67 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 112 70 70 72 80 96 64) },{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 103 71 70 72 64 96 64) }] }

theorem profile25_node263 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,66] 6 23 profile25_node263_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,66] 6 23 profile25_node263_cert).mp (by decide +kernel))

def profile25_node264_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 49 67 84 15 23 39 64), lower := (rows 49 67 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 116 70 84 72 84 96 64) },{ target := 1, region := (rows 1 0 21 8 16 32 127), good := (rows 117 69 84 72 84 96 64) }] }

theorem profile25_node264 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,80] 6 7 profile25_node264_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65,80] 6 7 profile25_node264_cert).mp (by decide +kernel))

def profile25_node252_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node252_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node252 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,65] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node252_route profile25_node252_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node253
  · exact profile25_node254
  · exact profile25_node255
  · exact profile25_node262
  · exact profile25_node263
  · exact profile25_node264

def profile25_node265_cert : CutBound 7 := { lost := (rows 0 17 0 0 0 0 0), upper := (rows 49 70 87 91 83 115 64), lower := (rows 49 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 112 70 70 72 80 96 64) },{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 97 70 70 72 64 96 64) }] }

theorem profile25_node265 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,68] 6 83 profile25_node265_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,68] 6 83 profile25_node265_cert).mp (by decide +kernel))

def profile25_node267_cert : CutBound 7 := { lost := (rows 0 1 0 16 0 0 0), upper := (rows 49 82 7 79 87 103 64), lower := (rows 49 82 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 70 72 82 96 64) },{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 97 66 111 72 64 96 64) }] }

theorem profile25_node267 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,3] 6 71 profile25_node267_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,3] 6 71 profile25_node267_cert).mp (by decide +kernel))

def profile25_node268_cert : CutBound 7 := { lost := (rows 0 1 2 0 0 0 0), upper := (rows 49 82 69 15 23 39 64), lower := (rows 49 82 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 70 72 82 96 64) },{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 117 80 69 72 80 96 64) }] }

theorem profile25_node268 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,65] 6 7 profile25_node268_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,65] 6 7 profile25_node268_cert).mp (by decide +kernel))

def profile25_node269_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 49 82 70 15 23 39 64), lower := (rows 49 82 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 118 86 70 72 86 96 64) }] }

theorem profile25_node269 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,66] 6 7 profile25_node269_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80,66] 6 7 profile25_node269_cert).mp (by decide +kernel))

def profile25_node266_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node266_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node266 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48,80] 6 (by decide) (choices 2) [3,65,66] profile25_node266_route profile25_node266_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node267
  · exact profile25_node268
  · exact profile25_node269

def profile25_node239_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 12 => 3 | 36 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node239_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node239 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [48] 6 (by decide) (choices 2) [5,17,20,65,68,80] profile25_node239_route profile25_node239_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node240
  · exact profile25_node247
  · exact profile25_node248
  · exact profile25_node252
  · exact profile25_node265
  · exact profile25_node266

def profile25_node271_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 67 7 119 123 115 115 64), lower := (rows 67 7 4 8 16 32 64), losses := [{ target := 4, region := (rows 7 6 4 8 0 32 127), good := (rows 67 71 71 72 64 96 64) }] }

theorem profile25_node271 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,5] 6 115 profile25_node271_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,5] 6 115 profile25_node271_cert).mp (by decide +kernel))

def profile25_node273_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 67 19 7 124 116 116 64), lower := (rows 67 19 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 66 82 126 72 80 96 64) },{ target := 1, region := (rows 1 0 4 12 20 36 127), good := (rows 65 81 125 72 80 96 64) }] }

theorem profile25_node273 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,3] 6 116 profile25_node273_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,3] 6 116 profile25_node273_cert).mp (by decide +kernel))

def profile25_node274_cert : CutBound 7 := { lost := (rows 16 0 2 0 0 0 0), upper := (rows 67 19 21 110 118 102 64), lower := (rows 67 19 21 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 6 8 16 32 127), good := (rows 69 85 85 72 80 96 64) },{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 69 72 64 96 64) }] }

theorem profile25_node274 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,17] 6 102 profile25_node274_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,17] 6 102 profile25_node274_cert).mp (by decide +kernel))

def profile25_node275_cert : CutBound 7 := { lost := (rows 16 0 1 16 0 0 0), upper := (rows 67 19 22 109 117 101 64), lower := (rows 67 19 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 70 86 86 72 80 96 64) },{ target := 4, region := (rows 7 2 4 12 0 36 127), good := (rows 67 67 111 72 64 96 64) }] }

theorem profile25_node275 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,18] 6 101 profile25_node275_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,18] 6 101 profile25_node275_cert).mp (by decide +kernel))

def profile25_node277_cert : CutBound 7 := { lost := (rows 16 0 2 0 0 0 0), upper := (rows 67 19 37 14 80 112 64), lower := (rows 67 19 37 14 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 127 127 127), good := (rows 117 117 117 124 112 112 112) },{ target := 4, region := (rows 11 2 4 8 0 32 127), good := (rows 67 67 101 79 64 96 64) }] }

theorem profile25_node277 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,6] 6 80 profile25_node277_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,6] 6 80 profile25_node277_cert).mp (by decide +kernel))

def profile25_node278_cert : Bound 7 := { allowed := (rows 16 64 82 64 0 0 0), upper := (rows 67 19 37 26 84 100 64), lower := (rows 67 19 37 26 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 20 36 127), good := (rows 74 90 116 90 80 96 64) }] }

theorem profile25_node278 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,18] 6 68 profile25_node278_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,18] 6 68 profile25_node278_cert).mp (by decide +kernel))

def profile25_node279_cert : CutBound 7 := { lost := (rows 16 0 16 1 0 0 0), upper := (rows 67 19 37 28 82 98 64), lower := (rows 67 19 37 28 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 19 35 127), good := (rows 114 114 124 92 80 96 64) },{ target := 4, region := (rows 3 2 7 8 0 35 127), good := (rows 103 103 101 76 64 96 64) }] }

theorem profile25_node279 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,20] 6 66 profile25_node279_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,20] 6 66 profile25_node279_cert).mp (by decide +kernel))

def profile25_node280_cert : Bound 7 := { allowed := (rows 16 64 82 16 0 0 0), upper := (rows 67 19 37 74 20 52 64), lower := (rows 67 19 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 20 36 127), good := (rows 74 90 124 74 80 96 64) }] }

theorem profile25_node280 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,66] 6 20 profile25_node280_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,66] 6 20 profile25_node280_cert).mp (by decide +kernel))

def profile25_node281_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 67 19 37 76 18 50 64), lower := (rows 67 19 37 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 19 35 127), good := (rows 114 114 124 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 65 81 109 76 80 96 64) }] }

theorem profile25_node281 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,68] 6 18 profile25_node281_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,68] 6 18 profile25_node281_cert).mp (by decide +kernel))

def profile25_node282_cert : Bound 7 := { allowed := (rows 16 64 82 2 0 0 0), upper := (rows 67 19 37 88 22 38 64), lower := (rows 67 19 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 127), good := (rows 74 90 100 88 88 96 64) }] }

theorem profile25_node282 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,80] 6 6 profile25_node282_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33,80] 6 6 profile25_node282_cert).mp (by decide +kernel))

def profile25_node276_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node276_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node276 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,33] 6 (by decide) (choices 2) [6,18,20,66,68,80] profile25_node276_route profile25_node276_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node277
  · exact profile25_node278
  · exact profile25_node279
  · exact profile25_node280
  · exact profile25_node281
  · exact profile25_node282

def profile25_node284_cert : CutBound 7 := { lost := (rows 16 0 1 16 0 0 0), upper := (rows 67 19 38 13 80 112 64), lower := (rows 67 19 38 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 127 127 127), good := (rows 118 118 118 124 112 112 112) },{ target := 4, region := (rows 7 2 4 12 0 32 127), good := (rows 67 67 111 77 64 96 64) }] }

theorem profile25_node284 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,5] 6 80 profile25_node284_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,5] 6 80 profile25_node284_cert).mp (by decide +kernel))

def profile25_node285_cert : Bound 7 := { allowed := (rows 16 64 80 66 0 0 0), upper := (rows 67 19 38 25 84 100 64), lower := (rows 67 19 38 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 31 47 127), good := (rows 118 118 118 124 80 96 64) }] }

theorem profile25_node285 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,17] 6 68 profile25_node285_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,17] 6 68 profile25_node285_cert).mp (by decide +kernel))

def profile25_node286_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 67 19 38 28 81 97 64), lower := (rows 67 19 38 28 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 12 19 35 127), good := (rows 113 113 124 92 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 47 127), good := (rows 103 103 103 109 64 96 64) }] }

theorem profile25_node286 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,20] 6 65 profile25_node286_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,20] 6 65 profile25_node286_cert).mp (by decide +kernel))

def profile25_node287_cert : Bound 7 := { allowed := (rows 16 64 80 18 0 0 0), upper := (rows 67 19 38 73 20 52 64), lower := (rows 67 19 38 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 31 47 127), good := (rows 118 118 118 124 80 96 64) }] }

theorem profile25_node287 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,65] 6 20 profile25_node287_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,65] 6 20 profile25_node287_cert).mp (by decide +kernel))

def profile25_node288_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 67 19 38 76 17 49 64), lower := (rows 67 19 38 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 66 82 110 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 19 35 127), good := (rows 113 113 124 76 80 96 64) }] }

theorem profile25_node288 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,68] 6 17 profile25_node288_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,68] 6 17 profile25_node288_cert).mp (by decide +kernel))

def profile25_node289_cert : Bound 7 := { allowed := (rows 16 64 81 2 0 0 0), upper := (rows 67 19 38 88 21 37 64), lower := (rows 67 19 38 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 127), good := (rows 74 90 110 88 88 96 64) }] }

theorem profile25_node289 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,80] 6 5 profile25_node289_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34,80] 6 5 profile25_node289_cert).mp (by decide +kernel))

def profile25_node283_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node283_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node283 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,34] 6 (by decide) (choices 2) [5,17,20,65,68,80] profile25_node283_route profile25_node283_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node284
  · exact profile25_node285
  · exact profile25_node286
  · exact profile25_node287
  · exact profile25_node288
  · exact profile25_node289

def profile25_node291_cert : Bound 7 := { allowed := (rows 16 64 66 80 0 0 0), upper := (rows 67 19 52 11 84 100 64), lower := (rows 67 19 52 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 127 8 127 127 127), good := (rows 118 118 116 126 116 116 116) }] }

theorem profile25_node291 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,3] 6 68 profile25_node291_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,3] 6 68 profile25_node291_cert).mp (by decide +kernel))

def profile25_node292_cert : CutBound 7 := { lost := (rows 16 0 1 0 0 0 0), upper := (rows 67 19 52 13 82 98 64), lower := (rows 67 19 52 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 19 35 127), good := (rows 118 118 116 124 80 96 64) },{ target := 4, region := (rows 3 2 4 8 0 35 127), good := (rows 99 99 100 109 64 96 64) }] }

theorem profile25_node292 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,5] 6 66 profile25_node292_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,5] 6 66 profile25_node292_cert).mp (by decide +kernel))

def profile25_node293_cert : CutBound 7 := { lost := (rows 16 0 2 0 0 0 0), upper := (rows 67 19 52 14 81 97 64), lower := (rows 67 19 52 14 16 32 64), losses := [{ target := 1, region := (rows 1 0 15 8 19 35 127), good := (rows 117 117 116 124 80 96 64) },{ target := 4, region := (rows 11 2 4 8 0 43 127), good := (rows 99 99 100 111 64 96 64) }] }

theorem profile25_node293 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,6] 6 65 profile25_node293_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,6] 6 65 profile25_node293_cert).mp (by decide +kernel))

def profile25_node294_cert : Bound 7 := { allowed := (rows 16 64 66 18 0 0 0), upper := (rows 67 19 52 73 22 38 64), lower := (rows 67 19 52 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 19 35 127), good := (rows 118 118 116 124 80 96 64) }] }

theorem profile25_node294 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,65] 6 6 profile25_node294_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,65] 6 6 profile25_node294_cert).mp (by decide +kernel))

def profile25_node295_cert : Bound 7 := { allowed := (rows 16 64 67 16 0 0 0), upper := (rows 67 19 52 74 21 37 64), lower := (rows 67 19 52 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 16 32 127), good := (rows 74 90 116 74 80 96 64) }] }

theorem profile25_node295 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,66] 6 5 profile25_node295_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,66] 6 5 profile25_node295_cert).mp (by decide +kernel))

def profile25_node296_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 67 19 52 76 19 35 64), lower := (rows 67 19 52 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 66 82 124 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 65 81 124 76 80 96 64) }] }

theorem profile25_node296 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,68] 6 3 profile25_node296_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48,68] 6 3 profile25_node296_cert).mp (by decide +kernel))

def profile25_node290_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node290_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node290 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,48] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile25_node290_route profile25_node290_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node291
  · exact profile25_node292
  · exact profile25_node293
  · exact profile25_node294
  · exact profile25_node295
  · exact profile25_node296

def profile25_node297_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 67 19 69 62 54 54 64), lower := (rows 67 19 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 7 8 16 32 127), good := (rows 69 85 69 72 80 96 64) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 71 69 72 64 96 64) }] }

theorem profile25_node297 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,65] 6 54 profile25_node297_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,65] 6 54 profile25_node297_cert).mp (by decide +kernel))

def profile25_node298_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 67 19 70 61 53 53 64), lower := (rows 67 19 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 86 70 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile25_node298 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,66] 6 53 profile25_node298_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,66] 6 53 profile25_node298_cert).mp (by decide +kernel))

def profile25_node299_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 67 19 84 47 55 39 64), lower := (rows 67 19 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 86 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 69 85 84 72 84 96 64) }] }

theorem profile25_node299 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,80] 6 39 profile25_node299_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,80] 6 39 profile25_node299_cert).mp (by decide +kernel))

def profile25_node300_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 67 19 100 31 23 55 64), lower := (rows 67 19 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 66 82 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 65 81 100 72 80 100 64) }] }

theorem profile25_node300 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,96] 6 23 profile25_node300_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17,96] 6 23 profile25_node300_cert).mp (by decide +kernel))

def profile25_node272_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node272_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node272 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,17] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node272_route profile25_node272_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node273
  · exact profile25_node274
  · exact profile25_node275
  · exact profile25_node276
  · exact profile25_node283
  · exact profile25_node290
  · exact profile25_node297
  · exact profile25_node298
  · exact profile25_node299
  · exact profile25_node300

def profile25_node302_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 67 22 7 121 113 113 64), lower := (rows 67 22 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 121 124 125 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 71 71 72 64 96 64) }] }

theorem profile25_node302 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,3] 6 113 profile25_node302_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,3] 6 113 profile25_node302_cert).mp (by decide +kernel))

def profile25_node303_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 67 22 21 107 115 99 64), lower := (rows 67 22 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 66 86 86 72 80 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 111 109 72 64 96 64) }] }

theorem profile25_node303 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,17] 6 99 profile25_node303_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,17] 6 99 profile25_node303_cert).mp (by decide +kernel))

def profile25_node304_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 67 22 22 105 113 97 64), lower := (rows 67 22 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 70 86 86 72 86 96 64) }] }

theorem profile25_node304 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,18] 6 97 profile25_node304_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,18] 6 97 profile25_node304_cert).mp (by decide +kernel))

def profile25_node306_cert : CutBound 7 := { lost := (rows 0 1 2 0 0 0 0), upper := (rows 67 22 37 11 80 112 64), lower := (rows 67 22 37 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 122 112 112 112) },{ target := 1, region := (rows 1 0 13 8 127 127 127), good := (rows 117 116 117 125 112 112 112) }] }

theorem profile25_node306 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,3] 6 80 profile25_node306_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,3] 6 80 profile25_node306_cert).mp (by decide +kernel))

def profile25_node307_cert : CutBound 7 := { lost := (rows 16 1 16 0 0 0 0), upper := (rows 67 22 37 25 82 98 64), lower := (rows 67 22 37 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 23 39 127), good := (rows 114 118 118 120 80 96 64) },{ target := 4, region := (rows 3 2 15 8 0 35 127), good := (rows 103 103 101 109 64 96 64) }] }

theorem profile25_node307 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,17] 6 66 profile25_node307_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,17] 6 66 profile25_node307_cert).mp (by decide +kernel))

def profile25_node308_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 67 22 37 26 81 97 64), lower := (rows 67 22 37 26 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 74 94 100 90 80 96 64) },{ target := 1, region := (rows 1 0 5 8 21 37 127), good := (rows 117 116 117 88 80 96 64) }] }

theorem profile25_node308 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,18] 6 65 profile25_node308_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,18] 6 65 profile25_node308_cert).mp (by decide +kernel))

def profile25_node309_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 67 22 37 73 18 50 64), lower := (rows 67 22 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 23 39 127), good := (rows 114 118 118 120 80 96 64) },{ target := 1, region := (rows 1 0 4 13 16 32 127), good := (rows 73 92 109 73 80 96 64) }] }

theorem profile25_node309 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,65] 6 18 profile25_node309_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,65] 6 18 profile25_node309_cert).mp (by decide +kernel))

def profile25_node310_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 67 22 37 74 17 49 64), lower := (rows 67 22 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 16 32 127), good := (rows 74 94 108 74 80 96 64) },{ target := 1, region := (rows 1 0 5 8 21 37 127), good := (rows 117 116 117 72 80 96 64) }] }

theorem profile25_node310 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,66] 6 17 profile25_node310_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,66] 6 17 profile25_node310_cert).mp (by decide +kernel))

def profile25_node311_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 67 22 37 88 19 35 64), lower := (rows 67 22 37 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 26 16 32 127), good := (rows 74 94 100 88 88 96 64) },{ target := 1, region := (rows 1 0 4 26 16 32 127), good := (rows 73 92 101 88 88 96 64) }] }

theorem profile25_node311 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,80] 6 3 profile25_node311_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33,80] 6 3 profile25_node311_cert).mp (by decide +kernel))

def profile25_node305_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node305_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node305 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node305_route profile25_node305_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node306
  · exact profile25_node307
  · exact profile25_node308
  · exact profile25_node309
  · exact profile25_node310
  · exact profile25_node311

def profile25_node312_cert : CutBound 7 := { lost := (rows 16 0 0 2 0 0 0), upper := (rows 67 22 38 89 81 113 64), lower := (rows 67 22 38 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 84 100 72 80 96 64) },{ target := 4, region := (rows 7 2 4 8 0 32 127), good := (rows 67 71 103 72 64 96 64) }] }

theorem profile25_node312 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,34] 6 81 profile25_node312_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,34] 6 81 profile25_node312_cert).mp (by decide +kernel))

def profile25_node313_cert : CutBound 7 := { lost := (rows 16 1 0 16 0 0 0), upper := (rows 67 22 52 75 83 99 64), lower := (rows 67 22 52 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 66 86 118 72 80 96 64) },{ target := 4, region := (rows 3 2 4 11 0 35 127), good := (rows 107 111 100 72 64 96 64) }] }

theorem profile25_node313 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,48] 6 67 profile25_node313_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,48] 6 67 profile25_node313_cert).mp (by decide +kernel))

def profile25_node314_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 67 22 69 59 51 51 64), lower := (rows 67 22 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 69 84 69 72 80 96 64) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 71 69 72 64 96 64) }] }

theorem profile25_node314 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,65] 6 51 profile25_node314_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,65] 6 51 profile25_node314_cert).mp (by decide +kernel))

def profile25_node315_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 67 22 70 57 49 49 64), lower := (rows 67 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 23 8 16 32 127), good := (rows 70 86 70 72 86 96 64) }] }

theorem profile25_node315 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,66] 6 49 profile25_node315_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,66] 6 49 profile25_node315_cert).mp (by decide +kernel))

def profile25_node316_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 67 22 84 43 51 35 64), lower := (rows 67 22 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 22 22 8 16 32 127), good := (rows 70 86 86 72 86 96 64) }] }

theorem profile25_node316 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,80] 6 35 profile25_node316_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,80] 6 35 profile25_node316_cert).mp (by decide +kernel))

def profile25_node317_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 67 22 100 27 19 51 64), lower := (rows 67 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 66 86 100 72 80 100 64) },{ target := 1, region := (rows 1 0 36 8 16 32 127), good := (rows 65 84 100 72 80 100 64) }] }

theorem profile25_node317 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,96] 6 19 profile25_node317_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20,96] 6 19 profile25_node317_cert).mp (by decide +kernel))

def profile25_node301_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node301_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node301 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,20] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node301_route profile25_node301_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node302
  · exact profile25_node303
  · exact profile25_node304
  · exact profile25_node305
  · exact profile25_node312
  · exact profile25_node313
  · exact profile25_node314
  · exact profile25_node315
  · exact profile25_node316
  · exact profile25_node317

def profile25_node318_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 67 35 87 95 87 119 64), lower := (rows 67 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 35 34 4 8 0 32 127), good := (rows 67 99 68 72 64 99 64) }] }

theorem profile25_node318 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,33] 6 87 profile25_node318_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,33] 6 87 profile25_node318_cert).mp (by decide +kernel))

def profile25_node320_cert : CutBound 7 := { lost := (rows 16 16 16 2 0 0 0), upper := (rows 67 38 7 89 81 113 64), lower := (rows 67 38 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 13 21 37 127), good := (rows 121 124 125 72 80 96 64) },{ target := 4, region := (rows 39 34 39 8 0 32 127), good := (rows 71 103 71 72 64 103 64) }] }

theorem profile25_node320 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,3] 6 81 profile25_node320_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,3] 6 81 profile25_node320_cert).mp (by decide +kernel))

def profile25_node322_cert : CutBound 7 := { lost := (rows 0 1 2 0 0 0 0), upper := (rows 67 38 21 11 80 112 64), lower := (rows 67 38 21 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 114 118 118 122 112 112 112) },{ target := 1, region := (rows 1 0 13 8 127 127 127), good := (rows 117 116 117 125 112 112 112) }] }

theorem profile25_node322 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,3] 6 80 profile25_node322_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,3] 6 80 profile25_node322_cert).mp (by decide +kernel))

def profile25_node323_cert : CutBound 7 := { lost := (rows 0 1 2 2 0 0 0), upper := (rows 67 38 21 25 82 98 64), lower := (rows 67 38 21 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 23 39 127), good := (rows 114 118 118 120 80 96 64) },{ target := 1, region := (rows 1 0 12 12 16 32 127), good := (rows 65 108 93 93 80 96 64) }] }

theorem profile25_node323 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,17] 6 66 profile25_node323_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,17] 6 66 profile25_node323_cert).mp (by decide +kernel))

def profile25_node324_cert : CutBound 7 := { lost := (rows 16 16 2 0 0 0 0), upper := (rows 67 38 21 26 81 97 64), lower := (rows 67 38 21 26 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 21 37 127), good := (rows 117 116 117 88 80 96 64) },{ target := 4, region := (rows 15 6 4 8 0 47 127), good := (rows 99 103 103 107 64 96 64) }] }

theorem profile25_node324 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,18] 6 65 profile25_node324_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,18] 6 65 profile25_node324_cert).mp (by decide +kernel))

def profile25_node325_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 67 38 21 73 18 50 64), lower := (rows 67 38 21 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 23 39 127), good := (rows 114 118 118 120 80 96 64) },{ target := 1, region := (rows 1 0 4 13 16 32 127), good := (rows 73 108 93 73 80 96 64) }] }

theorem profile25_node325 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,65] 6 18 profile25_node325_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,65] 6 18 profile25_node325_cert).mp (by decide +kernel))

def profile25_node326_cert : CutBound 7 := { lost := (rows 0 0 2 1 0 0 0), upper := (rows 67 38 21 74 17 49 64), lower := (rows 67 38 21 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 16 32 127), good := (rows 74 110 92 74 80 96 64) },{ target := 1, region := (rows 1 0 5 8 21 37 127), good := (rows 117 116 117 72 80 96 64) }] }

theorem profile25_node326 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,66] 6 17 profile25_node326_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,66] 6 17 profile25_node326_cert).mp (by decide +kernel))

def profile25_node327_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 67 38 21 88 19 35 64), lower := (rows 67 38 21 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 28 16 32 127), good := (rows 66 110 92 88 88 96 64) },{ target := 1, region := (rows 1 0 4 28 16 32 127), good := (rows 65 108 93 88 88 96 64) }] }

theorem profile25_node327 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,80] 6 3 profile25_node327_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17,80] 6 3 profile25_node327_cert).mp (by decide +kernel))

def profile25_node321_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node321_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node321 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,17] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node321_route profile25_node321_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node322
  · exact profile25_node323
  · exact profile25_node324
  · exact profile25_node325
  · exact profile25_node326
  · exact profile25_node327

def profile25_node328_cert : CutBound 7 := { lost := (rows 16 0 0 2 0 0 0), upper := (rows 67 38 22 89 81 113 64), lower := (rows 67 38 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 9 17 33 127), good := (rows 121 100 84 72 80 96 64) },{ target := 4, region := (rows 7 2 4 8 0 32 127), good := (rows 67 103 71 72 64 96 64) }] }

theorem profile25_node328 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,18] 6 81 profile25_node328_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,18] 6 81 profile25_node328_cert).mp (by decide +kernel))

def profile25_node329_cert : CutBound 7 := { lost := (rows 16 16 18 0 0 0 0), upper := (rows 67 38 69 27 19 51 64), lower := (rows 67 38 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 69 100 69 72 80 96 64) },{ target := 4, region := (rows 35 34 39 8 0 32 127), good := (rows 71 103 69 72 64 103 64) }] }

theorem profile25_node329 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,65] 6 19 profile25_node329_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,65] 6 19 profile25_node329_cert).mp (by decide +kernel))

def profile25_node330_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 67 38 70 25 17 49 64), lower := (rows 67 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 39 8 16 32 127), good := (rows 70 102 70 72 80 102 64) }] }

theorem profile25_node330 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,66] 6 17 profile25_node330_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,66] 6 17 profile25_node330_cert).mp (by decide +kernel))

def profile25_node331_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 67 38 84 27 19 51 64), lower := (rows 67 38 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 127), good := (rows 66 102 84 72 84 96 64) },{ target := 1, region := (rows 1 0 20 8 16 32 127), good := (rows 65 100 84 72 84 96 64) }] }

theorem profile25_node331 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,80] 6 19 profile25_node331_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36,80] 6 19 profile25_node331_cert).mp (by decide +kernel))

def profile25_node319_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node319_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node319 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,36] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node319_route profile25_node319_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node320
  · exact profile25_node321
  · exact profile25_node328
  · exact profile25_node329
  · exact profile25_node330
  · exact profile25_node331

def profile25_node333_cert : CutBound 7 := { lost := (rows 16 0 16 2 0 0 0), upper := (rows 67 50 7 93 85 117 64), lower := (rows 67 50 7 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 12 20 36 127), good := (rows 65 112 125 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 103 71 72 64 96 64) }] }

theorem profile25_node333 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,3] 6 85 profile25_node333_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,3] 6 85 profile25_node333_cert).mp (by decide +kernel))

def profile25_node335_cert : Bound 7 := { allowed := (rows 16 64 66 80 0 0 0), upper := (rows 67 50 21 11 84 100 64), lower := (rows 67 50 21 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 20 36 127), good := (rows 66 114 118 74 80 96 64) }] }

theorem profile25_node335 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,3] 6 68 profile25_node335_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,3] 6 68 profile25_node335_cert).mp (by decide +kernel))

def profile25_node336_cert : CutBound 7 := { lost := (rows 0 1 0 2 0 0 0), upper := (rows 67 50 21 13 82 98 64), lower := (rows 67 50 21 13 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 126 114 114 114) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 65 112 93 77 80 96 64) }] }

theorem profile25_node336 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,5] 6 66 profile25_node336_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,5] 6 66 profile25_node336_cert).mp (by decide +kernel))

def profile25_node337_cert : CutBound 7 := { lost := (rows 16 0 2 0 0 0 0), upper := (rows 67 50 21 14 81 97 64), lower := (rows 67 50 21 14 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 21 37 127), good := (rows 117 112 117 124 80 96 64) },{ target := 4, region := (rows 11 2 4 8 0 47 127), good := (rows 99 99 101 111 64 96 64) }] }

theorem profile25_node337 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,6] 6 65 profile25_node337_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,6] 6 65 profile25_node337_cert).mp (by decide +kernel))

def profile25_node338_cert : Bound 7 := { allowed := (rows 16 64 66 18 0 0 0), upper := (rows 67 50 21 73 22 38 64), lower := (rows 67 50 21 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 20 36 127), good := (rows 66 114 118 72 80 96 64) }] }

theorem profile25_node338 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,65] 6 6 profile25_node338_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,65] 6 6 profile25_node338_cert).mp (by decide +kernel))

def profile25_node339_cert : Bound 7 := { allowed := (rows 16 65 66 16 0 0 0), upper := (rows 67 50 21 74 21 37 64), lower := (rows 67 50 21 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 11 16 32 127), good := (rows 74 122 92 74 80 96 64) }] }

theorem profile25_node339 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,66] 6 5 profile25_node339_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,66] 6 5 profile25_node339_cert).mp (by decide +kernel))

def profile25_node340_cert : CutBound 7 := { lost := (rows 0 0 0 3 0 0 0), upper := (rows 67 50 21 76 19 35 64), lower := (rows 67 50 21 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 66 114 92 76 80 96 64) },{ target := 1, region := (rows 1 0 4 12 16 32 127), good := (rows 65 112 93 76 80 96 64) }] }

theorem profile25_node340 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,68] 6 3 profile25_node340_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17,68] 6 3 profile25_node340_cert).mp (by decide +kernel))

def profile25_node334_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node334_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node334 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,17] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile25_node334_route profile25_node334_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node335
  · exact profile25_node336
  · exact profile25_node337
  · exact profile25_node338
  · exact profile25_node339
  · exact profile25_node340

def profile25_node341_cert : CutBound 7 := { lost := (rows 16 0 1 16 0 0 0), upper := (rows 67 50 22 77 85 101 64), lower := (rows 67 50 22 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 70 118 86 72 80 96 64) },{ target := 4, region := (rows 7 2 4 12 0 36 127), good := (rows 67 99 111 72 64 96 64) }] }

theorem profile25_node341 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,18] 6 69 profile25_node341_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,18] 6 69 profile25_node341_cert).mp (by decide +kernel))

def profile25_node342_cert : CutBound 7 := { lost := (rows 16 0 18 0 0 0 0), upper := (rows 67 50 69 31 23 55 64), lower := (rows 67 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 5 8 16 32 127), good := (rows 69 112 69 72 80 96 64) },{ target := 4, region := (rows 3 2 7 8 0 32 127), good := (rows 71 103 69 72 64 96 64) }] }

theorem profile25_node342 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,65] 6 23 profile25_node342_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,65] 6 23 profile25_node342_cert).mp (by decide +kernel))

def profile25_node343_cert : CutBound 7 := { lost := (rows 16 0 17 0 0 0 0), upper := (rows 67 50 70 29 21 53 64), lower := (rows 67 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 7 8 16 32 127), good := (rows 70 118 70 72 80 96 64) },{ target := 4, region := (rows 7 2 7 8 0 32 127), good := (rows 71 103 71 72 64 96 64) }] }

theorem profile25_node343 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,66] 6 21 profile25_node343_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,66] 6 21 profile25_node343_cert).mp (by decide +kernel))

def profile25_node344_cert : CutBound 7 := { lost := (rows 0 0 3 0 0 0 0), upper := (rows 67 50 84 15 23 39 64), lower := (rows 67 50 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 127), good := (rows 70 118 84 72 84 96 64) },{ target := 1, region := (rows 1 0 22 8 16 32 127), good := (rows 69 116 84 72 84 96 64) }] }

theorem profile25_node344 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,80] 6 7 profile25_node344_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48,80] 6 7 profile25_node344_cert).mp (by decide +kernel))

def profile25_node332_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node332_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node332 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,48] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node332_route profile25_node332_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node333
  · exact profile25_node334
  · exact profile25_node341
  · exact profile25_node342
  · exact profile25_node343
  · exact profile25_node344

def profile25_node345_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 67 67 55 63 55 55 64), lower := (rows 67 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 127 127 4 8 0 32 127), good := (rows 67 67 71 75 67 99 67) }] }

theorem profile25_node345 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,65] 6 55 profile25_node345_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,65] 6 55 profile25_node345_cert).mp (by decide +kernel))

def profile25_node346_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 67 70 55 59 51 51 64), lower := (rows 67 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 66 70 70 72 80 96 64) },{ target := 4, region := (rows 7 6 4 8 0 32 127), good := (rows 67 71 71 72 64 96 64) }] }

theorem profile25_node346 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,68] 6 51 profile25_node346_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,68] 6 51 profile25_node346_cert).mp (by decide +kernel))

def profile25_node347_cert : CutBound 7 := { lost := (rows 16 1 0 0 0 0 0), upper := (rows 67 82 55 63 55 55 64), lower := (rows 67 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 127), good := (rows 66 82 68 72 82 96 64) },{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile25_node347 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,80] 6 55 profile25_node347_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,80] 6 55 profile25_node347_cert).mp (by decide +kernel))

def profile25_node348_cert : CutBound 7 := { lost := (rows 16 17 0 0 0 0 0), upper := (rows 67 98 23 31 23 55 64), lower := (rows 67 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 66 98 68 72 80 98 64) },{ target := 4, region := (rows 35 34 4 8 0 32 127), good := (rows 67 99 68 72 64 99 64) }] }

theorem profile25_node348 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,96] 6 23 profile25_node348_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66,96] 6 23 profile25_node348_cert).mp (by decide +kernel))

def profile25_node270_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node270_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node270 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [66] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile25_node270_route profile25_node270_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node271
  · exact profile25_node272
  · exact profile25_node301
  · exact profile25_node318
  · exact profile25_node319
  · exact profile25_node332
  · exact profile25_node345
  · exact profile25_node346
  · exact profile25_node347
  · exact profile25_node348

def profile25_node349_cert : CutBound 7 := { lost := (rows 18 0 0 0 0 0 0), upper := (rows 69 115 119 123 115 115 64), lower := (rows 69 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 16 32 127), good := (rows 69 64 69 72 80 96 64) },{ target := 4, region := (rows 5 2 4 8 0 32 127), good := (rows 69 66 69 72 64 96 64) }] }

theorem profile25_node349 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [68] 6 115 profile25_node349_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [68] 6 115 profile25_node349_cert).mp (by decide +kernel))

def profile25_node352_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 7 7 122 114 114 64), lower := (rows 81 7 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 22 38 127), good := (rows 80 126 126 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 69 69 72 81 96 64) }] }

theorem profile25_node352 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,3] 6 114 profile25_node352_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,3] 6 114 profile25_node352_cert).mp (by decide +kernel))

def profile25_node353_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 81 7 21 106 114 98 64), lower := (rows 81 7 21 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 84 72 80 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 69 85 72 85 96 64) }] }

theorem profile25_node353 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,17] 6 98 profile25_node353_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,17] 6 98 profile25_node353_cert).mp (by decide +kernel))

def profile25_node354_cert : CutBound 7 := { lost := (rows 2 0 0 16 0 0 0), upper := (rows 81 7 22 107 115 99 64), lower := (rows 81 7 22 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 4 8 16 32 127), good := (rows 81 69 85 72 81 96 64) },{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 110 72 64 96 64) }] }

theorem profile25_node354 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,18] 6 99 profile25_node354_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,18] 6 99 profile25_node354_cert).mp (by decide +kernel))

def profile25_node355_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 7 37 90 82 114 64), lower := (rows 81 7 37 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 100 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 69 101 72 81 96 64) }] }

theorem profile25_node355 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,33] 6 82 profile25_node355_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,33] 6 82 profile25_node355_cert).mp (by decide +kernel))

def profile25_node357_cert : CutBound 7 := { lost := (rows 2 0 1 0 0 0 0), upper := (rows 81 7 38 11 80 112 64), lower := (rows 81 7 38 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 8 127 127 127), good := (rows 112 118 118 126 112 112 112) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) }] }

theorem profile25_node357 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,3] 6 80 profile25_node357_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,3] 6 80 profile25_node357_cert).mp (by decide +kernel))

def profile25_node358_cert : CutBound 7 := { lost := (rows 2 0 1 2 0 0 0), upper := (rows 81 7 38 25 82 98 64), lower := (rows 81 7 38 25 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 80 118 118 88 80 96 64) },{ target := 1, region := (rows 25 0 4 25 16 32 127), good := (rows 89 77 100 89 89 96 64) }] }

theorem profile25_node358 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,17] 6 66 profile25_node358_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,17] 6 66 profile25_node358_cert).mp (by decide +kernel))

def profile25_node359_cert : CutBound 7 := { lost := (rows 2 16 16 0 0 0 0), upper := (rows 81 7 38 26 81 97 64), lower := (rows 81 7 38 26 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) },{ target := 4, region := (rows 1 3 15 8 0 35 127), good := (rows 103 103 102 110 64 96 64) }] }

theorem profile25_node359 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,18] 6 65 profile25_node359_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,18] 6 65 profile25_node359_cert).mp (by decide +kernel))

def profile25_node360_cert : CutBound 7 := { lost := (rows 2 0 1 2 0 0 0), upper := (rows 81 7 38 73 18 50 64), lower := (rows 81 7 38 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 80 118 118 72 80 96 64) },{ target := 1, region := (rows 17 0 4 27 16 32 127), good := (rows 89 77 108 73 89 96 64) }] }

theorem profile25_node360 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,65] 6 18 profile25_node360_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,65] 6 18 profile25_node360_cert).mp (by decide +kernel))

def profile25_node361_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 7 38 74 17 49 64), lower := (rows 81 7 38 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 80 78 110 74 80 96 64) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) }] }

theorem profile25_node361 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,66] 6 17 profile25_node361_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,66] 6 17 profile25_node361_cert).mp (by decide +kernel))

def profile25_node362_cert : CutBound 7 := { lost := (rows 2 0 0 3 0 0 0), upper := (rows 81 7 38 88 19 35 64), lower := (rows 81 7 38 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 88 78 102 88 88 96 64) },{ target := 1, region := (rows 25 0 4 25 16 32 127), good := (rows 89 77 100 89 89 96 64) }] }

theorem profile25_node362 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,80] 6 3 profile25_node362_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34,80] 6 3 profile25_node362_cert).mp (by decide +kernel))

def profile25_node356_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node356_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node356 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,34] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node356_route profile25_node356_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node357
  · exact profile25_node358
  · exact profile25_node359
  · exact profile25_node360
  · exact profile25_node361
  · exact profile25_node362

def profile25_node363_cert : CutBound 7 := { lost := (rows 2 0 0 16 0 0 0), upper := (rows 81 7 52 75 83 99 64), lower := (rows 81 7 52 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 4 8 16 32 127), good := (rows 81 69 117 72 81 96 64) },{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 100 72 64 96 64) }] }

theorem profile25_node363 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,48] 6 67 profile25_node363_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,48] 6 67 profile25_node363_cert).mp (by decide +kernel))

def profile25_node364_cert : CutBound 7 := { lost := (rows 2 0 2 1 0 0 0), upper := (rows 81 7 69 58 50 50 64), lower := (rows 81 7 69 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 127), good := (rows 80 126 68 72 80 96 64) },{ target := 1, region := (rows 17 0 23 8 16 32 127), good := (rows 85 69 69 72 85 96 64) }] }

theorem profile25_node364 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,65] 6 50 profile25_node364_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,65] 6 50 profile25_node364_cert).mp (by decide +kernel))

def profile25_node365_cert : CutBound 7 := { lost := (rows 2 0 1 0 0 0 0), upper := (rows 81 7 70 59 51 51 64), lower := (rows 81 7 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 70 70 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 69 68 72 81 96 64) }] }

theorem profile25_node365 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,66] 6 51 profile25_node365_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,66] 6 51 profile25_node365_cert).mp (by decide +kernel))

def profile25_node366_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 81 7 84 43 51 35 64), lower := (rows 81 7 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 70 84 72 84 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 69 85 72 85 96 64) }] }

theorem profile25_node366 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,80] 6 35 profile25_node366_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,80] 6 35 profile25_node366_cert).mp (by decide +kernel))

def profile25_node367_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 81 7 100 27 19 51 64), lower := (rows 81 7 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 80 70 100 72 80 100 64) },{ target := 1, region := (rows 17 0 36 8 16 32 127), good := (rows 81 69 100 72 81 100 64) }] }

theorem profile25_node367 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,96] 6 19 profile25_node367_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5,96] 6 19 profile25_node367_cert).mp (by decide +kernel))

def profile25_node351_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node351_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node351 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,5] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile25_node351_route profile25_node351_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node352
  · exact profile25_node353
  · exact profile25_node354
  · exact profile25_node355
  · exact profile25_node356
  · exact profile25_node363
  · exact profile25_node364
  · exact profile25_node365
  · exact profile25_node366
  · exact profile25_node367

def profile25_node368_cert : CutBound 7 := { lost := (rows 2 0 16 16 0 0 0), upper := (rows 81 19 103 111 119 103 64), lower := (rows 81 19 4 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 81 68 72 81 96 64) },{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 65 111 68 72 64 96 64) }] }

theorem profile25_node368 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,17] 6 103 profile25_node368_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,17] 6 103 profile25_node368_cert).mp (by decide +kernel))

def profile25_node370_cert : CutBound 7 := { lost := (rows 2 0 0 16 0 0 0), upper := (rows 81 22 7 107 115 99 64), lower := (rows 81 22 7 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 85 69 72 81 96 64) },{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 65 110 111 72 64 96 64) }] }

theorem profile25_node370 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,3] 6 99 profile25_node370_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,3] 6 99 profile25_node370_cert).mp (by decide +kernel))

def profile25_node372_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 81 22 37 11 82 98 64), lower := (rows 81 22 37 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 30 46 127), good := (rows 80 118 118 122 80 96 64) },{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 85 101 73 81 96 64) }] }

theorem profile25_node372 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,3] 6 66 profile25_node372_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,3] 6 66 profile25_node372_cert).mp (by decide +kernel))

def profile25_node373_cert : CutBound 7 := { lost := (rows 2 1 0 2 0 0 0), upper := (rows 81 22 37 73 18 34 64), lower := (rows 81 22 37 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 22 38 127), good := (rows 80 118 118 72 80 96 64) },{ target := 1, region := (rows 19 0 4 31 16 32 127), good := (rows 89 93 109 73 89 96 64) }] }

theorem profile25_node373 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,65] 6 2 profile25_node373_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,65] 6 2 profile25_node373_cert).mp (by decide +kernel))

def profile25_node374_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 22 37 74 19 35 64), lower := (rows 81 22 37 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 94 100 74 80 96 64) },{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 85 101 73 81 96 64) }] }

theorem profile25_node374 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,66] 6 3 profile25_node374_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33,66] 6 3 profile25_node374_cert).mp (by decide +kernel))

def profile25_node371_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node371_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node371 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,33] 6 (by decide) (choices 2) [3,65,66] profile25_node371_route profile25_node371_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node372
  · exact profile25_node373
  · exact profile25_node374

def profile25_node376_cert : CutBound 7 := { lost := (rows 2 0 16 0 0 0 0), upper := (rows 81 22 38 11 81 97 64), lower := (rows 81 22 38 11 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) },{ target := 4, region := (rows 1 2 12 8 0 41 127), good := (rows 97 70 102 111 64 96 64) }] }

theorem profile25_node376 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,3] 6 65 profile25_node376_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,3] 6 65 profile25_node376_cert).mp (by decide +kernel))

def profile25_node377_cert : CutBound 7 := { lost := (rows 2 0 0 2 0 0 0), upper := (rows 81 22 38 73 19 35 64), lower := (rows 81 22 38 73 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 31 16 32 127), good := (rows 89 93 109 73 89 96 64) }] }

theorem profile25_node377 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,65] 6 3 profile25_node377_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,65] 6 3 profile25_node377_cert).mp (by decide +kernel))

def profile25_node378_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 22 38 74 17 33 64), lower := (rows 81 22 38 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 80 94 110 74 80 96 64) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) }] }

theorem profile25_node378 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,66] 6 1 profile25_node378_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34,66] 6 1 profile25_node378_cert).mp (by decide +kernel))

def profile25_node375_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node375_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node375 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,34] 6 (by decide) (choices 2) [3,65,66] profile25_node375_route profile25_node375_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node376
  · exact profile25_node377
  · exact profile25_node378

def profile25_node379_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 81 22 69 43 51 35 64), lower := (rows 81 22 69 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 32 127), good := (rows 85 85 69 72 85 96 64) }] }

theorem profile25_node379 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,65] 6 35 profile25_node379_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,65] 6 35 profile25_node379_cert).mp (by decide +kernel))

def profile25_node380_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 22 70 43 51 35 64), lower := (rows 81 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 86 86 70 72 86 96 64) }] }

theorem profile25_node380 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,66] 6 35 profile25_node380_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,66] 6 35 profile25_node380_cert).mp (by decide +kernel))

def profile25_node381_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 81 22 100 11 19 35 64), lower := (rows 81 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 80 86 100 72 80 100 64) },{ target := 1, region := (rows 19 0 36 8 16 32 127), good := (rows 81 85 100 72 81 100 64) }] }

theorem profile25_node381 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,96] 6 3 profile25_node381_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20,96] 6 3 profile25_node381_cert).mp (by decide +kernel))

def profile25_node369_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | _ => 0

def profile25_node369_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node369 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,20] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile25_node369_route profile25_node369_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node370
  · exact profile25_node371
  · exact profile25_node375
  · exact profile25_node379
  · exact profile25_node380
  · exact profile25_node381

def profile25_node383_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 35 7 94 86 118 64), lower := (rows 81 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 80 98 126 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 97 69 72 81 96 64) }] }

theorem profile25_node383 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,3] 6 86 profile25_node383_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,3] 6 86 profile25_node383_cert).mp (by decide +kernel))

def profile25_node384_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 81 35 21 78 86 102 64), lower := (rows 81 35 21 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) }] }

theorem profile25_node384 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,17] 6 70 profile25_node384_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,17] 6 70 profile25_node384_cert).mp (by decide +kernel))

def profile25_node386_cert : Bound 7 := { allowed := (rows 2 80 64 80 0 0 0), upper := (rows 81 35 22 11 84 100 64), lower := (rows 81 35 22 11 16 32 64), losses := [{ target := 0, region := (rows 0 2 14 8 30 46 127), good := (rows 80 118 118 126 80 96 64) }] }

theorem profile25_node386 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,3] 6 68 profile25_node386_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,3] 6 68 profile25_node386_cert).mp (by decide +kernel))

def profile25_node387_cert : CutBound 7 := { lost := (rows 2 0 1 2 0 0 0), upper := (rows 81 35 22 13 82 98 64), lower := (rows 81 35 22 13 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 80 118 118 124 80 96 64) },{ target := 1, region := (rows 21 0 4 12 16 32 127), good := (rows 81 97 93 77 81 96 64) }] }

theorem profile25_node387 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,5] 6 66 profile25_node387_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,5] 6 66 profile25_node387_cert).mp (by decide +kernel))


#print axioms profile25_node387
end Delivery.SmallBudgetTenFinite7
