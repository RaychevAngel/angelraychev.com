import SmallBudgetTenFinite7Profile026Part001

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile26_node258_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile26_node258_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node258 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,3] 6 (by decide) (choices 1) [1,64] profile26_node258_route profile26_node258_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile26_node259
  · exact profile26_node260

def profile26_node261_cert : Bound 7 := { allowed := (rows 0 81 65 16 0 0 0), upper := (rows 81 14 52 73 19 35 64), lower := (rows 81 14 52 73 16 32 64), losses := [] }

theorem profile26_node261 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,65] 6 3 profile26_node261_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,65] 6 3 profile26_node261_cert).mp (by decide +kernel))

def profile26_node262_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 81 14 52 74 17 33 64), lower := (rows 81 14 52 74 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 14 16 32 127), good := (rows 80 78 126 74 80 96 64) }] }

theorem profile26_node262 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,66] 6 1 profile26_node262_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48,66] 6 1 profile26_node262_cert).mp (by decide +kernel))

def profile26_node257_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node257_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node257 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,48] 6 (by decide) (choices 2) [3,65,66] profile26_node257_route profile26_node257_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node258
  · exact profile26_node261
  · exact profile26_node262

def profile26_node263_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 81 14 69 59 51 51 64), lower := (rows 81 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 78 69 72 64 96 64) }] }

theorem profile26_node263 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,65] 6 51 profile26_node263_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,65] 6 51 profile26_node263_cert).mp (by decide +kernel))

def profile26_node264_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 14 70 57 49 49 64), lower := (rows 81 14 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 10 14 8 16 32 127), good := (rows 80 78 70 78 80 96 64) }] }

theorem profile26_node264 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,66] 6 49 profile26_node264_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,66] 6 49 profile26_node264_cert).mp (by decide +kernel))

def profile26_node265_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 14 84 43 51 35 64), lower := (rows 81 14 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 78 84 72 84 96 64) }] }

theorem profile26_node265 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,80] 6 35 profile26_node265_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,80] 6 35 profile26_node265_cert).mp (by decide +kernel))

def profile26_node266_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 14 100 27 19 51 64), lower := (rows 81 14 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 80 78 100 72 80 100 64) }] }

theorem profile26_node266 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,96] 6 19 profile26_node266_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12,96] 6 19 profile26_node266_cert).mp (by decide +kernel))

def profile26_node234_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile26_node234_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node234 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,12] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile26_node234_route profile26_node234_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node235
  · exact profile26_node244
  · exact profile26_node245
  · exact profile26_node246
  · exact profile26_node253
  · exact profile26_node257
  · exact profile26_node263
  · exact profile26_node264
  · exact profile26_node265
  · exact profile26_node266

def profile26_node267_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 19 111 111 127 111 64), lower := (rows 81 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 65 111 68 72 64 96 64) }] }

theorem profile26_node267 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,17] 6 111 profile26_node267_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,17] 6 111 profile26_node267_cert).mp (by decide +kernel))

def profile26_node269_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 22 7 105 121 105 64), lower := (rows 81 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 13 0 37 127), good := (rows 105 110 111 72 64 96 64) }] }

theorem profile26_node269 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,3] 6 105 profile26_node269_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,3] 6 105 profile26_node269_cert).mp (by decide +kernel))

def profile26_node271_cert : Bound 7 := { allowed := (rows 0 65 80 80 0 0 0), upper := (rows 81 22 13 11 112 96 64), lower := (rows 81 22 13 11 16 32 64), losses := [] }

theorem profile26_node271 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,3] 6 96 profile26_node271_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,3] 6 96 profile26_node271_cert).mp (by decide +kernel))

def profile26_node272_cert : Bound 7 := { allowed := (rows 0 65 80 80 0 0 0), upper := (rows 81 22 13 41 82 98 64), lower := (rows 81 22 13 41 16 32 64), losses := [] }

theorem profile26_node272 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,33] 6 66 profile26_node272_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,33] 6 66 profile26_node272_cert).mp (by decide +kernel))

def profile26_node273_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 22 13 42 81 97 64), lower := (rows 81 22 13 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 37 127), good := (rows 97 110 109 106 64 96 64) }] }

theorem profile26_node273 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,34] 6 65 profile26_node273_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,34] 6 65 profile26_node273_cert).mp (by decide +kernel))

def profile26_node274_cert : Bound 7 := { allowed := (rows 0 65 80 16 0 0 0), upper := (rows 81 22 13 73 50 34 64), lower := (rows 81 22 13 73 16 32 64), losses := [] }

theorem profile26_node274 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,65] 6 34 profile26_node274_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,65] 6 34 profile26_node274_cert).mp (by decide +kernel))

def profile26_node275_cert : Bound 7 := { allowed := (rows 0 65 80 17 0 0 0), upper := (rows 81 22 13 74 49 33 64), lower := (rows 81 22 13 74 16 32 64), losses := [] }

theorem profile26_node275 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,66] 6 33 profile26_node275_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,66] 6 33 profile26_node275_cert).mp (by decide +kernel))

def profile26_node276_cert : Bound 7 := { allowed := (rows 0 65 80 17 0 0 0), upper := (rows 81 22 13 104 19 35 64), lower := (rows 81 22 13 104 16 32 64), losses := [] }

theorem profile26_node276 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,96] 6 3 profile26_node276_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9,96] 6 3 profile26_node276_cert).mp (by decide +kernel))

def profile26_node270_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile26_node270_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node270 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,9] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile26_node270_route profile26_node270_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node271
  · exact profile26_node272
  · exact profile26_node273
  · exact profile26_node274
  · exact profile26_node275
  · exact profile26_node276

def profile26_node277_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 22 14 105 113 97 64), lower := (rows 81 22 14 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 78 72 64 96 64) }] }

theorem profile26_node277 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,10] 6 97 profile26_node277_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,10] 6 97 profile26_node277_cert).mp (by decide +kernel))

def profile26_node279_cert : Bound 7 := { allowed := (rows 0 65 80 80 0 0 0), upper := (rows 81 22 37 11 88 104 64), lower := (rows 81 22 37 11 16 32 64), losses := [] }

theorem profile26_node279 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,3] 6 72 profile26_node279_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,3] 6 72 profile26_node279_cert).mp (by decide +kernel))

def profile26_node280_cert : Bound 7 := { allowed := (rows 0 65 80 16 0 0 0), upper := (rows 81 22 37 73 26 42 64), lower := (rows 81 22 37 73 16 32 64), losses := [] }

theorem profile26_node280 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,65] 6 10 profile26_node280_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,65] 6 10 profile26_node280_cert).mp (by decide +kernel))

def profile26_node281_cert : Bound 7 := { allowed := (rows 0 65 80 17 0 0 0), upper := (rows 81 22 37 74 25 41 64), lower := (rows 81 22 37 74 16 32 64), losses := [] }

theorem profile26_node281 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,66] 6 9 profile26_node281_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33,66] 6 9 profile26_node281_cert).mp (by decide +kernel))

def profile26_node278_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node278_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node278 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,33] 6 (by decide) (choices 2) [3,65,66] profile26_node278_route profile26_node278_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node279
  · exact profile26_node280
  · exact profile26_node281

def profile26_node282_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 22 38 73 89 105 64), lower := (rows 81 22 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 102 72 64 96 64) }] }

theorem profile26_node282 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,34] 6 73 profile26_node282_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,34] 6 73 profile26_node282_cert).mp (by decide +kernel))

def profile26_node284_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 81 22 44 11 81 97 64), lower := (rows 81 22 44 11 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 41 127), good := (rows 97 70 108 111 64 96 64) }] }

theorem profile26_node284 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,3] 6 65 profile26_node284_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,3] 6 65 profile26_node284_cert).mp (by decide +kernel))

def profile26_node285_cert : Bound 7 := { allowed := (rows 0 65 81 16 0 0 0), upper := (rows 81 22 44 73 19 35 64), lower := (rows 81 22 44 73 16 32 64), losses := [] }

theorem profile26_node285 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,65] 6 3 profile26_node285_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,65] 6 3 profile26_node285_cert).mp (by decide +kernel))

def profile26_node286_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 22 44 74 17 33 64), lower := (rows 81 22 44 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 94 108 74 80 96 64) }] }

theorem profile26_node286 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,66] 6 1 profile26_node286_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40,66] 6 1 profile26_node286_cert).mp (by decide +kernel))

def profile26_node283_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node283_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node283 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,40] 6 (by decide) (choices 2) [3,65,66] profile26_node283_route profile26_node283_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node284
  · exact profile26_node285
  · exact profile26_node286

def profile26_node287_cert : Bound 7 := { allowed := (rows 0 65 16 81 0 0 0), upper := (rows 81 22 69 43 59 43 64), lower := (rows 81 22 69 8 16 32 64), losses := [] }

theorem profile26_node287 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,65] 6 43 profile26_node287_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,65] 6 43 profile26_node287_cert).mp (by decide +kernel))

def profile26_node288_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 22 70 41 57 41 64), lower := (rows 81 22 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 23 8 16 32 127), good := (rows 86 86 70 72 86 96 64) }] }

theorem profile26_node288 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,66] 6 41 profile26_node288_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,66] 6 41 profile26_node288_cert).mp (by decide +kernel))

def profile26_node289_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 22 76 43 51 35 64), lower := (rows 81 22 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 80 86 76 76 80 96 64) }] }

theorem profile26_node289 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,72] 6 35 profile26_node289_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,72] 6 35 profile26_node289_cert).mp (by decide +kernel))

def profile26_node290_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 22 100 11 27 43 64), lower := (rows 81 22 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 127), good := (rows 80 86 100 72 80 100 64) }] }

theorem profile26_node290 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,96] 6 11 profile26_node290_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20,96] 6 11 profile26_node290_cert).mp (by decide +kernel))

def profile26_node268_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile26_node268_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node268 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,20] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile26_node268_route profile26_node268_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node269
  · exact profile26_node270
  · exact profile26_node277
  · exact profile26_node278
  · exact profile26_node282
  · exact profile26_node283
  · exact profile26_node287
  · exact profile26_node288
  · exact profile26_node289
  · exact profile26_node290

def profile26_node292_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 35 7 92 92 124 64), lower := (rows 81 35 7 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 127), good := (rows 80 98 126 72 80 96 64) }] }

theorem profile26_node292 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,3] 6 92 profile26_node292_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,3] 6 92 profile26_node292_cert).mp (by decide +kernel))

def profile26_node294_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 13 14 80 112 64), lower := (rows 81 35 13 14 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 32 127), good := (rows 65 111 77 78 64 96 64) }] }

theorem profile26_node294 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,6] 6 80 profile26_node294_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,6] 6 80 profile26_node294_cert).mp (by decide +kernel))

def profile26_node295_cert : Bound 7 := { allowed := (rows 0 80 80 65 0 0 0), upper := (rows 81 35 13 26 84 100 64), lower := (rows 81 35 13 26 16 32 64), losses := [] }

theorem profile26_node295 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,18] 6 68 profile26_node295_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,18] 6 68 profile26_node295_cert).mp (by decide +kernel))

def profile26_node296_cert : Bound 7 := { allowed := (rows 0 80 80 65 0 0 0), upper := (rows 81 35 13 28 82 98 64), lower := (rows 81 35 13 28 16 32 64), losses := [] }

theorem profile26_node296 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,20] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,20] 6 66 profile26_node296_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,20] 6 66 profile26_node296_cert).mp (by decide +kernel))

def profile26_node297_cert : Bound 7 := { allowed := (rows 0 80 80 17 0 0 0), upper := (rows 81 35 13 74 20 52 64), lower := (rows 81 35 13 74 16 32 64), losses := [] }

theorem profile26_node297 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,66] 6 20 profile26_node297_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,66] 6 20 profile26_node297_cert).mp (by decide +kernel))

def profile26_node298_cert : Bound 7 := { allowed := (rows 0 80 80 17 0 0 0), upper := (rows 81 35 13 76 18 50 64), lower := (rows 81 35 13 76 16 32 64), losses := [] }

theorem profile26_node298 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,68] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,68] 6 18 profile26_node298_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,68] 6 18 profile26_node298_cert).mp (by decide +kernel))

def profile26_node299_cert : Bound 7 := { allowed := (rows 0 80 80 1 0 0 0), upper := (rows 81 35 13 88 22 38 64), lower := (rows 81 35 13 88 16 32 64), losses := [] }

theorem profile26_node299 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,80] 6 6 profile26_node299_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9,80] 6 6 profile26_node299_cert).mp (by decide +kernel))

def profile26_node293_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node293_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node293 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,9] 6 (by decide) (choices 2) [6,18,20,66,68,80] profile26_node293_route profile26_node293_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node294
  · exact profile26_node295
  · exact profile26_node296
  · exact profile26_node297
  · exact profile26_node298
  · exact profile26_node299

def profile26_node301_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 14 13 80 112 64), lower := (rows 81 35 14 13 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 32 127), good := (rows 65 111 78 77 64 96 64) }] }

theorem profile26_node301 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,5] 6 80 profile26_node301_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,5] 6 80 profile26_node301_cert).mp (by decide +kernel))

def profile26_node302_cert : Bound 7 := { allowed := (rows 0 80 81 64 0 0 0), upper := (rows 81 35 14 25 84 100 64), lower := (rows 81 35 14 25 16 32 64), losses := [] }

theorem profile26_node302 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,17] 6 68 profile26_node302_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,17] 6 68 profile26_node302_cert).mp (by decide +kernel))

def profile26_node303_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 81 35 14 28 81 97 64), lower := (rows 81 35 14 28 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 110 76 64 96 64) }] }

theorem profile26_node303 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,20] 6 65 profile26_node303_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,20] 6 65 profile26_node303_cert).mp (by decide +kernel))

def profile26_node304_cert : Bound 7 := { allowed := (rows 0 80 81 16 0 0 0), upper := (rows 81 35 14 73 20 52 64), lower := (rows 81 35 14 73 16 32 64), losses := [] }

theorem profile26_node304 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,65] 6 20 profile26_node304_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,65] 6 20 profile26_node304_cert).mp (by decide +kernel))

def profile26_node305_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 81 35 14 76 17 49 64), lower := (rows 81 35 14 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 14 16 32 127), good := (rows 80 110 78 76 80 96 64) }] }

theorem profile26_node305 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,68] 6 17 profile26_node305_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,68] 6 17 profile26_node305_cert).mp (by decide +kernel))

def profile26_node306_cert : Bound 7 := { allowed := (rows 0 80 81 1 0 0 0), upper := (rows 81 35 14 88 21 37 64), lower := (rows 81 35 14 88 16 32 64), losses := [] }

theorem profile26_node306 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,80] 6 5 profile26_node306_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10,80] 6 5 profile26_node306_cert).mp (by decide +kernel))

def profile26_node300_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node300_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node300 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,10] 6 (by decide) (choices 2) [5,17,20,65,68,80] profile26_node300_route profile26_node300_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node301
  · exact profile26_node302
  · exact profile26_node303
  · exact profile26_node304
  · exact profile26_node305
  · exact profile26_node306

def profile26_node307_cert : Bound 7 := { allowed := (rows 0 80 64 81 0 0 0), upper := (rows 81 35 21 78 94 110 64), lower := (rows 81 35 21 8 16 32 64), losses := [] }

theorem profile26_node307 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,17] 6 78 profile26_node307_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,17] 6 78 profile26_node307_cert).mp (by decide +kernel))

def profile26_node309_cert : Bound 7 := { allowed := (rows 0 80 65 80 0 0 0), upper := (rows 81 35 22 13 88 104 64), lower := (rows 81 35 22 13 16 32 64), losses := [] }

theorem profile26_node309 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,5] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,5] 6 72 profile26_node309_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,5] 6 72 profile26_node309_cert).mp (by decide +kernel))

def profile26_node310_cert : Bound 7 := { allowed := (rows 0 80 65 16 0 0 0), upper := (rows 81 35 22 73 28 44 64), lower := (rows 81 35 22 73 16 32 64), losses := [] }

theorem profile26_node310 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,65] 6 12 profile26_node310_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,65] 6 12 profile26_node310_cert).mp (by decide +kernel))

def profile26_node311_cert : Bound 7 := { allowed := (rows 0 80 65 17 0 0 0), upper := (rows 81 35 22 76 25 41 64), lower := (rows 81 35 22 76 16 32 64), losses := [] }

theorem profile26_node311 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,68] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,68] 6 9 profile26_node311_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18,68] 6 9 profile26_node311_cert).mp (by decide +kernel))

def profile26_node308_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node308_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node308 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,18] 6 (by decide) (choices 2) [5,65,68] profile26_node308_route profile26_node308_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node309
  · exact profile26_node310
  · exact profile26_node311

def profile26_node313_cert : Bound 7 := { allowed := (rows 0 80 65 80 0 0 0), upper := (rows 81 35 28 11 84 100 64), lower := (rows 81 35 28 11 16 32 64), losses := [] }

theorem profile26_node313 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,3] 6 68 profile26_node313_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,3] 6 68 profile26_node313_cert).mp (by decide +kernel))

def profile26_node314_cert : Bound 7 := { allowed := (rows 0 80 65 80 0 0 0), upper := (rows 81 35 28 13 82 98 64), lower := (rows 81 35 28 13 16 32 64), losses := [] }

theorem profile26_node314 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,5] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,5] 6 66 profile26_node314_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,5] 6 66 profile26_node314_cert).mp (by decide +kernel))

def profile26_node315_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 81 35 28 14 81 97 64), lower := (rows 81 35 28 14 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 76 110 64 96 64) }] }

theorem profile26_node315 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,6] 6 65 profile26_node315_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,6] 6 65 profile26_node315_cert).mp (by decide +kernel))

def profile26_node316_cert : Bound 7 := { allowed := (rows 0 80 65 16 0 0 0), upper := (rows 81 35 28 73 22 38 64), lower := (rows 81 35 28 73 16 32 64), losses := [] }

theorem profile26_node316 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,65] 6 6 profile26_node316_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,65] 6 6 profile26_node316_cert).mp (by decide +kernel))

def profile26_node317_cert : Bound 7 := { allowed := (rows 0 80 65 17 0 0 0), upper := (rows 81 35 28 74 21 37 64), lower := (rows 81 35 28 74 16 32 64), losses := [] }

theorem profile26_node317 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,66] 6 5 profile26_node317_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,66] 6 5 profile26_node317_cert).mp (by decide +kernel))

def profile26_node318_cert : Bound 7 := { allowed := (rows 0 80 65 17 0 0 0), upper := (rows 81 35 28 76 19 35 64), lower := (rows 81 35 28 76 16 32 64), losses := [] }

theorem profile26_node318 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,68] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,68] 6 3 profile26_node318_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24,68] 6 3 profile26_node318_cert).mp (by decide +kernel))

def profile26_node312_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node312_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node312 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,24] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile26_node312_route profile26_node312_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node313
  · exact profile26_node314
  · exact profile26_node315
  · exact profile26_node316
  · exact profile26_node317
  · exact profile26_node318

def profile26_node319_cert : Bound 7 := { allowed := (rows 0 80 16 81 0 0 0), upper := (rows 81 35 69 30 30 62 64), lower := (rows 81 35 69 8 16 32 64), losses := [] }

theorem profile26_node319 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,65] 6 30 profile26_node319_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,65] 6 30 profile26_node319_cert).mp (by decide +kernel))

def profile26_node320_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 35 70 29 29 61 64), lower := (rows 81 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 70 72 80 96 64) }] }

theorem profile26_node320 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,66] 6 29 profile26_node320_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,66] 6 29 profile26_node320_cert).mp (by decide +kernel))

def profile26_node321_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 35 76 31 23 55 64), lower := (rows 81 35 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 80 98 76 76 80 96 64) }] }

theorem profile26_node321 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,72] 6 23 profile26_node321_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,72] 6 23 profile26_node321_cert).mp (by decide +kernel))

def profile26_node322_cert : Bound 7 := { allowed := (rows 0 80 1 81 0 0 0), upper := (rows 81 35 84 15 31 47 64), lower := (rows 81 35 84 8 16 32 64), losses := [] }

theorem profile26_node322 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,80] 6 15 profile26_node322_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33,80] 6 15 profile26_node322_cert).mp (by decide +kernel))

def profile26_node291_column : Nat → Fin 7 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node291_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node291 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,33] 6 (by decide) (choices 2) [3,9,10,17,18,24,65,66,72,80] profile26_node291_route profile26_node291_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node292
  · exact profile26_node293
  · exact profile26_node300
  · exact profile26_node307
  · exact profile26_node308
  · exact profile26_node312
  · exact profile26_node319
  · exact profile26_node320
  · exact profile26_node321
  · exact profile26_node322

def profile26_node325_cert : Bound 7 := { allowed := (rows 0 81 80 64 0 0 0), upper := (rows 81 38 7 25 88 104 64), lower := (rows 81 38 7 25 16 32 64), losses := [] }

theorem profile26_node325 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,17] 6 72 profile26_node325_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,17] 6 72 profile26_node325_cert).mp (by decide +kernel))

def profile26_node326_cert : Bound 7 := { allowed := (rows 0 81 80 16 0 0 0), upper := (rows 81 38 7 73 24 56 64), lower := (rows 81 38 7 73 16 32 64), losses := [] }

theorem profile26_node326 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,65] 6 24 profile26_node326_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,65] 6 24 profile26_node326_cert).mp (by decide +kernel))

def profile26_node327_cert : Bound 7 := { allowed := (rows 0 81 80 1 0 0 0), upper := (rows 81 38 7 88 25 41 64), lower := (rows 81 38 7 88 16 32 64), losses := [] }

theorem profile26_node327 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,80] 6 9 profile26_node327_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3,80] 6 9 profile26_node327_cert).mp (by decide +kernel))

def profile26_node324_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node324_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node324 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,3] 6 (by decide) (choices 2) [17,65,80] profile26_node324_route profile26_node324_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node325
  · exact profile26_node326
  · exact profile26_node327

def profile26_node329_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 81 38 13 11 80 112 64), lower := (rows 81 38 13 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 126 122 112 112 112) }] }

theorem profile26_node329 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,3] 6 80 profile26_node329_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,3] 6 80 profile26_node329_cert).mp (by decide +kernel))

def profile26_node330_cert : Bound 7 := { allowed := (rows 0 81 80 64 0 0 0), upper := (rows 81 38 13 25 82 98 64), lower := (rows 81 38 13 25 16 32 64), losses := [] }

theorem profile26_node330 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,17] 6 66 profile26_node330_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,17] 6 66 profile26_node330_cert).mp (by decide +kernel))

def profile26_node331_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 81 38 13 26 81 97 64), lower := (rows 81 38 13 26 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 37 127), good := (rows 97 102 111 74 64 96 64) }] }

theorem profile26_node331 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,18] 6 65 profile26_node331_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,18] 6 65 profile26_node331_cert).mp (by decide +kernel))

def profile26_node332_cert : Bound 7 := { allowed := (rows 0 81 80 16 0 0 0), upper := (rows 81 38 13 73 18 50 64), lower := (rows 81 38 13 73 16 32 64), losses := [] }

theorem profile26_node332 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,65] 6 18 profile26_node332_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,65] 6 18 profile26_node332_cert).mp (by decide +kernel))

def profile26_node333_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 38 13 74 17 49 64), lower := (rows 81 38 13 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 110 76 74 80 96 64) }] }

theorem profile26_node333 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,66] 6 17 profile26_node333_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,66] 6 17 profile26_node333_cert).mp (by decide +kernel))

def profile26_node334_cert : Bound 7 := { allowed := (rows 0 81 80 1 0 0 0), upper := (rows 81 38 13 88 19 35 64), lower := (rows 81 38 13 88 16 32 64), losses := [] }

theorem profile26_node334 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,80] 6 3 profile26_node334_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9,80] 6 3 profile26_node334_cert).mp (by decide +kernel))

def profile26_node328_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node328_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node328 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,9] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile26_node328_route profile26_node328_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node329
  · exact profile26_node330
  · exact profile26_node331
  · exact profile26_node332
  · exact profile26_node333
  · exact profile26_node334

def profile26_node336_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 38 14 25 81 97 64), lower := (rows 81 38 14 25 16 32 64), losses := [{ target := 4, region := (rows 1 14 12 8 0 41 127), good := (rows 97 102 110 111 64 96 64) }] }

theorem profile26_node336 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,17] 6 65 profile26_node336_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,17] 6 65 profile26_node336_cert).mp (by decide +kernel))

def profile26_node337_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 38 14 73 17 49 64), lower := (rows 81 38 14 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 32 127), good := (rows 73 102 78 73 64 96 64) }] }

theorem profile26_node337 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,65] 6 17 profile26_node337_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,65] 6 17 profile26_node337_cert).mp (by decide +kernel))

def profile26_node338_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 38 14 88 17 33 64), lower := (rows 81 38 14 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 88 102 78 88 88 96 64) }] }

theorem profile26_node338 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,80] 6 1 profile26_node338_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10,80] 6 1 profile26_node338_cert).mp (by decide +kernel))

def profile26_node335_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node335_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node335 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,10] 6 (by decide) (choices 2) [17,65,80] profile26_node335_route profile26_node335_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node336
  · exact profile26_node337
  · exact profile26_node338

def profile26_node339_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 38 21 75 91 107 64), lower := (rows 81 38 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 36 127), good := (rows 65 110 111 72 64 96 64) }] }

theorem profile26_node339 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,17] 6 75 profile26_node339_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,17] 6 75 profile26_node339_cert).mp (by decide +kernel))

def profile26_node340_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 38 22 73 89 105 64), lower := (rows 81 38 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 102 70 72 64 96 64) }] }

theorem profile26_node340 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,18] 6 73 profile26_node340_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,18] 6 73 profile26_node340_cert).mp (by decide +kernel))

def profile26_node342_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 81 38 28 11 81 97 64), lower := (rows 81 38 28 11 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 41 127), good := (rows 97 102 110 107 64 96 64) }] }

theorem profile26_node342 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,3] 6 65 profile26_node342_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,3] 6 65 profile26_node342_cert).mp (by decide +kernel))

def profile26_node343_cert : Bound 7 := { allowed := (rows 0 81 65 16 0 0 0), upper := (rows 81 38 28 73 19 35 64), lower := (rows 81 38 28 73 16 32 64), losses := [] }

theorem profile26_node343 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,65] 6 3 profile26_node343_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,65] 6 3 profile26_node343_cert).mp (by decide +kernel))

def profile26_node344_cert : CutBound 7 := { lost := (rows 0 0 0 1 0 0 0), upper := (rows 81 38 28 74 17 33 64), lower := (rows 81 38 28 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 127), good := (rows 80 110 92 74 80 96 64) }] }

theorem profile26_node344 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,66] 6 1 profile26_node344_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24,66] 6 1 profile26_node344_cert).mp (by decide +kernel))

def profile26_node341_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node341_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node341 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,24] 6 (by decide) (choices 2) [3,65,66] profile26_node341_route profile26_node341_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node342
  · exact profile26_node343
  · exact profile26_node344

def profile26_node345_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 81 38 69 27 27 59 64), lower := (rows 81 38 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 102 69 72 64 96 64) }] }

theorem profile26_node345 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,65] 6 27 profile26_node345_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,65] 6 27 profile26_node345_cert).mp (by decide +kernel))

def profile26_node346_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 38 70 25 25 57 64), lower := (rows 81 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 38 8 16 32 127), good := (rows 80 102 70 72 80 102 64) }] }

theorem profile26_node346 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,66] 6 25 profile26_node346_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,66] 6 25 profile26_node346_cert).mp (by decide +kernel))

def profile26_node347_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 38 76 27 19 51 64), lower := (rows 81 38 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 80 102 76 76 80 96 64) }] }

theorem profile26_node347 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,72] 6 19 profile26_node347_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,72] 6 19 profile26_node347_cert).mp (by decide +kernel))

def profile26_node348_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 38 84 11 27 43 64), lower := (rows 81 38 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) }] }

theorem profile26_node348 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,80] 6 11 profile26_node348_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36,80] 6 11 profile26_node348_cert).mp (by decide +kernel))

def profile26_node323_column : Nat → Fin 7 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile26_node323_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node323 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,36] 6 (by decide) (choices 2) [3,9,10,17,18,24,65,66,72,80] profile26_node323_route profile26_node323_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node324
  · exact profile26_node328
  · exact profile26_node335
  · exact profile26_node339
  · exact profile26_node340
  · exact profile26_node341
  · exact profile26_node345
  · exact profile26_node346
  · exact profile26_node347
  · exact profile26_node348

def profile26_node350_cert : CutBound 7 := { lost := (rows 0 0 0 16 0 0 0), upper := (rows 81 50 7 77 93 109 64), lower := (rows 81 50 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 65 98 111 72 64 96 64) }] }

theorem profile26_node350 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,3] 6 77 profile26_node350_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,3] 6 77 profile26_node350_cert).mp (by decide +kernel))

def profile26_node352_cert : Bound 7 := { allowed := (rows 0 65 80 80 0 0 0), upper := (rows 81 50 13 11 84 100 64), lower := (rows 81 50 13 11 16 32 64), losses := [] }

theorem profile26_node352 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,3] 6 68 profile26_node352_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,3] 6 68 profile26_node352_cert).mp (by decide +kernel))

def profile26_node353_cert : Bound 7 := { allowed := (rows 0 65 80 80 0 0 0), upper := (rows 81 50 13 13 82 98 64), lower := (rows 81 50 13 13 16 32 64), losses := [] }

theorem profile26_node353 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,5] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,5] 6 66 profile26_node353_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,5] 6 66 profile26_node353_cert).mp (by decide +kernel))

def profile26_node355_cert : CutBound 7 := { lost := (rows 0 1 0 1 0 0 0), upper := (rows 81 50 13 14 17 96 64), lower := (rows 81 50 13 14 17 32 64), losses := [{ target := 0, region := (rows 0 19 4 12 16 127 127), good := (rows 114 114 110 110 114 96 96) }] }

theorem profile26_node355 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6,1] 6 64 profile26_node355_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6,1] 6 64 profile26_node355_cert).mp (by decide +kernel))

def profile26_node356_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 81 50 13 14 80 33 64), lower := (rows 81 50 13 14 80 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 127 32 127), good := (rows 80 114 92 94 80 114 80) }] }

theorem profile26_node356 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6,64] 6 1 profile26_node356_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6,64] 6 1 profile26_node356_cert).mp (by decide +kernel))

def profile26_node354_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile26_node354_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node354 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,6] 6 (by decide) (choices 1) [1,64] profile26_node354_route profile26_node354_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile26_node355
  · exact profile26_node356

def profile26_node357_cert : Bound 7 := { allowed := (rows 0 65 80 16 0 0 0), upper := (rows 81 50 13 73 22 38 64), lower := (rows 81 50 13 73 16 32 64), losses := [] }

theorem profile26_node357 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,65] 6 6 profile26_node357_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,65] 6 6 profile26_node357_cert).mp (by decide +kernel))

def profile26_node358_cert : Bound 7 := { allowed := (rows 0 65 80 17 0 0 0), upper := (rows 81 50 13 74 21 37 64), lower := (rows 81 50 13 74 16 32 64), losses := [] }

theorem profile26_node358 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,66] 6 5 profile26_node358_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,66] 6 5 profile26_node358_cert).mp (by decide +kernel))

def profile26_node359_cert : Bound 7 := { allowed := (rows 0 65 80 17 0 0 0), upper := (rows 81 50 13 76 19 35 64), lower := (rows 81 50 13 76 16 32 64), losses := [] }

theorem profile26_node359 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,68] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,68] 6 3 profile26_node359_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9,68] 6 3 profile26_node359_cert).mp (by decide +kernel))

def profile26_node351_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node351_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node351 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,9] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile26_node351_route profile26_node351_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node352
  · exact profile26_node353
  · exact profile26_node354
  · exact profile26_node357
  · exact profile26_node358
  · exact profile26_node359

def profile26_node362_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 50 14 13 17 96 64), lower := (rows 81 50 14 13 17 32 64), losses := [{ target := 0, region := (rows 0 19 12 8 16 127 127), good := (rows 114 114 110 110 114 96 96) }] }

theorem profile26_node362 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5,1] 6 64 profile26_node362_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5,1] 6 64 profile26_node362_cert).mp (by decide +kernel))

def profile26_node363_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 81 50 14 13 80 33 64), lower := (rows 81 50 14 13 80 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 127 32 127), good := (rows 80 114 94 92 80 114 80) }] }

theorem profile26_node363 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5,64] 6 1 profile26_node363_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5,64] 6 1 profile26_node363_cert).mp (by decide +kernel))

def profile26_node361_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile26_node361_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node361 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,5] 6 (by decide) (choices 1) [1,64] profile26_node361_route profile26_node361_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile26_node362
  · exact profile26_node363

def profile26_node364_cert : Bound 7 := { allowed := (rows 0 65 81 16 0 0 0), upper := (rows 81 50 14 73 21 37 64), lower := (rows 81 50 14 73 16 32 64), losses := [] }

theorem profile26_node364 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,65] 6 5 profile26_node364_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,65] 6 5 profile26_node364_cert).mp (by decide +kernel))

def profile26_node365_cert : CutBound 7 := { lost := (rows 0 0 1 1 0 0 0), upper := (rows 81 50 14 76 17 33 64), lower := (rows 81 50 14 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 14 16 32 127), good := (rows 80 126 78 76 80 96 64) }] }

theorem profile26_node365 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,68] 6 1 profile26_node365_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10,68] 6 1 profile26_node365_cert).mp (by decide +kernel))

def profile26_node360_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node360_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node360 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,10] 6 (by decide) (choices 2) [5,65,68] profile26_node360_route profile26_node360_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile26_node361
  · exact profile26_node364
  · exact profile26_node365

def profile26_node366_cert : Bound 7 := { allowed := (rows 0 65 16 81 0 0 0), upper := (rows 81 50 69 15 31 47 64), lower := (rows 81 50 69 8 16 32 64), losses := [] }

theorem profile26_node366 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,65] 6 15 profile26_node366_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,65] 6 15 profile26_node366_cert).mp (by decide +kernel))

def profile26_node367_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 50 70 13 29 45 64), lower := (rows 81 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 70 72 80 96 64) }] }

theorem profile26_node367 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,66] 6 13 profile26_node367_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,66] 6 13 profile26_node367_cert).mp (by decide +kernel))

def profile26_node368_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 81 50 76 15 23 39 64), lower := (rows 81 50 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 127), good := (rows 80 114 76 76 80 96 64) }] }

theorem profile26_node368 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,72] 6 7 profile26_node368_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48,72] 6 7 profile26_node368_cert).mp (by decide +kernel))

def profile26_node349_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile26_node349_route : Route 7 := (fun mask => (mask,id))

theorem profile26_node349 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,48] 6 (by decide) (choices 2) [3,9,10,65,66,72] profile26_node349_route profile26_node349_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node350
  · exact profile26_node351
  · exact profile26_node360
  · exact profile26_node366
  · exact profile26_node367
  · exact profile26_node368

def profile26_node369_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 81 67 63 63 63 63 64), lower := (rows 81 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile26_node369 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,65] 6 63 profile26_node369_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,65] 6 63 profile26_node369_cert).mp (by decide +kernel))

def profile26_node370_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 81 70 63 59 59 59 64), lower := (rows 81 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 80 70 70 72 80 96 64) }] }

theorem profile26_node370 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,68] 6 59 profile26_node370_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,68] 6 59 profile26_node370_cert).mp (by decide +kernel))

def profile26_node371_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 81 82 47 47 63 47 64), lower := (rows 81 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) }] }

theorem profile26_node371 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,80] 6 47 profile26_node371_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,80] 6 47 profile26_node371_cert).mp (by decide +kernel))

def profile26_node372_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 81 98 31 31 31 63 64), lower := (rows 81 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 80 98 68 72 80 98 64) }] }

theorem profile26_node372 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,96] 6 31 profile26_node372_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80,96] 6 31 profile26_node372_cert).mp (by decide +kernel))

def profile26_node200_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile26_node200_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile26_node200 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [80] 6 (by decide) (choices 2) [5,12,17,20,33,36,48,65,68,80,96] profile26_node200_route profile26_node200_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node201
  · exact profile26_node234
  · exact profile26_node267
  · exact profile26_node268
  · exact profile26_node291
  · exact profile26_node323
  · exact profile26_node349
  · exact profile26_node369
  · exact profile26_node370
  · exact profile26_node371
  · exact profile26_node372

def profile26_node373_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 97 95 95 95 95 127 64), lower := (rows 97 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 127), good := (rows 97 66 68 72 64 97 64) }] }

theorem profile26_node373 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [96] 6 95 profile26_node373_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [96] 6 95 profile26_node373_cert).mp (by decide +kernel))

def profile26_node0_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile26_node0_route : Route 7 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 24 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 40 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 72 => (66,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile26_node0 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [] 6 (by decide) (choices 2) [6,18,34,48,66,80,96] profile26_node0_route profile26_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile26_node1
  · exact profile26_node67
  · exact profile26_node119
  · exact profile26_node160
  · exact profile26_node199
  · exact profile26_node200
  · exact profile26_node373

theorem profile26 : Upper (D (n:=7) [34,33,33,33,18,17,2]) (R (n:=7) [34,33,33,33,18,17,2]) [] 6 := profile26_node0


#print axioms profile26
end Delivery.SmallBudgetTenFinite7
