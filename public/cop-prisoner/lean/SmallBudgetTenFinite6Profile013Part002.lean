import SmallBudgetTenFinite6Profile013Part001

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile13_node260_cert : CutBound 6 := { lost := (rows 0 17 16 0 0 0), upper := (rows 21 42 7 41 18 50), lower := (rows 21 42 7 41 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 30 46), good := (rows 52 58 54 58 16 32) },{ target := 4, region := (rows 1 10 12 8 0 32), good := (rows 5 46 7 47 0 32) }] }

theorem profile13_node260 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,33] 6 18 profile13_node260_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,33] 6 18 profile13_node260_cert).mp (by decide +kernel))

def profile13_node261_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 21 42 7 42 17 49), lower := (rows 21 42 7 42 16 32), losses := [{ target := 0, region := (rows 0 42 4 42 16 32), good := (rows 20 42 14 42 16 42) }] }

theorem profile13_node261 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,34] 6 17 profile13_node261_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,34] 6 17 profile13_node261_cert).mp (by decide +kernel))

def profile13_node262_cert : CutBound 6 := { lost := (rows 0 17 0 0 0 0), upper := (rows 21 42 7 56 19 35), lower := (rows 21 42 7 56 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 20 42 6 58 16 32) },{ target := 4, region := (rows 1 10 4 8 0 36), good := (rows 37 42 39 42 0 32) }] }

theorem profile13_node262 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,48] 6 3 profile13_node262_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3,48] 6 3 profile13_node262_cert).mp (by decide +kernel))

def profile13_node256_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node256_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node256 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,3] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node256_route profile13_node256_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node257
  · exact profile13_node258
  · exact profile13_node259
  · exact profile13_node260
  · exact profile13_node261
  · exact profile13_node262

def profile13_node263_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 21 42 21 43 51 35), lower := (rows 21 42 21 8 16 32), losses := [{ target := 1, region := (rows 21 0 21 8 16 32), good := (rows 21 40 21 8 21 32) }] }

theorem profile13_node263 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,17] 6 35 profile13_node263_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,17] 6 35 profile13_node263_cert).mp (by decide +kernel))

def profile13_node264_cert : CutBound 6 := { lost := (rows 2 16 0 16 0 0), upper := (rows 21 42 22 43 51 35), lower := (rows 21 42 22 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 40 21 8 16 32) },{ target := 4, region := (rows 1 3 4 9 0 33), good := (rows 47 42 6 8 0 32) }] }

theorem profile13_node264 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,18] 6 35 profile13_node264_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,18] 6 35 profile13_node264_cert).mp (by decide +kernel))

def profile13_node266_cert : CutBound 6 := { lost := (rows 0 17 0 16 0 0), upper := (rows 21 42 37 11 18 50), lower := (rows 21 42 37 11 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 26 42), good := (rows 20 58 36 58 16 32) },{ target := 4, region := (rows 1 6 4 13 0 32), good := (rows 15 42 47 11 0 32) }] }

theorem profile13_node266 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,3] 6 18 profile13_node266_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,3] 6 18 profile13_node266_cert).mp (by decide +kernel))

def profile13_node267_cert : CutBound 6 := { lost := (rows 0 1 0 2 0 0), upper := (rows 21 42 37 25 18 34), lower := (rows 21 42 37 25 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 26 42), good := (rows 20 58 36 58 16 32) },{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 29 40 45 25 16 32) }] }

theorem profile13_node267 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,17] 6 2 profile13_node267_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,17] 6 2 profile13_node267_cert).mp (by decide +kernel))

def profile13_node268_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 21 42 37 26 19 35), lower := (rows 21 42 37 26 16 32), losses := [{ target := 0, region := (rows 0 6 4 9 16 32), good := (rows 30 42 46 26 16 32) }] }

theorem profile13_node268 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,18] 6 3 profile13_node268_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33,18] 6 3 profile13_node268_cert).mp (by decide +kernel))

def profile13_node265_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 48 => 5 | _ => 0

def profile13_node265_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node265 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,33] 6 (by decide) (choices 2) [3,17,18] profile13_node265_route profile13_node265_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node266
  · exact profile13_node267
  · exact profile13_node268

def profile13_node269_cert : CutBound 6 := { lost := (rows 0 0 17 0 0 0), upper := (rows 21 42 38 27 19 51), lower := (rows 21 42 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 46 38 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 5 46 38 8 0 32) }] }

theorem profile13_node269 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,34] 6 19 profile13_node269_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,34] 6 19 profile13_node269_cert).mp (by decide +kernel))

def profile13_node270_cert : CutBound 6 := { lost := (rows 2 16 0 16 0 0), upper := (rows 21 42 52 11 19 35), lower := (rows 21 42 52 8 16 32), losses := [{ target := 1, region := (rows 5 0 4 8 16 32), good := (rows 21 40 53 8 16 32) },{ target := 4, region := (rows 1 3 4 9 0 33), good := (rows 47 42 36 8 0 32) }] }

theorem profile13_node270 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,48] 6 3 profile13_node270_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40,48] 6 3 profile13_node270_cert).mp (by decide +kernel))

def profile13_node255_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node255_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node255 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,40] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile13_node255_route profile13_node255_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node256
  · exact profile13_node263
  · exact profile13_node264
  · exact profile13_node265
  · exact profile13_node269
  · exact profile13_node270

def profile13_node272_cert : CutBound 6 := { lost := (rows 32 0 32 16 0 0), upper := (rows 21 50 7 43 59 43), lower := (rows 21 50 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 45 34 47 8 0 32) },{ target := 5, region := (rows 3 2 6 8 16 0), good := (rows 21 23 7 8 16 0) }] }

theorem profile13_node272 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,3] 6 43 profile13_node272_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,3] 6 43 profile13_node272_cert).mp (by decide +kernel))

def profile13_node274_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 21 50 13 11 50 34), lower := (rows 21 50 13 11 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 54 50 62 58 50 50) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 21 48 13 13 16 32) }] }

theorem profile13_node274 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,3] 6 34 profile13_node274_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,3] 6 34 profile13_node274_cert).mp (by decide +kernel))

def profile13_node275_cert : CutBound 6 := { lost := (rows 2 1 2 2 0 0), upper := (rows 21 50 13 41 18 34), lower := (rows 21 50 13 41 16 32), losses := [{ target := 0, region := (rows 0 63 4 8 63 63), good := (rows 54 50 62 58 50 50) },{ target := 1, region := (rows 3 0 14 10 16 32), good := (rows 21 61 13 45 16 32) }] }

theorem profile13_node275 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,33] 6 2 profile13_node275_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,33] 6 2 profile13_node275_cert).mp (by decide +kernel))

def profile13_node276_cert : CutBound 6 := { lost := (rows 0 0 0 17 0 0), upper := (rows 21 50 13 42 19 35), lower := (rows 21 50 13 42 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 20 58 12 42 16 32) },{ target := 4, region := (rows 1 2 4 10 0 32), good := (rows 5 42 13 42 0 32) }] }

theorem profile13_node276 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,34] 6 3 profile13_node276_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9,34] 6 3 profile13_node276_cert).mp (by decide +kernel))

def profile13_node273_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node273_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node273 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,9] 6 (by decide) (choices 2) [3,33,34] profile13_node273_route profile13_node273_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node274
  · exact profile13_node275
  · exact profile13_node276

def profile13_node278_cert : CutBound 6 := { lost := (rows 2 0 1 0 0 0), upper := (rows 21 50 14 11 49 33), lower := (rows 21 50 14 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 20 50 14 14 16 32) },{ target := 1, region := (rows 5 0 4 8 29 45), good := (rows 53 48 61 57 16 32) }] }

theorem profile13_node278 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,3] 6 33 profile13_node278_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,3] 6 33 profile13_node278_cert).mp (by decide +kernel))

def profile13_node280_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 21 50 14 41 17 34), lower := (rows 21 50 14 41 17 32), losses := [{ target := 0, region := (rows 0 19 12 8 16 63), good := (rows 54 50 46 46 50 32) }] }

theorem profile13_node280 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33,1] 6 2 profile13_node280_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33,1] 6 2 profile13_node280_cert).mp (by decide +kernel))

def profile13_node281_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 21 50 14 41 18 33), lower := (rows 21 50 14 41 18 32), losses := [{ target := 0, region := (rows 0 42 12 8 62 32), good := (rows 20 50 30 62 18 50) }] }

theorem profile13_node281 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33,2] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33,2] 6 1 profile13_node281_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33,2] 6 1 profile13_node281_cert).mp (by decide +kernel))

def profile13_node279_column : Nat → Fin 6 := fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile13_node279_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node279 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,33] 6 (by decide) (choices 1) [1,2] profile13_node279_route profile13_node279_column
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node280
  · exact profile13_node281

def profile13_node282_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 21 50 14 42 17 33), lower := (rows 21 50 14 42 16 32), losses := [{ target := 0, region := (rows 0 2 14 10 16 32), good := (rows 20 62 14 46 16 32) }] }

theorem profile13_node282 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,34] 6 1 profile13_node282_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10,34] 6 1 profile13_node282_cert).mp (by decide +kernel))

def profile13_node277_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node277_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node277 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,10] 6 (by decide) (choices 2) [3,33,34] profile13_node277_route profile13_node277_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node278
  · exact profile13_node279
  · exact profile13_node282

def profile13_node283_cert : CutBound 6 := { lost := (rows 2 0 2 0 0 0), upper := (rows 21 50 37 11 27 43), lower := (rows 21 50 37 8 16 32), losses := [{ target := 1, region := (rows 3 0 6 8 16 32), good := (rows 21 53 37 8 16 32) }] }

theorem profile13_node283 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,33] 6 11 profile13_node283_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,33] 6 11 profile13_node283_cert).mp (by decide +kernel))

def profile13_node284_cert : CutBound 6 := { lost := (rows 0 0 17 0 0 0), upper := (rows 21 50 38 11 27 43), lower := (rows 21 50 38 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 20 54 38 8 16 32) },{ target := 4, region := (rows 1 2 6 8 0 32), good := (rows 5 38 38 8 0 32) }] }

theorem profile13_node284 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,34] 6 11 profile13_node284_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,34] 6 11 profile13_node284_cert).mp (by decide +kernel))

def profile13_node286_cert : CutBound 6 := { lost := (rows 32 0 16 0 0 0), upper := (rows 21 50 44 11 19 35), lower := (rows 21 50 44 11 16 32), losses := [{ target := 4, region := (rows 1 2 12 8 0 40), good := (rows 5 34 44 47 0 32) },{ target := 5, region := (rows 5 2 4 8 24 0), good := (rows 21 18 29 27 16 0) }] }

theorem profile13_node286 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,40,3] 6 3 profile13_node286_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,40,3] 6 3 profile13_node286_cert).mp (by decide +kernel))

def profile13_node285_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node285_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node285 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48,40] 6 (by decide) (choices 2) [3] profile13_node285_route profile13_node285_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node286

def profile13_node271_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile13_node271_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node271 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20,48] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile13_node271_route profile13_node271_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node272
  · exact profile13_node273
  · exact profile13_node277
  · exact profile13_node283
  · exact profile13_node284
  · exact profile13_node285

def profile13_node204_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node204_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node204 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [20] 6 (by decide) (choices 2) [9,17,24,33,40,48] profile13_node204_route profile13_node204_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node205
  · exact profile13_node221
  · exact profile13_node222
  · exact profile13_node232
  · exact profile13_node255
  · exact profile13_node271

def profile13_node289_cert : CutBound 6 := { lost := (rows 0 16 16 1 0 0), upper := (rows 49 7 7 58 58 58), lower := (rows 49 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 48 62 62 8 16 32) },{ target := 4, region := (rows 1 7 7 8 0 32), good := (rows 39 7 7 8 0 32) }] }

theorem profile13_node289 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,3] 6 58 profile13_node289_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,3] 6 58 profile13_node289_cert).mp (by decide +kernel))

def profile13_node290_cert : CutBound 6 := { lost := (rows 0 16 0 1 0 0), upper := (rows 49 7 13 58 50 50), lower := (rows 49 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 12 8 16 32) },{ target := 4, region := (rows 1 6 4 8 0 32), good := (rows 33 7 15 8 0 32) }] }

theorem profile13_node290 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,9] 6 50 profile13_node290_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,9] 6 50 profile13_node290_cert).mp (by decide +kernel))

def profile13_node292_cert : CutBound 6 := { lost := (rows 2 0 1 0 0 0), upper := (rows 49 7 14 11 48 48), lower := (rows 49 7 14 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 63 63), good := (rows 48 54 62 62 48 48) },{ target := 1, region := (rows 63 0 4 8 63 63), good := (rows 49 53 61 57 49 49) }] }

theorem profile13_node292 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,3] 6 48 profile13_node292_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,3] 6 48 profile13_node292_cert).mp (by decide +kernel))

def profile13_node293_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 49 7 14 25 50 34), lower := (rows 49 7 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 57 13 12 25 16 32) },{ target := 4, region := (rows 1 10 12 8 0 46), good := (rows 33 39 46 47 0 32) }] }

theorem profile13_node293 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,17] 6 34 profile13_node293_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,17] 6 34 profile13_node293_cert).mp (by decide +kernel))

def profile13_node294_cert : CutBound 6 := { lost := (rows 2 0 1 0 0 0), upper := (rows 49 7 14 26 49 33), lower := (rows 49 7 14 26 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 48 6 14 30 16 32) },{ target := 1, region := (rows 63 0 4 8 63 63), good := (rows 49 53 61 57 49 49) }] }

theorem profile13_node294 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,18] 6 33 profile13_node294_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,18] 6 33 profile13_node294_cert).mp (by decide +kernel))

def profile13_node295_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 49 7 14 56 19 35), lower := (rows 49 7 14 56 16 32), losses := [{ target := 0, region := (rows 0 2 6 9 16 32), good := (rows 56 14 14 56 16 32) }] }

theorem profile13_node295 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,48] 6 3 profile13_node295_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10,48] 6 3 profile13_node295_cert).mp (by decide +kernel))

def profile13_node291_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node291_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node291 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,10] 6 (by decide) (choices 2) [3,17,18,48] profile13_node291_route profile13_node291_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node292
  · exact profile13_node293
  · exact profile13_node294
  · exact profile13_node295

def profile13_node296_cert : CutBound 6 := { lost := (rows 0 0 2 1 0 0), upper := (rows 49 7 21 42 58 42), lower := (rows 49 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 20 8 16 32) },{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 5 21 8 16 32) }] }

theorem profile13_node296 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,17] 6 42 profile13_node296_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,17] 6 42 profile13_node296_cert).mp (by decide +kernel))

def profile13_node297_cert : CutBound 6 := { lost := (rows 0 32 32 16 0 0), upper := (rows 49 7 22 43 59 43), lower := (rows 49 7 22 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 33 47 46 8 0 32) },{ target := 5, region := (rows 1 3 5 8 16 0), good := (rows 23 7 22 8 16 0) }] }

theorem profile13_node297 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,18] 6 43 profile13_node297_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,18] 6 43 profile13_node297_cert).mp (by decide +kernel))

def profile13_node299_cert : CutBound 6 := { lost := (rows 0 0 1 16 0 0), upper := (rows 49 7 28 11 50 34), lower := (rows 49 7 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 26 42), good := (rows 48 54 60 62 16 32) },{ target := 4, region := (rows 1 2 4 10 0 42), good := (rows 33 47 44 43 0 32) }] }

theorem profile13_node299 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,3] 6 34 profile13_node299_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,3] 6 34 profile13_node299_cert).mp (by decide +kernel))

def profile13_node300_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 49 7 28 41 18 34), lower := (rows 49 7 28 41 16 32), losses := [{ target := 1, region := (rows 1 0 5 9 16 32), good := (rows 61 13 28 45 16 32) }] }

theorem profile13_node300 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,33] 6 2 profile13_node300_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,33] 6 2 profile13_node300_cert).mp (by decide +kernel))

def profile13_node301_cert : CutBound 6 := { lost := (rows 0 0 32 16 0 0), upper := (rows 49 7 28 42 19 35), lower := (rows 49 7 28 42 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 33 47 12 42 0 32) },{ target := 5, region := (rows 1 2 12 8 18 0), good := (rows 17 23 28 30 16 0) }] }

theorem profile13_node301 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,34] 6 3 profile13_node301_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24,34] 6 3 profile13_node301_cert).mp (by decide +kernel))

def profile13_node298_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node298_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node298 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,24] 6 (by decide) (choices 2) [3,33,34] profile13_node298_route profile13_node298_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node299
  · exact profile13_node300
  · exact profile13_node301

def profile13_node302_cert : CutBound 6 := { lost := (rows 2 0 3 0 0 0), upper := (rows 49 7 52 11 27 43), lower := (rows 49 7 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 52 6 52 8 16 32) },{ target := 1, region := (rows 5 0 5 8 16 32), good := (rows 53 5 53 8 16 32) }] }

theorem profile13_node302 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,48] 6 11 profile13_node302_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5,48] 6 11 profile13_node302_cert).mp (by decide +kernel))

def profile13_node288_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node288_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node288 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,5] 6 (by decide) (choices 2) [3,9,10,17,18,24,48] profile13_node288_route profile13_node288_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node289
  · exact profile13_node290
  · exact profile13_node291
  · exact profile13_node296
  · exact profile13_node297
  · exact profile13_node298
  · exact profile13_node302

def profile13_node305_cert : CutBound 6 := { lost := (rows 2 16 16 16 0 0), upper := (rows 49 14 7 11 48 48), lower := (rows 49 14 7 11 16 32), losses := [{ target := 1, region := (rows 63 0 4 8 63 63), good := (rows 49 61 53 57 49 49) },{ target := 4, region := (rows 1 15 13 13 0 32), good := (rows 47 14 15 15 0 32) }] }

theorem profile13_node305 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,3] 6 48 profile13_node305_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,3] 6 48 profile13_node305_cert).mp (by decide +kernel))

def profile13_node306_cert : CutBound 6 := { lost := (rows 0 16 16 2 0 0), upper := (rows 49 14 7 25 50 34), lower := (rows 49 14 7 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 57 12 13 25 16 32) },{ target := 4, region := (rows 1 10 12 8 0 46), good := (rows 33 46 39 47 0 32) }] }

theorem profile13_node306 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,17] 6 34 profile13_node306_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,17] 6 34 profile13_node306_cert).mp (by decide +kernel))

def profile13_node307_cert : CutBound 6 := { lost := (rows 2 32 32 32 0 0), upper := (rows 49 14 7 26 49 33), lower := (rows 49 14 7 26 16 32), losses := [{ target := 1, region := (rows 63 0 4 8 63 63), good := (rows 49 61 53 57 49 49) },{ target := 5, region := (rows 1 7 5 9 16 0), good := (rows 31 14 15 26 16 0) }] }

theorem profile13_node307 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,18] 6 33 profile13_node307_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,18] 6 33 profile13_node307_cert).mp (by decide +kernel))

def profile13_node308_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 49 14 7 56 19 35), lower := (rows 49 14 7 56 16 32), losses := [{ target := 0, region := (rows 0 6 4 9 16 32), good := (rows 56 14 14 56 16 32) }] }

theorem profile13_node308 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,48] 6 3 profile13_node308_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3,48] 6 3 profile13_node308_cert).mp (by decide +kernel))

def profile13_node304_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | _ => 0

def profile13_node304_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node304 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,3] 6 (by decide) (choices 2) [3,17,18,48] profile13_node304_route profile13_node304_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node305
  · exact profile13_node306
  · exact profile13_node307
  · exact profile13_node308

def profile13_node309_cert : CutBound 6 := { lost := (rows 0 16 2 16 0 0), upper := (rows 49 14 21 43 51 35), lower := (rows 49 14 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 12 21 8 16 32) },{ target := 4, region := (rows 1 6 4 12 0 36), good := (rows 33 46 47 8 0 32) }] }

theorem profile13_node309 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,17] 6 35 profile13_node309_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,17] 6 35 profile13_node309_cert).mp (by decide +kernel))

def profile13_node311_cert : CutBound 6 := { lost := (rows 2 32 32 32 0 0), upper := (rows 49 14 22 11 49 33), lower := (rows 49 14 22 11 16 32), losses := [{ target := 1, region := (rows 63 0 4 8 63 63), good := (rows 49 61 53 57 49 49) },{ target := 5, region := (rows 1 11 5 9 16 0), good := (rows 31 14 22 15 16 0) }] }

theorem profile13_node311 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,3] 6 33 profile13_node311_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,3] 6 33 profile13_node311_cert).mp (by decide +kernel))

def profile13_node312_cert : CutBound 6 := { lost := (rows 0 0 0 18 0 0), upper := (rows 49 14 22 41 19 35), lower := (rows 49 14 22 41 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 57 12 20 41 16 32) },{ target := 4, region := (rows 1 2 4 9 0 32), good := (rows 41 14 6 41 0 32) }] }

theorem profile13_node312 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,33] 6 3 profile13_node312_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,33] 6 3 profile13_node312_cert).mp (by decide +kernel))

def profile13_node313_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 49 14 22 42 17 33), lower := (rows 49 14 22 42 16 32), losses := [{ target := 0, region := (rows 0 3 5 9 16 32), good := (rows 62 14 22 42 16 32) }] }

theorem profile13_node313 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,34] 6 1 profile13_node313_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18,34] 6 1 profile13_node313_cert).mp (by decide +kernel))

def profile13_node310_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node310_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node310 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,18] 6 (by decide) (choices 2) [3,33,34] profile13_node310_route profile13_node310_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node311
  · exact profile13_node312
  · exact profile13_node313

def profile13_node314_cert : CutBound 6 := { lost := (rows 2 0 3 0 0 0), upper := (rows 49 14 52 11 19 35), lower := (rows 49 14 52 8 16 32), losses := [{ target := 0, region := (rows 0 2 5 8 16 32), good := (rows 52 14 52 8 16 32) },{ target := 1, region := (rows 5 0 5 8 16 32), good := (rows 53 13 53 8 16 32) }] }

theorem profile13_node314 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,48] 6 3 profile13_node314_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12,48] 6 3 profile13_node314_cert).mp (by decide +kernel))

def profile13_node303_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile13_node303_route : Route 6 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node303 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,12] 6 (by decide) (choices 2) [3,17,18,48] profile13_node303_route profile13_node303_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile13_node304
  · exact profile13_node309
  · exact profile13_node310
  · exact profile13_node314

def profile13_node315_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 49 19 47 47 63 47), lower := (rows 49 19 4 8 16 32), losses := [{ target := 4, region := (rows 1 2 6 10 0 34), good := (rows 33 47 4 8 0 32) }] }

theorem profile13_node315 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,17] 6 47 profile13_node315_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,17] 6 47 profile13_node315_cert).mp (by decide +kernel))

def profile13_node317_cert : CutBound 6 := { lost := (rows 0 32 32 16 0 0), upper := (rows 49 22 7 43 59 43), lower := (rows 49 22 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 33 46 47 8 0 32) },{ target := 5, region := (rows 1 3 5 8 16 0), good := (rows 23 22 7 8 16 0) }] }

theorem profile13_node317 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,3] 6 43 profile13_node317_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,3] 6 43 profile13_node317_cert).mp (by decide +kernel))

def profile13_node319_cert : CutBound 6 := { lost := (rows 0 1 2 0 0 0), upper := (rows 49 22 13 11 50 34), lower := (rows 49 22 13 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 30 46), good := (rows 48 54 62 58 16 32) },{ target := 1, region := (rows 1 0 12 8 16 32), good := (rows 49 20 13 13 16 32) }] }

theorem profile13_node319 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,3] 6 34 profile13_node319_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,3] 6 34 profile13_node319_cert).mp (by decide +kernel))

def profile13_node320_cert : CutBound 6 := { lost := (rows 0 1 2 2 0 0), upper := (rows 49 22 13 41 18 34), lower := (rows 49 22 13 41 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 48 54 62 40 16 32) },{ target := 1, region := (rows 1 0 13 9 16 32), good := (rows 61 20 13 45 16 32) }] }

theorem profile13_node320 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,33] 6 2 profile13_node320_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,33] 6 2 profile13_node320_cert).mp (by decide +kernel))

def profile13_node322_cert : CutBound 6 := { lost := (rows 2 0 2 1 0 0), upper := (rows 49 22 13 42 17 34), lower := (rows 49 22 13 42 17 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 42), good := (rows 48 62 44 42 16 32) },{ target := 1, region := (rows 41 0 12 8 61 32), good := (rows 49 20 29 61 17 49) }] }

theorem profile13_node322 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34,1] 6 2 profile13_node322_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34,1] 6 2 profile13_node322_cert).mp (by decide +kernel))

def profile13_node323_cert : CutBound 6 := { lost := (rows 2 1 2 0 0 0), upper := (rows 49 22 13 42 18 33), lower := (rows 49 22 13 42 18 32), losses := [{ target := 0, region := (rows 0 6 4 8 30 32), good := (rows 48 22 30 58 18 32) },{ target := 1, region := (rows 19 0 12 8 16 63), good := (rows 49 53 45 45 49 32) }] }

theorem profile13_node323 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34,2] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34,2] 6 1 profile13_node323_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34,2] 6 1 profile13_node323_cert).mp (by decide +kernel))

def profile13_node321_column : Nat → Fin 6 := fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile13_node321_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node321 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9,34] 6 (by decide) (choices 1) [1,2] profile13_node321_route profile13_node321_column
    (by change RowCover 6 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile13_node322
  · exact profile13_node323

def profile13_node318_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node318_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node318 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,9] 6 (by decide) (choices 2) [3,33,34] profile13_node318_route profile13_node318_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node319
  · exact profile13_node320
  · exact profile13_node321

def profile13_node325_cert : CutBound 6 := { lost := (rows 2 0 1 0 0 0), upper := (rows 49 22 14 11 49 33), lower := (rows 49 22 14 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 48 22 14 14 16 32) },{ target := 1, region := (rows 63 0 4 8 63 63), good := (rows 49 53 61 57 49 49) }] }

theorem profile13_node325 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,3] 6 33 profile13_node325_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,3] 6 33 profile13_node325_cert).mp (by decide +kernel))

def profile13_node326_cert : CutBound 6 := { lost := (rows 0 0 0 18 0 0), upper := (rows 49 22 14 41 19 35), lower := (rows 49 22 14 41 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 57 20 12 41 16 32) },{ target := 4, region := (rows 1 2 4 9 0 32), good := (rows 41 6 14 41 0 32) }] }

theorem profile13_node326 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,33] 6 3 profile13_node326_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,33] 6 3 profile13_node326_cert).mp (by decide +kernel))

def profile13_node327_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 49 22 14 42 17 33), lower := (rows 49 22 14 42 16 32), losses := [{ target := 0, region := (rows 0 3 13 9 16 32), good := (rows 62 22 14 46 16 32) }] }

theorem profile13_node327 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,34] 6 1 profile13_node327_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10,34] 6 1 profile13_node327_cert).mp (by decide +kernel))

def profile13_node324_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node324_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node324 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,10] 6 (by decide) (choices 2) [3,33,34] profile13_node324_route profile13_node324_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile13_node325
  · exact profile13_node326
  · exact profile13_node327

def profile13_node328_cert : CutBound 6 := { lost := (rows 0 0 18 0 0 0), upper := (rows 49 22 37 11 27 43), lower := (rows 49 22 37 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 20 37 8 16 32) },{ target := 4, region := (rows 1 2 5 8 0 32), good := (rows 37 6 37 8 0 32) }] }

theorem profile13_node328 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,33] 6 11 profile13_node328_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,33] 6 11 profile13_node328_cert).mp (by decide +kernel))

def profile13_node329_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 49 22 38 11 27 43), lower := (rows 49 22 38 8 16 32), losses := [{ target := 0, region := (rows 0 3 5 8 16 32), good := (rows 54 22 38 8 16 32) }] }

theorem profile13_node329 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,34] 6 11 profile13_node329_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,34] 6 11 profile13_node329_cert).mp (by decide +kernel))

def profile13_node331_cert : CutBound 6 := { lost := (rows 0 32 16 0 0 0), upper := (rows 49 22 44 11 19 35), lower := (rows 49 22 44 11 16 32), losses := [{ target := 4, region := (rows 1 2 12 8 0 40), good := (rows 33 6 44 47 0 32) },{ target := 5, region := (rows 1 6 4 8 24 0), good := (rows 17 22 30 27 16 0) }] }

theorem profile13_node331 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,40,3] 6 3 profile13_node331_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,40,3] 6 3 profile13_node331_cert).mp (by decide +kernel))

def profile13_node330_column : Nat → Fin 6 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 48 => 4 | _ => 0

def profile13_node330_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node330 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20,40] 6 (by decide) (choices 2) [3] profile13_node330_route profile13_node330_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile13_node331

def profile13_node316_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | _ => 0

def profile13_node316_route : Route 6 := (fun mask => (mask,id))

theorem profile13_node316 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,20] 6 (by decide) (choices 2) [3,9,10,33,34,40] profile13_node316_route profile13_node316_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile13_node317
  · exact profile13_node318
  · exact profile13_node324
  · exact profile13_node328
  · exact profile13_node329
  · exact profile13_node330

def profile13_node332_cert : CutBound 6 := { lost := (rows 2 1 0 0 0 0), upper := (rows 49 50 15 15 31 47), lower := (rows 49 50 4 8 16 32), losses := [{ target := 0, region := (rows 0 3 4 8 16 32), good := (rows 50 50 4 8 16 32) },{ target := 1, region := (rows 3 0 4 8 16 32), good := (rows 49 49 4 8 16 32) }] }

theorem profile13_node332 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,48] 6 15 profile13_node332_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48,48] 6 15 profile13_node332_cert).mp (by decide +kernel))

def profile13_node287_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node287_route : Route 6 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node287 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [48] 6 (by decide) (choices 2) [5,12,17,20,48] profile13_node287_route profile13_node287_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile13_node288
  · exact profile13_node303
  · exact profile13_node315
  · exact profile13_node316
  · exact profile13_node332

def profile13_node0_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile13_node0_route : Route 6 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile13_node0 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [] 6 (by decide) (choices 2) [6,12,18,20,48] profile13_node0_route profile13_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile13_node1
  · exact profile13_node66
  · exact profile13_node98
  · exact profile13_node204
  · exact profile13_node287

theorem profile13 : Upper (D (n:=6) [34,34,33,33,18,18]) (R (n:=6) [34,34,33,33,18,18]) [] 6 := profile13_node0


#print axioms profile13
end Delivery.SmallBudgetTenFinite6
