import SmallBudgetTenFinite6Profile010Part001

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile10_node259_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 7 7 62 54 54), lower := (rows 25 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 24 62 62 8 16 32) }] }

theorem profile10_node259 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,3] 6 54 profile10_node259_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,3] 6 54 profile10_node259_cert).mp (by decide +kernel))

def profile10_node260_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 7 21 46 54 38), lower := (rows 25 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 24 62 20 8 16 32) }] }

theorem profile10_node260 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,17] 6 38 profile10_node260_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,17] 6 38 profile10_node260_cert).mp (by decide +kernel))

def profile10_node261_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 25 7 22 47 55 39), lower := (rows 25 7 22 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 9 47 46 8 0 32) }] }

theorem profile10_node261 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,18] 6 39 profile10_node261_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,18] 6 39 profile10_node261_cert).mp (by decide +kernel))

def profile10_node262_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 7 37 30 22 54), lower := (rows 25 7 37 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 24 62 36 8 16 32) }] }

theorem profile10_node262 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,33] 6 22 profile10_node262_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,33] 6 22 profile10_node262_cert).mp (by decide +kernel))

def profile10_node264_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 25 7 38 11 20 52), lower := (rows 25 7 38 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 31 47), good := (rows 60 54 54 62 16 32) }] }

theorem profile10_node264 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,3] 6 20 profile10_node264_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,3] 6 20 profile10_node264_cert).mp (by decide +kernel))

def profile10_node265_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 25 7 38 13 18 50), lower := (rows 25 7 38 13 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 24 54 54 60 16 32) }] }

theorem profile10_node265 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,5] 6 18 profile10_node265_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,5] 6 18 profile10_node265_cert).mp (by decide +kernel))

def profile10_node266_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 7 38 14 17 49), lower := (rows 25 7 38 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 32), good := (rows 24 14 46 14 16 32) }] }

theorem profile10_node266 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,6] 6 17 profile10_node266_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,6] 6 17 profile10_node266_cert).mp (by decide +kernel))

def profile10_node267_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 25 7 38 25 22 38), lower := (rows 25 7 38 25 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 24 54 54 24 16 32) }] }

theorem profile10_node267 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,17] 6 6 profile10_node267_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,17] 6 6 profile10_node267_cert).mp (by decide +kernel))

def profile10_node268_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 25 7 38 26 21 37), lower := (rows 25 7 38 26 16 32), losses := [{ target := 1, region := (rows 9 0 4 8 18 34), good := (rows 25 53 52 57 16 32) }] }

theorem profile10_node268 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,18] 6 5 profile10_node268_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,18] 6 5 profile10_node268_cert).mp (by decide +kernel))

def profile10_node269_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 25 7 38 28 19 35), lower := (rows 25 7 38 28 16 32), losses := [{ target := 1, region := (rows 9 0 4 8 16 32), good := (rows 25 5 36 29 16 32) }] }

theorem profile10_node269 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,20] 6 3 profile10_node269_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34,20] 6 3 profile10_node269_cert).mp (by decide +kernel))

def profile10_node263_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node263_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node263 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,34] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node263_route profile10_node263_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node264
  · exact profile10_node265
  · exact profile10_node266
  · exact profile10_node267
  · exact profile10_node268
  · exact profile10_node269

def profile10_node270_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 25 7 52 15 23 39), lower := (rows 25 7 52 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 9 47 36 8 0 32) }] }

theorem profile10_node270 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,48] 6 7 profile10_node270_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5,48] 6 7 profile10_node270_cert).mp (by decide +kernel))

def profile10_node258_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node258_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node258 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,5] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile10_node258_route profile10_node258_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node259
  · exact profile10_node260
  · exact profile10_node261
  · exact profile10_node262
  · exact profile10_node263
  · exact profile10_node270

def profile10_node271_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 25 19 39 47 55 39), lower := (rows 25 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 32), good := (rows 27 19 0 8 16 32) }] }

theorem profile10_node271 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,17] 6 39 profile10_node271_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,17] 6 39 profile10_node271_cert).mp (by decide +kernel))

def profile10_node273_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 25 22 7 47 55 39), lower := (rows 25 22 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 9 46 47 8 0 32) }] }

theorem profile10_node273 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,3] 6 39 profile10_node273_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,3] 6 39 profile10_node273_cert).mp (by decide +kernel))

def profile10_node275_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 25 22 37 11 22 38), lower := (rows 25 22 37 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 24 54 54 58 16 32) }] }

theorem profile10_node275 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,3] 6 6 profile10_node275_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,3] 6 6 profile10_node275_cert).mp (by decide +kernel))

def profile10_node276_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 25 22 37 13 18 34), lower := (rows 25 22 37 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 47), good := (rows 58 54 54 62 16 32) }] }

theorem profile10_node276 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,5] 6 2 profile10_node276_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,5] 6 2 profile10_node276_cert).mp (by decide +kernel))

def profile10_node277_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 22 37 14 19 35), lower := (rows 25 22 37 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 24 30 36 14 16 32) }] }

theorem profile10_node277 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,6] 6 3 profile10_node277_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33,6] 6 3 profile10_node277_cert).mp (by decide +kernel))

def profile10_node274_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node274_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node274 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,33] 6 (by decide) (choices 2) [3,5,6] profile10_node274_route profile10_node274_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node275
  · exact profile10_node276
  · exact profile10_node277

def profile10_node279_cert : CutBound 6 := { lost := (rows 4 0 0 4 0 0), upper := (rows 25 22 38 11 21 37), lower := (rows 25 22 38 11 16 32), losses := [{ target := 2, region := (rows 3 2 0 14 16 32), good := (rows 25 27 43 11 16 32) }] }

theorem profile10_node279 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,3] 6 5 profile10_node279_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,3] 6 5 profile10_node279_cert).mp (by decide +kernel))

def profile10_node280_cert : CutBound 6 := { lost := (rows 2 0 0 2 0 0), upper := (rows 25 22 38 13 19 35), lower := (rows 25 22 38 13 16 32), losses := [{ target := 1, region := (rows 3 0 4 14 16 32), good := (rows 25 29 45 13 16 32) }] }

theorem profile10_node280 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,5] 6 3 profile10_node280_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,5] 6 3 profile10_node280_cert).mp (by decide +kernel))

def profile10_node281_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 22 38 14 17 33), lower := (rows 25 22 38 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 32), good := (rows 24 30 46 14 16 32) }] }

theorem profile10_node281 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,6] 6 1 profile10_node281_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34,6] 6 1 profile10_node281_cert).mp (by decide +kernel))

def profile10_node278_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node278_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node278 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20,34] 6 (by decide) (choices 2) [3,5,6] profile10_node278_route profile10_node278_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node279
  · exact profile10_node280
  · exact profile10_node281

def profile10_node272_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile10_node272_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node272 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,20] 6 (by decide) (choices 2) [3,33,34] profile10_node272_route profile10_node272_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node273
  · exact profile10_node274
  · exact profile10_node278

def profile10_node283_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 35 7 30 22 54), lower := (rows 25 35 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 24 34 62 8 16 32) }] }

theorem profile10_node283 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,3] 6 22 profile10_node283_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,3] 6 22 profile10_node283_cert).mp (by decide +kernel))

def profile10_node284_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 25 35 21 14 22 38), lower := (rows 25 35 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 29 37 21 8 16 32) }] }

theorem profile10_node284 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,17] 6 6 profile10_node284_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,17] 6 6 profile10_node284_cert).mp (by decide +kernel))

def profile10_node286_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 25 35 22 11 20 36), lower := (rows 25 35 22 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 31 47), good := (rows 60 54 54 62 16 32) }] }

theorem profile10_node286 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,3] 6 4 profile10_node286_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,3] 6 4 profile10_node286_cert).mp (by decide +kernel))

def profile10_node287_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 25 35 22 13 22 38), lower := (rows 25 35 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 24 54 54 60 16 32) }] }

theorem profile10_node287 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,5] 6 6 profile10_node287_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,5] 6 6 profile10_node287_cert).mp (by decide +kernel))

def profile10_node288_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 35 22 14 21 37), lower := (rows 25 35 22 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 24 34 30 14 16 32) }] }

theorem profile10_node288 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,6] 6 5 profile10_node288_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18,6] 6 5 profile10_node288_cert).mp (by decide +kernel))

def profile10_node285_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node285_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node285 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33,18] 6 (by decide) (choices 2) [3,5,6] profile10_node285_route profile10_node285_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node286
  · exact profile10_node287
  · exact profile10_node288

def profile10_node282_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node282_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node282 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,33] 6 (by decide) (choices 2) [3,17,18] profile10_node282_route profile10_node282_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node283
  · exact profile10_node284
  · exact profile10_node285

def profile10_node291_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 25 38 7 11 20 52), lower := (rows 25 38 7 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 24 54 54 58 16 32) }] }

theorem profile10_node291 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,3] 6 20 profile10_node291_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,3] 6 20 profile10_node291_cert).mp (by decide +kernel))

def profile10_node292_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 25 38 7 13 18 50), lower := (rows 25 38 7 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 47), good := (rows 58 54 54 62 16 32) }] }

theorem profile10_node292 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,5] 6 18 profile10_node292_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,5] 6 18 profile10_node292_cert).mp (by decide +kernel))

def profile10_node293_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 38 7 14 17 49), lower := (rows 25 38 7 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 32), good := (rows 24 46 14 14 16 32) }] }

theorem profile10_node293 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,6] 6 17 profile10_node293_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,6] 6 17 profile10_node293_cert).mp (by decide +kernel))

def profile10_node294_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 25 38 7 25 22 38), lower := (rows 25 38 7 25 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 24 54 54 24 16 32) }] }

theorem profile10_node294 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,17] 6 6 profile10_node294_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,17] 6 6 profile10_node294_cert).mp (by decide +kernel))

def profile10_node295_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 25 38 7 26 21 37), lower := (rows 25 38 7 26 16 32), losses := [{ target := 1, region := (rows 9 0 4 8 20 36), good := (rows 25 52 53 25 16 32) }] }

theorem profile10_node295 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,18] 6 5 profile10_node295_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,18] 6 5 profile10_node295_cert).mp (by decide +kernel))

def profile10_node296_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 25 38 7 28 19 35), lower := (rows 25 38 7 28 16 32), losses := [{ target := 1, region := (rows 9 0 4 8 16 32), good := (rows 25 36 5 29 16 32) }] }

theorem profile10_node296 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,20] 6 3 profile10_node296_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3,20] 6 3 profile10_node296_cert).mp (by decide +kernel))

def profile10_node290_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node290_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node290 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,3] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node290_route profile10_node290_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node291
  · exact profile10_node292
  · exact profile10_node293
  · exact profile10_node294
  · exact profile10_node295
  · exact profile10_node296

def profile10_node297_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 25 38 21 15 23 39), lower := (rows 25 38 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 29 36 21 8 16 32) }] }

theorem profile10_node297 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,17] 6 7 profile10_node297_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,17] 6 7 profile10_node297_cert).mp (by decide +kernel))

def profile10_node299_cert : CutBound 6 := { lost := (rows 4 0 0 4 0 0), upper := (rows 25 38 22 11 21 37), lower := (rows 25 38 22 11 16 32), losses := [{ target := 2, region := (rows 5 2 0 14 16 32), good := (rows 25 43 27 11 16 32) }] }

theorem profile10_node299 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,3] 6 5 profile10_node299_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,3] 6 5 profile10_node299_cert).mp (by decide +kernel))

def profile10_node300_cert : CutBound 6 := { lost := (rows 2 0 0 2 0 0), upper := (rows 25 38 22 13 19 35), lower := (rows 25 38 22 13 16 32), losses := [{ target := 1, region := (rows 5 0 4 14 16 32), good := (rows 25 45 29 13 16 32) }] }

theorem profile10_node300 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,5] 6 3 profile10_node300_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,5] 6 3 profile10_node300_cert).mp (by decide +kernel))

def profile10_node301_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 25 38 22 14 17 33), lower := (rows 25 38 22 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 32), good := (rows 24 46 30 14 16 32) }] }

theorem profile10_node301 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,6] 6 1 profile10_node301_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18,6] 6 1 profile10_node301_cert).mp (by decide +kernel))

def profile10_node298_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node298_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node298 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36,18] 6 (by decide) (choices 2) [3,5,6] profile10_node298_route profile10_node298_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node299
  · exact profile10_node300
  · exact profile10_node301

def profile10_node289_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node289_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node289 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,36] 6 (by decide) (choices 2) [3,17,18] profile10_node289_route profile10_node289_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node290
  · exact profile10_node297
  · exact profile10_node298

def profile10_node303_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 25 50 7 15 23 39), lower := (rows 25 50 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 9 34 47 8 0 32) }] }

theorem profile10_node303 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,48,3] 6 7 profile10_node303_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,48,3] 6 7 profile10_node303_cert).mp (by decide +kernel))

def profile10_node302_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile10_node302_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node302 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24,48] 6 (by decide) (choices 2) [3] profile10_node302_route profile10_node302_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node303

def profile10_node257_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | _ => 0

def profile10_node257_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node257 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [24] 6 (by decide) (choices 2) [5,17,20,33,36,48] profile10_node257_route profile10_node257_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node258
  · exact profile10_node271
  · exact profile10_node272
  · exact profile10_node282
  · exact profile10_node289
  · exact profile10_node302

def profile10_node306_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 7 7 28 28 60), lower := (rows 35 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 58 62 62 8 16 32) }] }

theorem profile10_node306 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,3] 6 28 profile10_node306_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,3] 6 28 profile10_node306_cert).mp (by decide +kernel))

def profile10_node307_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 7 13 30 22 54), lower := (rows 35 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 12 8 16 32) }] }

theorem profile10_node307 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,9] 6 22 profile10_node307_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,9] 6 22 profile10_node307_cert).mp (by decide +kernel))

def profile10_node308_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 7 14 29 21 53), lower := (rows 35 7 14 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 34), good := (rows 57 61 60 8 16 32) }] }

theorem profile10_node308 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,10] 6 21 profile10_node308_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,10] 6 21 profile10_node308_cert).mp (by decide +kernel))

def profile10_node309_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 7 21 30 30 62), lower := (rows 35 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 58 62 20 8 16 32) }] }

theorem profile10_node309 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,17] 6 30 profile10_node309_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,17] 6 30 profile10_node309_cert).mp (by decide +kernel))

def profile10_node310_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 7 22 29 29 61), lower := (rows 35 7 22 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 18 34), good := (rows 57 61 60 8 16 32) }] }

theorem profile10_node310 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,18] 6 29 profile10_node310_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,18] 6 29 profile10_node310_cert).mp (by decide +kernel))

def profile10_node312_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 7 28 11 20 52), lower := (rows 35 7 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 30 46), good := (rows 50 54 60 62 16 32) }] }

theorem profile10_node312 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,3] 6 20 profile10_node312_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,3] 6 20 profile10_node312_cert).mp (by decide +kernel))

def profile10_node313_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 7 28 13 18 50), lower := (rows 35 7 28 13 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 19 35), good := (rows 50 54 28 60 16 32) }] }

theorem profile10_node313 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,5] 6 18 profile10_node313_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,5] 6 18 profile10_node313_cert).mp (by decide +kernel))

def profile10_node314_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 7 28 14 17 49), lower := (rows 35 7 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 42 14 28 14 16 32) }] }

theorem profile10_node314 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,6] 6 17 profile10_node314_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,6] 6 17 profile10_node314_cert).mp (by decide +kernel))

def profile10_node315_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 7 28 25 22 38), lower := (rows 35 7 28 25 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 18 34), good := (rows 50 54 28 28 16 32) }] }

theorem profile10_node315 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,17] 6 6 profile10_node315_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,17] 6 6 profile10_node315_cert).mp (by decide +kernel))

def profile10_node316_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 7 28 26 21 37), lower := (rows 35 7 28 26 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 34 6 28 30 16 32) }] }

theorem profile10_node316 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,18] 6 5 profile10_node316_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,18] 6 5 profile10_node316_cert).mp (by decide +kernel))

def profile10_node317_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 35 7 28 28 19 35), lower := (rows 35 7 28 28 16 32), losses := [{ target := 0, region := (rows 0 2 28 28 16 32), good := (rows 34 14 28 28 28 32) }] }

theorem profile10_node317 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,20] 6 3 profile10_node317_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24,20] 6 3 profile10_node317_cert).mp (by decide +kernel))

def profile10_node311_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node311_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node311 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5,24] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node311_route profile10_node311_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node312
  · exact profile10_node313
  · exact profile10_node314
  · exact profile10_node315
  · exact profile10_node316
  · exact profile10_node317

def profile10_node305_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node305_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node305 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,5] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node305_route profile10_node305_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node306
  · exact profile10_node307
  · exact profile10_node308
  · exact profile10_node309
  · exact profile10_node310
  · exact profile10_node311

def profile10_node319_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 11 7 28 20 52), lower := (rows 35 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 34 10 62 8 16 32) }] }

theorem profile10_node319 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,3] 6 20 profile10_node319_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,3] 6 20 profile10_node319_cert).mp (by decide +kernel))

def profile10_node321_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 11 21 14 20 52), lower := (rows 35 11 21 14 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 53 61 53 60 16 32) }] }

theorem profile10_node321 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,6] 6 20 profile10_node321_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,6] 6 20 profile10_node321_cert).mp (by decide +kernel))

def profile10_node322_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 11 21 26 20 36), lower := (rows 35 11 21 26 16 32), losses := [{ target := 1, region := (rows 1 0 7 8 31 47), good := (rows 53 61 53 60 16 32) }] }

theorem profile10_node322 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,18] 6 4 profile10_node322_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,18] 6 4 profile10_node322_cert).mp (by decide +kernel))

def profile10_node323_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 11 21 28 22 38), lower := (rows 35 11 21 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 34 10 28 28 16 32) }] }

theorem profile10_node323 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,20] 6 6 profile10_node323_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17,20] 6 6 profile10_node323_cert).mp (by decide +kernel))

def profile10_node320_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node320_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node320 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,17] 6 (by decide) (choices 2) [6,18,20] profile10_node320_route profile10_node320_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node321
  · exact profile10_node322
  · exact profile10_node323

def profile10_node325_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 11 22 13 20 52), lower := (rows 35 11 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 54 62 54 60 16 32) }] }

theorem profile10_node325 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,5] 6 20 profile10_node325_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,5] 6 20 profile10_node325_cert).mp (by decide +kernel))

def profile10_node326_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 11 22 25 20 36), lower := (rows 35 11 22 25 16 32), losses := [{ target := 0, region := (rows 0 2 7 8 31 47), good := (rows 54 62 54 60 16 32) }] }

theorem profile10_node326 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,17] 6 4 profile10_node326_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,17] 6 4 profile10_node326_cert).mp (by decide +kernel))

def profile10_node327_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 11 22 28 21 37), lower := (rows 35 11 22 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 34 10 30 28 16 32) }] }

theorem profile10_node327 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,20] 6 5 profile10_node327_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18,20] 6 5 profile10_node327_cert).mp (by decide +kernel))

def profile10_node324_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node324_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node324 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9,18] 6 (by decide) (choices 2) [5,17,20] profile10_node324_route profile10_node324_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node325
  · exact profile10_node326
  · exact profile10_node327

def profile10_node318_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node318_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node318 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,9] 6 (by decide) (choices 2) [3,17,18] profile10_node318_route profile10_node318_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node319
  · exact profile10_node320
  · exact profile10_node324

def profile10_node329_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 14 7 29 21 53), lower := (rows 35 14 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 33 60 61 8 16 32) }] }

theorem profile10_node329 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,3] 6 21 profile10_node329_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,3] 6 21 profile10_node329_cert).mp (by decide +kernel))

def profile10_node331_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 14 21 11 20 52), lower := (rows 35 14 21 11 16 32), losses := [{ target := 1, region := (rows 1 0 13 8 31 47), good := (rows 53 60 53 61 16 32) }] }

theorem profile10_node331 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,3] 6 20 profile10_node331_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,3] 6 20 profile10_node331_cert).mp (by decide +kernel))

def profile10_node332_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 14 21 13 18 50), lower := (rows 35 14 21 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 27 43), good := (rows 50 62 52 62 16 32) }] }

theorem profile10_node332 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,5] 6 18 profile10_node332_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,5] 6 18 profile10_node332_cert).mp (by decide +kernel))

def profile10_node333_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 35 14 21 14 17 49), lower := (rows 35 14 21 14 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 32), good := (rows 42 14 30 14 16 32) }] }

theorem profile10_node333 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,6] 6 17 profile10_node333_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,6] 6 17 profile10_node333_cert).mp (by decide +kernel))

def profile10_node334_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 35 14 21 25 22 38), lower := (rows 35 14 21 25 16 32), losses := [{ target := 1, region := (rows 1 0 12 12 16 32), good := (rows 33 12 29 29 16 32) }] }

theorem profile10_node334 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,17] 6 6 profile10_node334_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,17] 6 6 profile10_node334_cert).mp (by decide +kernel))

def profile10_node335_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 35 14 21 26 21 37), lower := (rows 35 14 21 26 16 32), losses := [{ target := 0, region := (rows 0 6 4 12 16 32), good := (rows 34 14 30 26 16 32) }] }

theorem profile10_node335 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,18] 6 5 profile10_node335_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,18] 6 5 profile10_node335_cert).mp (by decide +kernel))

def profile10_node336_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 35 14 21 28 19 35), lower := (rows 35 14 21 28 16 32), losses := [{ target := 0, region := (rows 0 14 4 12 16 32), good := (rows 34 14 30 30 16 32) }] }

theorem profile10_node336 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,20] 6 3 profile10_node336_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17,20] 6 3 profile10_node336_cert).mp (by decide +kernel))

def profile10_node330_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node330_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node330 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,17] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node330_route profile10_node330_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node331
  · exact profile10_node332
  · exact profile10_node333
  · exact profile10_node334
  · exact profile10_node335
  · exact profile10_node336

def profile10_node338_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 14 22 13 17 49), lower := (rows 35 14 22 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 34 14 22 14 16 32) }] }

theorem profile10_node338 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,5] 6 17 profile10_node338_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,5] 6 17 profile10_node338_cert).mp (by decide +kernel))

def profile10_node339_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 35 14 22 25 21 37), lower := (rows 35 14 22 25 16 32), losses := [{ target := 0, region := (rows 0 10 12 8 16 32), good := (rows 34 14 22 30 16 32) }] }

theorem profile10_node339 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,17] 6 5 profile10_node339_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,17] 6 5 profile10_node339_cert).mp (by decide +kernel))

def profile10_node340_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 35 14 22 28 17 33), lower := (rows 35 14 22 28 16 32), losses := [{ target := 0, region := (rows 0 30 28 28 16 32), good := (rows 34 14 30 30 30 32) }] }

theorem profile10_node340 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,20] 6 1 profile10_node340_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18,20] 6 1 profile10_node340_cert).mp (by decide +kernel))

def profile10_node337_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node337_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node337 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12,18] 6 (by decide) (choices 2) [5,17,20] profile10_node337_route profile10_node337_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node338
  · exact profile10_node339
  · exact profile10_node340

def profile10_node328_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node328_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node328 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,12] 6 (by decide) (choices 2) [3,17,18] profile10_node328_route profile10_node328_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node329
  · exact profile10_node330
  · exact profile10_node337

def profile10_node342_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 19 7 28 28 60), lower := (rows 35 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 34 18 62 8 16 32) }] }

theorem profile10_node342 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,3] 6 28 profile10_node342_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,3] 6 28 profile10_node342_cert).mp (by decide +kernel))

def profile10_node344_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 35 19 13 14 20 52), lower := (rows 35 19 13 14 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 32), good := (rows 47 15 13 14 0 32) }] }

theorem profile10_node344 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,6] 6 20 profile10_node344_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,6] 6 20 profile10_node344_cert).mp (by decide +kernel))

def profile10_node345_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 19 13 26 20 36), lower := (rows 35 19 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 20 36), good := (rows 42 26 60 26 16 32) }] }

theorem profile10_node345 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,18] 6 4 profile10_node345_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,18] 6 4 profile10_node345_cert).mp (by decide +kernel))

def profile10_node346_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 35 19 13 28 22 38), lower := (rows 35 19 13 28 16 32), losses := [{ target := 1, region := (rows 1 0 7 10 16 32), good := (rows 45 29 13 28 16 32) }] }

theorem profile10_node346 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,20] 6 6 profile10_node346_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9,20] 6 6 profile10_node346_cert).mp (by decide +kernel))

def profile10_node343_column : Nat → Fin 6 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node343_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node343 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,9] 6 (by decide) (choices 2) [6,18,20] profile10_node343_route profile10_node343_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node344
  · exact profile10_node345
  · exact profile10_node346

def profile10_node348_cert : CutBound 6 := { lost := (rows 0 0 16 16 0 0), upper := (rows 35 19 14 13 20 52), lower := (rows 35 19 14 13 16 32), losses := [{ target := 4, region := (rows 1 2 7 11 0 32), good := (rows 47 15 14 13 0 32) }] }

theorem profile10_node348 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,5] 6 20 profile10_node348_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,5] 6 20 profile10_node348_cert).mp (by decide +kernel))

def profile10_node349_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 19 14 25 20 36), lower := (rows 35 19 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 20 36), good := (rows 41 25 60 25 16 32) }] }

theorem profile10_node349 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,17] 6 4 profile10_node349_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,17] 6 4 profile10_node349_cert).mp (by decide +kernel))

def profile10_node350_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 35 19 14 28 21 37), lower := (rows 35 19 14 28 16 32), losses := [{ target := 0, region := (rows 0 2 7 10 16 32), good := (rows 46 30 14 28 16 32) }] }

theorem profile10_node350 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,20] 6 5 profile10_node350_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10,20] 6 5 profile10_node350_cert).mp (by decide +kernel))

def profile10_node347_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node347_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node347 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,10] 6 (by decide) (choices 2) [5,17,20] profile10_node347_route profile10_node347_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node348
  · exact profile10_node349
  · exact profile10_node350

def profile10_node351_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 19 21 14 30 46), lower := (rows 35 19 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 37 21 21 8 16 32) }] }

theorem profile10_node351 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,17] 6 14 profile10_node351_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,17] 6 14 profile10_node351_cert).mp (by decide +kernel))

def profile10_node352_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 19 22 13 29 45), lower := (rows 35 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 38 22 22 8 16 32) }] }

theorem profile10_node352 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,18] 6 13 profile10_node352_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,18] 6 13 profile10_node352_cert).mp (by decide +kernel))

def profile10_node354_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 19 28 11 20 36), lower := (rows 35 19 28 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 28 44), good := (rows 34 18 60 62 16 32) }] }

theorem profile10_node354 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,3] 6 4 profile10_node354_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,3] 6 4 profile10_node354_cert).mp (by decide +kernel))

def profile10_node355_cert : CutBound 6 := { lost := (rows 0 0 2 2 0 0), upper := (rows 35 19 28 13 22 38), lower := (rows 35 19 28 13 16 32), losses := [{ target := 1, region := (rows 1 0 6 11 16 32), good := (rows 45 29 28 13 16 32) }] }

theorem profile10_node355 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,5] 6 6 profile10_node355_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,5] 6 6 profile10_node355_cert).mp (by decide +kernel))

def profile10_node356_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 35 19 28 14 21 37), lower := (rows 35 19 28 14 16 32), losses := [{ target := 0, region := (rows 0 2 6 11 16 32), good := (rows 46 30 28 14 16 32) }] }

theorem profile10_node356 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,6] 6 5 profile10_node356_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24,6] 6 5 profile10_node356_cert).mp (by decide +kernel))

def profile10_node353_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node353_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node353 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17,24] 6 (by decide) (choices 2) [3,5,6] profile10_node353_route profile10_node353_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node354
  · exact profile10_node355
  · exact profile10_node356

def profile10_node341_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node341_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node341 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,17] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node341_route profile10_node341_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node342
  · exact profile10_node343
  · exact profile10_node347
  · exact profile10_node351
  · exact profile10_node352
  · exact profile10_node353

def profile10_node358_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 22 7 29 29 61), lower := (rows 35 22 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 33 60 61 8 16 32) }] }

theorem profile10_node358 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,3] 6 29 profile10_node358_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,3] 6 29 profile10_node358_cert).mp (by decide +kernel))

def profile10_node360_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 22 13 11 20 52), lower := (rows 35 22 13 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 50 54 62 58 16 32) }] }

theorem profile10_node360 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,3] 6 20 profile10_node360_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,3] 6 20 profile10_node360_cert).mp (by decide +kernel))

def profile10_node361_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 22 13 13 18 50), lower := (rows 35 22 13 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 47), good := (rows 50 54 62 62 16 32) }] }

theorem profile10_node361 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,5] 6 18 profile10_node361_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,5] 6 18 profile10_node361_cert).mp (by decide +kernel))

def profile10_node362_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 22 13 14 17 49), lower := (rows 35 22 13 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 42 30 12 14 16 32) }] }

theorem profile10_node362 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,6] 6 17 profile10_node362_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,6] 6 17 profile10_node362_cert).mp (by decide +kernel))

def profile10_node363_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 22 13 25 22 38), lower := (rows 35 22 13 25 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 50 54 62 24 16 32) }] }

theorem profile10_node363 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,17] 6 6 profile10_node363_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,17] 6 6 profile10_node363_cert).mp (by decide +kernel))

def profile10_node364_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 35 22 13 26 21 37), lower := (rows 35 22 13 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 42 30 12 26 16 32) }] }

theorem profile10_node364 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,18] 6 5 profile10_node364_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,18] 6 5 profile10_node364_cert).mp (by decide +kernel))

def profile10_node365_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 35 22 13 28 19 35), lower := (rows 35 22 13 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 10 16 32), good := (rows 42 30 14 30 16 32) }] }

theorem profile10_node365 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,20] 6 3 profile10_node365_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9,20] 6 3 profile10_node365_cert).mp (by decide +kernel))

def profile10_node359_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node359_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node359 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,9] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node359_route profile10_node359_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node360
  · exact profile10_node361
  · exact profile10_node362
  · exact profile10_node363
  · exact profile10_node364
  · exact profile10_node365

def profile10_node367_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 35 22 14 13 17 49), lower := (rows 35 22 14 13 16 32), losses := [{ target := 2, region := (rows 7 2 0 8 31 47), good := (rows 51 51 59 57 16 32) }] }

theorem profile10_node367 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,5] 6 17 profile10_node367_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,5] 6 17 profile10_node367_cert).mp (by decide +kernel))

def profile10_node368_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 35 22 14 25 21 37), lower := (rows 35 22 14 25 16 32), losses := [{ target := 0, region := (rows 0 10 12 8 16 32), good := (rows 34 22 14 30 16 32) }] }

theorem profile10_node368 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,17] 6 5 profile10_node368_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,17] 6 5 profile10_node368_cert).mp (by decide +kernel))

def profile10_node369_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 35 22 14 28 17 33), lower := (rows 35 22 14 28 16 32), losses := [{ target := 0, region := (rows 0 26 31 26 16 32), good := (rows 46 30 14 30 30 32) }] }

theorem profile10_node369 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,20] 6 1 profile10_node369_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10,20] 6 1 profile10_node369_cert).mp (by decide +kernel))

def profile10_node366_column : Nat → Fin 6 := fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node366_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node366 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,10] 6 (by decide) (choices 2) [5,17,20] profile10_node366_route profile10_node366_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node367
  · exact profile10_node368
  · exact profile10_node369

def profile10_node370_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 22 21 15 31 47), lower := (rows 35 22 21 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 34 22 22 8 16 32) }] }

theorem profile10_node370 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,17] 6 15 profile10_node370_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,17] 6 15 profile10_node370_cert).mp (by decide +kernel))

def profile10_node371_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 35 22 22 13 29 45), lower := (rows 35 22 22 8 16 32), losses := [{ target := 0, region := (rows 0 22 22 8 16 32), good := (rows 38 22 22 8 22 32) }] }

theorem profile10_node371 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,18] 6 13 profile10_node371_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,18] 6 13 profile10_node371_cert).mp (by decide +kernel))

def profile10_node372_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 22 28 15 23 39), lower := (rows 35 22 28 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 34 22 30 8 16 32) }] }

theorem profile10_node372 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,24] 6 7 profile10_node372_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20,24] 6 7 profile10_node372_cert).mp (by decide +kernel))

def profile10_node357_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node357_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node357 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,20] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node357_route profile10_node357_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node358
  · exact profile10_node359
  · exact profile10_node366
  · exact profile10_node370
  · exact profile10_node371
  · exact profile10_node372

def profile10_node374_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 35 26 7 29 21 53), lower := (rows 35 26 7 8 16 32), losses := [{ target := 1, region := (rows 1 0 4 12 20 36), good := (rows 33 24 61 8 16 32) }] }

theorem profile10_node374 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,3] 6 21 profile10_node374_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,3] 6 21 profile10_node374_cert).mp (by decide +kernel))

def profile10_node376_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 35 26 21 11 20 36), lower := (rows 35 26 21 11 16 32), losses := [{ target := 1, region := (rows 1 0 13 8 31 47), good := (rows 53 60 53 61 16 32) }] }

theorem profile10_node376 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,3] 6 4 profile10_node376_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,3] 6 4 profile10_node376_cert).mp (by decide +kernel))

def profile10_node377_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 35 26 21 13 22 38), lower := (rows 35 26 21 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 24 40), good := (rows 34 58 20 62 16 32) }] }

theorem profile10_node377 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,5] 6 6 profile10_node377_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,5] 6 6 profile10_node377_cert).mp (by decide +kernel))

def profile10_node378_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 35 26 21 14 21 37), lower := (rows 35 26 21 14 16 32), losses := [{ target := 0, region := (rows 0 6 4 12 16 32), good := (rows 34 26 30 14 16 32) }] }

theorem profile10_node378 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,6] 6 5 profile10_node378_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17,6] 6 5 profile10_node378_cert).mp (by decide +kernel))

def profile10_node375_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node375_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node375 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,17] 6 (by decide) (choices 2) [3,5,6] profile10_node375_route profile10_node375_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node376
  · exact profile10_node377
  · exact profile10_node378

def profile10_node379_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 35 26 22 13 21 37), lower := (rows 35 26 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 38 30 22 8 16 32) }] }

theorem profile10_node379 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,18] 6 5 profile10_node379_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24,18] 6 5 profile10_node379_cert).mp (by decide +kernel))

def profile10_node373_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node373_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node373 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34,24] 6 (by decide) (choices 2) [3,17,18] profile10_node373_route profile10_node373_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node374
  · exact profile10_node375
  · exact profile10_node379

def profile10_node304_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 36 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node304_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node304 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [34] 6 (by decide) (choices 2) [5,9,12,17,20,24] profile10_node304_route profile10_node304_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node305
  · exact profile10_node318
  · exact profile10_node328
  · exact profile10_node341
  · exact profile10_node357
  · exact profile10_node373

def profile10_node382_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 41 7 7 30 22 54), lower := (rows 41 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 40 62 62 8 16 32) }] }

theorem profile10_node382 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,3] 6 22 profile10_node382_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,3] 6 22 profile10_node382_cert).mp (by decide +kernel))

def profile10_node383_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 41 7 21 30 22 54), lower := (rows 41 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 40 62 20 8 16 32) }] }

theorem profile10_node383 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,17] 6 22 profile10_node383_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,17] 6 22 profile10_node383_cert).mp (by decide +kernel))

def profile10_node385_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 41 7 22 11 20 52), lower := (rows 41 7 22 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 31 47), good := (rows 60 54 54 62 16 32) }] }

theorem profile10_node385 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,3] 6 20 profile10_node385_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,3] 6 20 profile10_node385_cert).mp (by decide +kernel))

def profile10_node386_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 41 7 22 13 18 50), lower := (rows 41 7 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 40 54 54 60 16 32) }] }

theorem profile10_node386 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,5] 6 18 profile10_node386_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,5] 6 18 profile10_node386_cert).mp (by decide +kernel))

def profile10_node387_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 41 7 22 14 17 49), lower := (rows 41 7 22 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 32), good := (rows 40 14 30 14 16 32) }] }

theorem profile10_node387 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,6] 6 17 profile10_node387_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,6] 6 17 profile10_node387_cert).mp (by decide +kernel))


#print axioms profile10_node387
end Delivery.SmallBudgetTenFinite6
