import SmallBudgetTenFinite6Profile010Part002

namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile10_node388_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 41 7 22 25 22 38), lower := (rows 41 7 22 25 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 40 54 54 24 16 32) }] }

theorem profile10_node388 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,17] 6 6 profile10_node388_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,17] 6 6 profile10_node388_cert).mp (by decide +kernel))

def profile10_node389_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 41 7 22 26 21 37), lower := (rows 41 7 22 26 16 32), losses := [{ target := 0, region := (rows 0 2 12 12 16 32), good := (rows 44 14 30 30 16 32) }] }

theorem profile10_node389 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,18] 6 5 profile10_node389_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,18] 6 5 profile10_node389_cert).mp (by decide +kernel))

def profile10_node390_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 41 7 22 28 19 35), lower := (rows 41 7 22 28 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 40 14 30 28 16 32) }] }

theorem profile10_node390 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,20] 6 3 profile10_node390_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18,20] 6 3 profile10_node390_cert).mp (by decide +kernel))

def profile10_node384_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node384_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node384 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5,18] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node384_route profile10_node384_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node385
  · exact profile10_node386
  · exact profile10_node387
  · exact profile10_node388
  · exact profile10_node389
  · exact profile10_node390

def profile10_node381_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node381_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node381 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,5] 6 (by decide) (choices 2) [3,17,18] profile10_node381_route profile10_node381_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node382
  · exact profile10_node383
  · exact profile10_node384

def profile10_node392_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 41 19 7 30 22 54), lower := (rows 41 19 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 40 18 62 8 16 32) }] }

theorem profile10_node392 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,3] 6 22 profile10_node392_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,3] 6 22 profile10_node392_cert).mp (by decide +kernel))

def profile10_node393_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 41 19 21 14 22 38), lower := (rows 41 19 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 6 8 16 32), good := (rows 41 21 21 8 16 32) }] }

theorem profile10_node393 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,17] 6 6 profile10_node393_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,17] 6 6 profile10_node393_cert).mp (by decide +kernel))

def profile10_node394_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 41 19 22 15 23 39), lower := (rows 41 19 22 8 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 16 32), good := (rows 40 22 22 8 16 32) }] }

theorem profile10_node394 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,18] 6 7 profile10_node394_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17,18] 6 7 profile10_node394_cert).mp (by decide +kernel))

def profile10_node391_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node391_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node391 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,17] 6 (by decide) (choices 2) [3,17,18] profile10_node391_route profile10_node391_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node392
  · exact profile10_node393
  · exact profile10_node394

def profile10_node397_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 41 22 7 11 20 52), lower := (rows 41 22 7 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 40 54 54 58 16 32) }] }

theorem profile10_node397 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,3] 6 20 profile10_node397_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,3] 6 20 profile10_node397_cert).mp (by decide +kernel))

def profile10_node398_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 41 22 7 13 18 50), lower := (rows 41 22 7 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 31 47), good := (rows 58 54 54 62 16 32) }] }

theorem profile10_node398 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,5] 6 18 profile10_node398_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,5] 6 18 profile10_node398_cert).mp (by decide +kernel))

def profile10_node399_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 41 22 7 14 17 49), lower := (rows 41 22 7 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 16 32), good := (rows 40 30 14 14 16 32) }] }

theorem profile10_node399 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,6] 6 17 profile10_node399_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,6] 6 17 profile10_node399_cert).mp (by decide +kernel))

def profile10_node400_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 41 22 7 25 22 38), lower := (rows 41 22 7 25 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 40 54 54 24 16 32) }] }

theorem profile10_node400 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,17] 6 6 profile10_node400_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,17] 6 6 profile10_node400_cert).mp (by decide +kernel))

def profile10_node401_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 41 22 7 26 21 37), lower := (rows 41 22 7 26 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 40 30 14 26 16 32) }] }

theorem profile10_node401 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,18] 6 5 profile10_node401_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,18] 6 5 profile10_node401_cert).mp (by decide +kernel))

def profile10_node402_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 41 22 7 28 19 35), lower := (rows 41 22 7 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 10 16 32), good := (rows 42 30 14 30 16 32) }] }

theorem profile10_node402 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,20] 6 3 profile10_node402_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3,20] 6 3 profile10_node402_cert).mp (by decide +kernel))

def profile10_node396_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node396_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node396 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,3] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node396_route profile10_node396_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node397
  · exact profile10_node398
  · exact profile10_node399
  · exact profile10_node400
  · exact profile10_node401
  · exact profile10_node402

def profile10_node403_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 41 22 21 15 23 39), lower := (rows 41 22 21 8 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 16 32), good := (rows 40 22 22 8 16 32) }] }

theorem profile10_node403 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,17] 6 7 profile10_node403_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,17] 6 7 profile10_node403_cert).mp (by decide +kernel))

def profile10_node404_cert : CutBound 6 := { lost := (rows 0 1 1 0 0 0), upper := (rows 41 22 22 15 23 39), lower := (rows 41 22 22 8 16 32), losses := [{ target := 0, region := (rows 0 22 22 8 16 32), good := (rows 40 22 22 8 22 32) }] }

theorem profile10_node404 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,18] 6 7 profile10_node404_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20,18] 6 7 profile10_node404_cert).mp (by decide +kernel))

def profile10_node395_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node395_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node395 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40,20] 6 (by decide) (choices 2) [3,17,18] profile10_node395_route profile10_node395_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node396
  · exact profile10_node403
  · exact profile10_node404

def profile10_node380_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 12 => 3 | 36 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node380_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node380 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [40] 6 (by decide) (choices 2) [5,17,20] profile10_node380_route profile10_node380_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node381
  · exact profile10_node391
  · exact profile10_node395

def profile10_node407_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 7 30 30 62), lower := (rows 49 7 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 14 22 38), good := (rows 48 62 62 8 16 32) }] }

theorem profile10_node407 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,3] 6 30 profile10_node407_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,3] 6 30 profile10_node407_cert).mp (by decide +kernel))

def profile10_node408_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 13 30 22 54), lower := (rows 49 7 13 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 12 8 16 32) }] }

theorem profile10_node408 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,9] 6 22 profile10_node408_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,9] 6 22 profile10_node408_cert).mp (by decide +kernel))

def profile10_node410_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 7 14 11 20 52), lower := (rows 49 7 14 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 30 46), good := (rows 48 54 62 62 16 32) }] }

theorem profile10_node410 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,3] 6 20 profile10_node410_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,3] 6 20 profile10_node410_cert).mp (by decide +kernel))

def profile10_node411_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 49 7 14 13 18 50), lower := (rows 49 7 14 13 16 32), losses := [{ target := 1, region := (rows 1 0 4 10 16 32), good := (rows 49 13 12 13 16 32) }] }

theorem profile10_node411 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,5] 6 18 profile10_node411_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,5] 6 18 profile10_node411_cert).mp (by decide +kernel))

def profile10_node412_cert : CutBound 6 := { lost := (rows 0 0 1 1 0 0), upper := (rows 49 7 14 14 17 49), lower := (rows 49 7 14 14 16 32), losses := [{ target := 0, region := (rows 0 2 14 14 16 32), good := (rows 48 14 14 14 16 32) }] }

theorem profile10_node412 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,6] 6 17 profile10_node412_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,6] 6 17 profile10_node412_cert).mp (by decide +kernel))

def profile10_node413_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 49 7 14 25 22 38), lower := (rows 49 7 14 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 57 13 12 25 16 32) }] }

theorem profile10_node413 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,17] 6 6 profile10_node413_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,17] 6 6 profile10_node413_cert).mp (by decide +kernel))

def profile10_node414_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 7 14 26 21 37), lower := (rows 49 7 14 26 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 48 6 14 30 16 32) }] }

theorem profile10_node414 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,18] 6 5 profile10_node414_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,18] 6 5 profile10_node414_cert).mp (by decide +kernel))

def profile10_node415_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 49 7 14 28 19 35), lower := (rows 49 7 14 28 16 32), losses := [{ target := 2, region := (rows 15 2 0 8 22 38), good := (rows 49 51 59 57 16 32) }] }

theorem profile10_node415 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,20] 6 3 profile10_node415_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10,20] 6 3 profile10_node415_cert).mp (by decide +kernel))

def profile10_node409_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node409_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node409 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,10] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node409_route profile10_node409_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node410
  · exact profile10_node411
  · exact profile10_node412
  · exact profile10_node413
  · exact profile10_node414
  · exact profile10_node415

def profile10_node416_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 7 21 14 30 46), lower := (rows 49 7 21 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 18 34), good := (rows 48 62 20 8 16 32) }] }

theorem profile10_node416 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,17] 6 14 profile10_node416_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,17] 6 14 profile10_node416_cert).mp (by decide +kernel))

def profile10_node417_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 7 22 15 31 47), lower := (rows 49 7 22 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 33 47 46 8 0 32) }] }

theorem profile10_node417 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,18] 6 15 profile10_node417_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,18] 6 15 profile10_node417_cert).mp (by decide +kernel))

def profile10_node418_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 7 28 15 23 39), lower := (rows 49 7 28 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 10 0 34), good := (rows 33 47 12 8 0 32) }] }

theorem profile10_node418 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,24] 6 7 profile10_node418_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5,24] 6 7 profile10_node418_cert).mp (by decide +kernel))

def profile10_node406_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node406_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node406 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,5] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile10_node406_route profile10_node406_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node407
  · exact profile10_node408
  · exact profile10_node409
  · exact profile10_node416
  · exact profile10_node417
  · exact profile10_node418

def profile10_node420_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 11 7 30 22 54), lower := (rows 49 11 7 8 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 20 36), good := (rows 48 10 62 8 16 32) }] }

theorem profile10_node420 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,3] 6 22 profile10_node420_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,3] 6 22 profile10_node420_cert).mp (by decide +kernel))

def profile10_node421_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 49 11 21 14 22 38), lower := (rows 49 11 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 13 21 8 16 32) }] }

theorem profile10_node421 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,17] 6 6 profile10_node421_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,17] 6 6 profile10_node421_cert).mp (by decide +kernel))

def profile10_node423_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 11 22 11 20 36), lower := (rows 49 11 22 11 16 32), losses := [{ target := 0, region := (rows 0 2 14 8 30 46), good := (rows 48 62 54 62 16 32) }] }

theorem profile10_node423 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,3] 6 4 profile10_node423_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,3] 6 4 profile10_node423_cert).mp (by decide +kernel))

def profile10_node424_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 11 22 13 22 38), lower := (rows 49 11 22 13 16 32), losses := [{ target := 0, region := (rows 0 2 6 8 22 38), good := (rows 48 62 54 60 16 32) }] }

theorem profile10_node424 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,5] 6 6 profile10_node424_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,5] 6 6 profile10_node424_cert).mp (by decide +kernel))

def profile10_node425_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 11 22 14 21 37), lower := (rows 49 11 22 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 12 16 32), good := (rows 48 10 30 14 16 32) }] }

theorem profile10_node425 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,6] 6 5 profile10_node425_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18,6] 6 5 profile10_node425_cert).mp (by decide +kernel))

def profile10_node422_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node422_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node422 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9,18] 6 (by decide) (choices 2) [3,5,6] profile10_node422_route profile10_node422_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node423
  · exact profile10_node424
  · exact profile10_node425

def profile10_node419_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node419_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node419 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,9] 6 (by decide) (choices 2) [3,17,18] profile10_node419_route profile10_node419_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node420
  · exact profile10_node421
  · exact profile10_node422

def profile10_node428_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 49 14 7 11 20 52), lower := (rows 49 14 7 11 16 32), losses := [{ target := 1, region := (rows 15 0 4 8 22 38), good := (rows 49 61 53 57 16 32) }] }

theorem profile10_node428 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,3] 6 20 profile10_node428_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,3] 6 20 profile10_node428_cert).mp (by decide +kernel))

def profile10_node429_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 14 7 13 18 50), lower := (rows 49 14 7 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 30 46), good := (rows 48 62 54 62 16 32) }] }

theorem profile10_node429 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,5] 6 18 profile10_node429_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,5] 6 18 profile10_node429_cert).mp (by decide +kernel))

def profile10_node430_cert : CutBound 6 := { lost := (rows 0 1 0 1 0 0), upper := (rows 49 14 7 14 17 49), lower := (rows 49 14 7 14 16 32), losses := [{ target := 0, region := (rows 0 14 4 14 16 32), good := (rows 48 14 14 14 16 32) }] }

theorem profile10_node430 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,6] 6 17 profile10_node430_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,6] 6 17 profile10_node430_cert).mp (by decide +kernel))

def profile10_node431_cert : CutBound 6 := { lost := (rows 0 0 0 2 0 0), upper := (rows 49 14 7 25 22 38), lower := (rows 49 14 7 25 16 32), losses := [{ target := 1, region := (rows 1 0 4 9 16 32), good := (rows 57 12 13 25 16 32) }] }

theorem profile10_node431 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,17] 6 6 profile10_node431_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,17] 6 6 profile10_node431_cert).mp (by decide +kernel))

def profile10_node432_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 49 14 7 26 21 37), lower := (rows 49 14 7 26 16 32), losses := [{ target := 1, region := (rows 15 0 4 8 22 38), good := (rows 49 61 53 57 16 32) }] }

theorem profile10_node432 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,18] 6 5 profile10_node432_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,18] 6 5 profile10_node432_cert).mp (by decide +kernel))

def profile10_node433_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 14 7 28 19 35), lower := (rows 49 14 7 28 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 48 14 6 30 16 32) }] }

theorem profile10_node433 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,20] 6 3 profile10_node433_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3,20] 6 3 profile10_node433_cert).mp (by decide +kernel))

def profile10_node427_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | _ => 0

def profile10_node427_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node427 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,3] 6 (by decide) (choices 2) [3,5,6,17,18,20] profile10_node427_route profile10_node427_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node428
  · exact profile10_node429
  · exact profile10_node430
  · exact profile10_node431
  · exact profile10_node432
  · exact profile10_node433

def profile10_node434_cert : CutBound 6 := { lost := (rows 0 0 2 0 0 0), upper := (rows 49 14 21 15 23 39), lower := (rows 49 14 21 8 16 32), losses := [{ target := 1, region := (rows 1 0 5 8 16 32), good := (rows 53 12 21 8 16 32) }] }

theorem profile10_node434 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,17] 6 7 profile10_node434_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,17] 6 7 profile10_node434_cert).mp (by decide +kernel))

def profile10_node436_cert : CutBound 6 := { lost := (rows 2 0 0 0 0 0), upper := (rows 49 14 22 11 21 37), lower := (rows 49 14 22 11 16 32), losses := [{ target := 1, region := (rows 15 0 4 8 22 38), good := (rows 49 61 53 57 16 32) }] }

theorem profile10_node436 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,3] 6 5 profile10_node436_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,3] 6 5 profile10_node436_cert).mp (by decide +kernel))

def profile10_node437_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 14 22 13 19 35), lower := (rows 49 14 22 13 16 32), losses := [{ target := 0, region := (rows 0 10 4 8 16 32), good := (rows 48 14 22 14 16 32) }] }

theorem profile10_node437 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,5] 6 3 profile10_node437_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,5] 6 3 profile10_node437_cert).mp (by decide +kernel))

def profile10_node438_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 49 14 22 14 17 33), lower := (rows 49 14 22 14 16 32), losses := [{ target := 0, region := (rows 0 31 21 31 16 32), good := (rows 62 14 30 14 30 32) }] }

theorem profile10_node438 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,6] 6 1 profile10_node438_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18,6] 6 1 profile10_node438_cert).mp (by decide +kernel))

def profile10_node435_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node435_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node435 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12,18] 6 (by decide) (choices 2) [3,5,6] profile10_node435_route profile10_node435_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node436
  · exact profile10_node437
  · exact profile10_node438

def profile10_node426_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 5 | _ => 0

def profile10_node426_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node426 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,12] 6 (by decide) (choices 2) [3,17,18] profile10_node426_route profile10_node426_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node427
  · exact profile10_node434
  · exact profile10_node435

def profile10_node439_cert : CutBound 6 := { lost := (rows 0 4 0 0 0 0), upper := (rows 49 19 15 15 31 47), lower := (rows 49 19 4 8 16 32), losses := [{ target := 2, region := (rows 1 3 0 8 16 32), good := (rows 51 19 0 8 16 32) }] }

theorem profile10_node439 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,17] 6 15 profile10_node439_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,17] 6 15 profile10_node439_cert).mp (by decide +kernel))

def profile10_node441_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 22 7 15 31 47), lower := (rows 49 22 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 33 46 47 8 0 32) }] }

theorem profile10_node441 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,3] 6 15 profile10_node441_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,3] 6 15 profile10_node441_cert).mp (by decide +kernel))

def profile10_node443_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 22 13 11 22 38), lower := (rows 49 22 13 11 16 32), losses := [{ target := 0, region := (rows 0 6 4 8 22 38), good := (rows 48 54 62 58 16 32) }] }

theorem profile10_node443 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,3] 6 6 profile10_node443_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,3] 6 6 profile10_node443_cert).mp (by decide +kernel))

def profile10_node444_cert : CutBound 6 := { lost := (rows 0 1 0 0 0 0), upper := (rows 49 22 13 13 18 34), lower := (rows 49 22 13 13 16 32), losses := [{ target := 0, region := (rows 0 14 4 8 30 46), good := (rows 48 54 62 62 16 32) }] }

theorem profile10_node444 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,5] 6 2 profile10_node444_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,5] 6 2 profile10_node444_cert).mp (by decide +kernel))

def profile10_node445_cert : CutBound 6 := { lost := (rows 0 0 0 1 0 0), upper := (rows 49 22 13 14 19 35), lower := (rows 49 22 13 14 16 32), losses := [{ target := 0, region := (rows 0 2 4 10 16 32), good := (rows 48 30 12 14 16 32) }] }

theorem profile10_node445 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,6] 6 3 profile10_node445_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9,6] 6 3 profile10_node445_cert).mp (by decide +kernel))

def profile10_node442_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node442_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node442 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,9] 6 (by decide) (choices 2) [3,5,6] profile10_node442_route profile10_node442_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node443
  · exact profile10_node444
  · exact profile10_node445

def profile10_node447_cert : CutBound 6 := { lost := (rows 0 0 1 0 0 0), upper := (rows 49 22 14 11 21 37), lower := (rows 49 22 14 11 16 32), losses := [{ target := 0, region := (rows 0 2 12 8 16 32), good := (rows 48 22 14 14 16 32) }] }

theorem profile10_node447 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,3] 6 5 profile10_node447_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,3] 6 5 profile10_node447_cert).mp (by decide +kernel))

def profile10_node448_cert : CutBound 6 := { lost := (rows 4 0 0 0 0 0), upper := (rows 49 22 14 13 19 35), lower := (rows 49 22 14 13 16 32), losses := [{ target := 2, region := (rows 15 2 0 8 22 38), good := (rows 49 51 59 57 16 32) }] }

theorem profile10_node448 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,5] 6 3 profile10_node448_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,5] 6 3 profile10_node448_cert).mp (by decide +kernel))

def profile10_node449_cert : CutBound 6 := { lost := (rows 0 1 1 1 0 0), upper := (rows 49 22 14 14 17 33), lower := (rows 49 22 14 14 16 32), losses := [{ target := 0, region := (rows 0 19 31 31 16 32), good := (rows 62 30 14 14 30 32) }] }

theorem profile10_node449 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,6] 6 1 profile10_node449_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10,6] 6 1 profile10_node449_cert).mp (by decide +kernel))

def profile10_node446_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | _ => 0

def profile10_node446_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node446 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20,10] 6 (by decide) (choices 2) [3,5,6] profile10_node446_route profile10_node446_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node447
  · exact profile10_node448
  · exact profile10_node449

def profile10_node440_column : Nat → Fin 6 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 24 => 4 | 40 => 5 | 48 => 4 | _ => 0

def profile10_node440_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node440 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,20] 6 (by decide) (choices 2) [3,9,10] profile10_node440_route profile10_node440_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile10_node441
  · exact profile10_node442
  · exact profile10_node446

def profile10_node451_cert : CutBound 6 := { lost := (rows 0 0 0 16 0 0), upper := (rows 49 26 7 15 23 39), lower := (rows 49 26 7 8 16 32), losses := [{ target := 4, region := (rows 1 2 4 12 0 36), good := (rows 33 10 47 8 0 32) }] }

theorem profile10_node451 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,24,3] 6 7 profile10_node451_cert
    ((DegreeLoss.cutCheck_true (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,24,3] 6 7 profile10_node451_cert).mp (by decide +kernel))

def profile10_node450_column : Nat → Fin 6 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 48 => 4 | _ => 0

def profile10_node450_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node450 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,24] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48,24] 6 (by decide) (choices 2) [3] profile10_node450_route profile10_node450_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node451

def profile10_node405_column : Nat → Fin 6 := fun mask => match mask with | 33 => 5 | 36 => 5 | 40 => 5 | 48 => 5 | _ => 0

def profile10_node405_route : Route 6 := (fun mask => (mask,id))

theorem profile10_node405 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [48] 6 (by decide) (choices 2) [5,9,12,17,20,24] profile10_node405_route profile10_node405_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node406
  · exact profile10_node419
  · exact profile10_node426
  · exact profile10_node439
  · exact profile10_node440
  · exact profile10_node450

def profile10_node0_column : Nat → Fin 6 := fun mask => match mask with | _ => 0

def profile10_node0_route : Route 6 := (fun mask => match mask with | 12 => (10,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | _ => (mask,id))

theorem profile10_node0 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [] 6 (by decide) (choices 2) [6,10,18,24,34,40,48] profile10_node0_route profile10_node0_column
    (by change RowCover 6 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile10_node1
  · exact profile10_node85
  · exact profile10_node161
  · exact profile10_node257
  · exact profile10_node304
  · exact profile10_node380
  · exact profile10_node405

theorem profile10 : Upper (D (n:=6) [34,34,34,33,18,17]) (R (n:=6) [34,34,34,33,18,17]) [] 6 := profile10_node0


#print axioms profile10
end Delivery.SmallBudgetTenFinite6
