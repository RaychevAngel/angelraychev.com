import SmallBudgetTenFinite7Profile025Part002

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile25_node388_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 35 22 14 81 97 64), lower := (rows 81 35 22 14 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 80 98 94 78 80 96 64) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 113 117 125 113 113 113) }] }

theorem profile25_node388 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,6] 6 65 profile25_node388_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,6] 6 65 profile25_node388_cert).mp (by decide +kernel))

def profile25_node389_cert : Bound 7 := { allowed := (rows 2 80 64 18 0 0 0), upper := (rows 81 35 22 73 22 38 64), lower := (rows 81 35 22 73 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 22 38 127), good := (rows 80 118 118 72 80 96 64) }] }

theorem profile25_node389 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,65] 6 6 profile25_node389_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,65] 6 6 profile25_node389_cert).mp (by decide +kernel))

def profile25_node390_cert : Bound 7 := { allowed := (rows 2 80 65 16 0 0 0), upper := (rows 81 35 22 74 21 37 64), lower := (rows 81 35 22 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 80 106 94 74 80 96 64) }] }

theorem profile25_node390 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,66] 6 5 profile25_node390_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,66] 6 5 profile25_node390_cert).mp (by decide +kernel))

def profile25_node391_cert : CutBound 7 := { lost := (rows 2 0 0 3 0 0 0), upper := (rows 81 35 22 76 19 35 64), lower := (rows 81 35 22 76 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 127), good := (rows 80 98 94 76 80 96 64) },{ target := 1, region := (rows 21 0 4 12 16 32 127), good := (rows 81 97 93 77 81 96 64) }] }

theorem profile25_node391 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,68] 6 3 profile25_node391_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18,68] 6 3 profile25_node391_cert).mp (by decide +kernel))

def profile25_node385_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node385_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node385 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,18] 6 (by decide) (choices 2) [3,5,6,65,66,68] profile25_node385_route profile25_node385_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node386
  · exact profile25_node387
  · exact profile25_node388
  · exact profile25_node389
  · exact profile25_node390
  · exact profile25_node391

def profile25_node392_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 81 35 69 30 22 54 64), lower := (rows 81 35 69 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 23 8 16 32 127), good := (rows 85 101 69 72 85 96 64) }] }

theorem profile25_node392 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,65] 6 22 profile25_node392_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,65] 6 22 profile25_node392_cert).mp (by decide +kernel))

def profile25_node393_cert : CutBound 7 := { lost := (rows 2 0 1 0 0 0 0), upper := (rows 81 35 70 31 23 55 64), lower := (rows 81 35 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 102 70 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 97 68 72 81 96 64) }] }

theorem profile25_node393 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,66] 6 23 profile25_node393_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,66] 6 23 profile25_node393_cert).mp (by decide +kernel))

def profile25_node394_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 81 35 84 15 23 39 64), lower := (rows 81 35 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) }] }

theorem profile25_node394 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,80] 6 7 profile25_node394_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33,80] 6 7 profile25_node394_cert).mp (by decide +kernel))

def profile25_node382_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node382_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node382 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,33] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node382_route profile25_node382_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node383
  · exact profile25_node384
  · exact profile25_node385
  · exact profile25_node392
  · exact profile25_node393
  · exact profile25_node394

def profile25_node397_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 81 38 7 11 80 112 64), lower := (rows 81 38 7 11 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 118 122 112 112 112) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) }] }

theorem profile25_node397 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,3] 6 80 profile25_node397_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,3] 6 80 profile25_node397_cert).mp (by decide +kernel))

def profile25_node398_cert : CutBound 7 := { lost := (rows 2 1 0 2 0 0 0), upper := (rows 81 38 7 25 82 98 64), lower := (rows 81 38 7 25 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 22 38 127), good := (rows 80 118 118 88 80 96 64) },{ target := 1, region := (rows 25 0 4 25 16 32 127), good := (rows 89 100 77 89 89 96 64) }] }

theorem profile25_node398 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,17] 6 66 profile25_node398_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,17] 6 66 profile25_node398_cert).mp (by decide +kernel))

def profile25_node399_cert : CutBound 7 := { lost := (rows 2 16 16 0 0 0 0), upper := (rows 81 38 7 26 81 97 64), lower := (rows 81 38 7 26 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) },{ target := 4, region := (rows 1 7 5 8 0 37 127), good := (rows 103 102 103 74 64 96 64) }] }

theorem profile25_node399 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,18] 6 65 profile25_node399_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,18] 6 65 profile25_node399_cert).mp (by decide +kernel))

def profile25_node400_cert : CutBound 7 := { lost := (rows 2 1 0 2 0 0 0), upper := (rows 81 38 7 73 18 50 64), lower := (rows 81 38 7 73 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 22 38 127), good := (rows 80 118 118 72 80 96 64) },{ target := 1, region := (rows 17 0 4 29 16 32 127), good := (rows 89 108 77 73 89 96 64) }] }

theorem profile25_node400 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,65] 6 18 profile25_node400_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,65] 6 18 profile25_node400_cert).mp (by decide +kernel))

def profile25_node401_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 38 7 74 17 49 64), lower := (rows 81 38 7 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 80 110 78 74 80 96 64) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) }] }

theorem profile25_node401 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,66] 6 17 profile25_node401_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,66] 6 17 profile25_node401_cert).mp (by decide +kernel))

def profile25_node402_cert : CutBound 7 := { lost := (rows 2 0 0 3 0 0 0), upper := (rows 81 38 7 88 19 35 64), lower := (rows 81 38 7 88 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 25 16 32 127), good := (rows 88 102 78 88 88 96 64) },{ target := 1, region := (rows 25 0 4 25 16 32 127), good := (rows 89 100 77 89 89 96 64) }] }

theorem profile25_node402 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,80] 6 3 profile25_node402_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3,80] 6 3 profile25_node402_cert).mp (by decide +kernel))

def profile25_node396_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node396_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node396 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,3] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node396_route profile25_node396_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node397
  · exact profile25_node398
  · exact profile25_node399
  · exact profile25_node400
  · exact profile25_node401
  · exact profile25_node402

def profile25_node403_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 81 38 21 75 83 99 64), lower := (rows 81 38 21 8 16 32 64), losses := [{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) }] }

theorem profile25_node403 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,17] 6 67 profile25_node403_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,17] 6 67 profile25_node403_cert).mp (by decide +kernel))

def profile25_node406_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 38 22 11 17 96 64), lower := (rows 81 38 22 11 17 32 64), losses := [{ target := 0, region := (rows 0 31 21 8 16 127 127), good := (rows 118 102 118 110 118 96 96) }] }

theorem profile25_node406 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3,1] 6 64 profile25_node406_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3,1] 6 64 profile25_node406_cert).mp (by decide +kernel))

def profile25_node407_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 38 22 11 80 33 64), lower := (rows 81 38 22 11 80 32 64), losses := [{ target := 0, region := (rows 0 34 46 8 127 32 127), good := (rows 80 118 86 94 80 118 80) }] }

theorem profile25_node407 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3,64] 6 1 profile25_node407_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3,64] 6 1 profile25_node407_cert).mp (by decide +kernel))

def profile25_node405_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile25_node405_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node405 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,3] 6 (by decide) (choices 1) [1,64] profile25_node405_route profile25_node405_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile25_node406
  · exact profile25_node407

def profile25_node408_cert : CutBound 7 := { lost := (rows 2 0 0 2 0 0 0), upper := (rows 81 38 22 73 19 35 64), lower := (rows 81 38 22 73 16 32 64), losses := [{ target := 1, region := (rows 21 0 4 31 16 32 127), good := (rows 89 109 93 73 89 96 64) }] }

theorem profile25_node408 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,65] 6 3 profile25_node408_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,65] 6 3 profile25_node408_cert).mp (by decide +kernel))

def profile25_node409_cert : CutBound 7 := { lost := (rows 2 0 0 1 0 0 0), upper := (rows 81 38 22 74 17 33 64), lower := (rows 81 38 22 74 16 32 64), losses := [{ target := 0, region := (rows 0 2 4 14 16 32 127), good := (rows 80 110 94 74 80 96 64) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 117 117 121 113 113 113) }] }

theorem profile25_node409 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,66] 6 1 profile25_node409_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18,66] 6 1 profile25_node409_cert).mp (by decide +kernel))

def profile25_node404_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node404_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node404 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,18] 6 (by decide) (choices 2) [3,65,66] profile25_node404_route profile25_node404_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node405
  · exact profile25_node408
  · exact profile25_node409

def profile25_node410_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 81 38 69 27 19 51 64), lower := (rows 81 38 69 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 21 8 16 32 127), good := (rows 85 100 69 72 85 96 64) }] }

theorem profile25_node410 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,65] 6 19 profile25_node410_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,65] 6 19 profile25_node410_cert).mp (by decide +kernel))

def profile25_node411_cert : CutBound 7 := { lost := (rows 0 1 1 0 0 0 0), upper := (rows 81 38 70 27 19 51 64), lower := (rows 81 38 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 38 8 16 32 127), good := (rows 80 102 70 72 80 102 64) }] }

theorem profile25_node411 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,66] 6 19 profile25_node411_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,66] 6 19 profile25_node411_cert).mp (by decide +kernel))

def profile25_node412_cert : CutBound 7 := { lost := (rows 2 0 3 0 0 0 0), upper := (rows 81 38 84 11 19 35 64), lower := (rows 81 38 84 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 127), good := (rows 84 102 84 72 84 96 64) },{ target := 1, region := (rows 21 0 21 8 16 32 127), good := (rows 85 101 85 72 85 96 64) }] }

theorem profile25_node412 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,80] 6 3 profile25_node412_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36,80] 6 3 profile25_node412_cert).mp (by decide +kernel))

def profile25_node395_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 5 | 96 => 5 | _ => 0

def profile25_node395_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node395 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,36] 6 (by decide) (choices 2) [3,17,18,65,66,80] profile25_node395_route profile25_node395_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node396
  · exact profile25_node403
  · exact profile25_node404
  · exact profile25_node410
  · exact profile25_node411
  · exact profile25_node412

def profile25_node414_cert : CutBound 7 := { lost := (rows 2 0 0 16 0 0 0), upper := (rows 81 50 7 79 87 103 64), lower := (rows 81 50 7 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 113 69 72 81 96 64) },{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 65 98 111 72 64 96 64) }] }

theorem profile25_node414 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,3] 6 71 profile25_node414_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,3] 6 71 profile25_node414_cert).mp (by decide +kernel))

def profile25_node415_cert : CutBound 7 := { lost := (rows 2 0 2 0 0 0 0), upper := (rows 81 50 69 15 23 39 64), lower := (rows 81 50 69 8 16 32 64), losses := [{ target := 1, region := (rows 19 0 23 8 16 32 127), good := (rows 85 117 69 72 85 96 64) }] }

theorem profile25_node415 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,65] 6 7 profile25_node415_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,65] 6 7 profile25_node415_cert).mp (by decide +kernel))

def profile25_node416_cert : CutBound 7 := { lost := (rows 2 0 1 0 0 0 0), upper := (rows 81 50 70 15 23 39 64), lower := (rows 81 50 70 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 127), good := (rows 80 118 70 72 80 96 64) },{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 113 69 72 81 96 64) }] }

theorem profile25_node416 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,66] 6 7 profile25_node416_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48,66] 6 7 profile25_node416_cert).mp (by decide +kernel))

def profile25_node413_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 48 => 4 | 80 => 4 | 96 => 5 | _ => 0

def profile25_node413_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node413 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,48] 6 (by decide) (choices 2) [3,65,66] profile25_node413_route profile25_node413_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile25_node414
  · exact profile25_node415
  · exact profile25_node416

def profile25_node417_cert : CutBound 7 := { lost := (rows 2 16 0 0 0 0 0), upper := (rows 81 67 55 63 55 55 64), lower := (rows 81 67 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 65 68 72 81 96 64) },{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) }] }

theorem profile25_node417 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,65] 6 55 profile25_node417_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,65] 6 55 profile25_node417_cert).mp (by decide +kernel))

def profile25_node418_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 81 70 55 59 51 51 64), lower := (rows 81 70 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 127), good := (rows 80 70 70 72 80 96 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 68 68 72 81 96 64) }] }

theorem profile25_node418 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,68] 6 51 profile25_node418_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,68] 6 51 profile25_node418_cert).mp (by decide +kernel))

def profile25_node419_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 81 82 39 47 55 39 64), lower := (rows 81 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 82 82 68 72 82 96 64) },{ target := 1, region := (rows 19 0 4 8 16 32 127), good := (rows 81 81 68 72 81 96 64) }] }

theorem profile25_node419 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,80] 6 39 profile25_node419_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,80] 6 39 profile25_node419_cert).mp (by decide +kernel))

def profile25_node420_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 81 98 23 31 23 55 64), lower := (rows 81 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 80 98 68 72 80 98 64) },{ target := 1, region := (rows 17 0 4 8 16 32 127), good := (rows 81 96 68 72 81 96 64) }] }

theorem profile25_node420 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,96] 6 23 profile25_node420_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80,96] 6 23 profile25_node420_cert).mp (by decide +kernel))

def profile25_node350_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node350_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node350 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [80] 6 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] profile25_node350_route profile25_node350_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node351
  · exact profile25_node368
  · exact profile25_node369
  · exact profile25_node382
  · exact profile25_node395
  · exact profile25_node413
  · exact profile25_node417
  · exact profile25_node418
  · exact profile25_node419
  · exact profile25_node420

def profile25_node421_cert : CutBound 7 := { lost := (rows 18 0 0 0 0 0 0), upper := (rows 97 87 87 95 87 119 64), lower := (rows 97 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 33 0 4 8 16 32 127), good := (rows 97 64 68 72 80 97 64) },{ target := 4, region := (rows 33 2 4 8 0 32 127), good := (rows 97 66 68 72 64 97 64) }] }

theorem profile25_node421 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [96] 6 87 profile25_node421_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [96] 6 87 profile25_node421_cert).mp (by decide +kernel))

def profile25_node0_column : Nat → Fin 7 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile25_node0_route : Route 7 := (fun mask => (mask,id))

theorem profile25_node0 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [] 6 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96] profile25_node0_route profile25_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile25_node1
  · exact profile25_node52
  · exact profile25_node116
  · exact profile25_node160
  · exact profile25_node200
  · exact profile25_node239
  · exact profile25_node270
  · exact profile25_node349
  · exact profile25_node350
  · exact profile25_node421

theorem profile25 : Upper (D (n:=7) [34,34,33,32,18,17,2]) (R (n:=7) [34,34,33,32,18,17,2]) [] 6 := profile25_node0


#print axioms profile25
end Delivery.SmallBudgetTenFinite7
