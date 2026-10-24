import SmallBudgetTenFinite7Profile034Part002

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile34_node388_cert : Bound 7 := { allowed := (rows 32 80 96 32 0 0 0), upper := (rows 81 38 28 74 49 33 64), lower := (rows 81 38 28 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 33 127), good := (rows 97 110 76 74 64 96 64) }] }

theorem profile34_node388 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,66] 6 33 profile34_node388_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,66] 6 33 profile34_node388_cert).mp (by decide +kernel))

def profile34_node389_cert : Bound 7 := { allowed := (rows 32 80 96 16 0 0 0), upper := (rows 81 38 28 104 19 35 64), lower := (rows 81 38 28 104 16 32 64), losses := [] }

theorem profile34_node389 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,96] 6 3 profile34_node389_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,96] 6 3 profile34_node389_cert).mp (by decide +kernel))

def profile34_node383_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node383_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node383 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile34_node383_route profile34_node383_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node384
  · exact profile34_node385
  · exact profile34_node386
  · exact profile34_node387
  · exact profile34_node388
  · exact profile34_node389

def profile34_node390_cert : CutBound 7 := { lost := (rows 32 16 0 32 0 0 0), upper := (rows 81 38 37 90 90 122 64), lower := (rows 81 38 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 102 103 72 64 96 64) },{ target := 5, region := (rows 19 2 4 10 18 0 127), good := (rows 81 95 69 72 81 64 64) }] }

theorem profile34_node390 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,33] 6 90 profile34_node390_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,33] 6 90 profile34_node390_cert).mp (by decide +kernel))

def profile34_node391_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 38 38 89 89 121 64), lower := (rows 81 38 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 65 102 102 72 64 102 64) }] }

theorem profile34_node391 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,34] 6 89 profile34_node391_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,34] 6 89 profile34_node391_cert).mp (by decide +kernel))

def profile34_node392_cert : CutBound 7 := { lost := (rows 32 16 0 32 0 0 0), upper := (rows 81 38 44 91 83 115 64), lower := (rows 81 38 44 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 102 110 72 64 96 64) },{ target := 5, region := (rows 19 2 4 10 18 0 127), good := (rows 81 95 76 72 81 64 64) }] }

theorem profile34_node392 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,40] 6 83 profile34_node392_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,40] 6 83 profile34_node392_cert).mp (by decide +kernel))

def profile34_node393_cert : Bound 7 := { allowed := (rows 32 64 64 112 0 0 0), upper := (rows 81 38 52 75 91 107 64), lower := (rows 81 38 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 102 102 72 64 96 64) }] }

theorem profile34_node393 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,48] 6 75 profile34_node393_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,48] 6 75 profile34_node393_cert).mp (by decide +kernel))

def profile34_node394_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 38 69 58 58 58 64), lower := (rows 81 38 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 102 69 72 64 96 64) },{ target := 5, region := (rows 17 2 21 8 16 0 127), good := (rows 85 70 69 72 85 64 64) }] }

theorem profile34_node394 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,65] 6 58 profile34_node394_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,65] 6 58 profile34_node394_cert).mp (by decide +kernel))

def profile34_node395_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 38 70 57 57 57 64), lower := (rows 81 38 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 34 38 8 0 32 127), good := (rows 65 102 70 72 64 102 64) }] }

theorem profile34_node395 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,66] 6 57 profile34_node395_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,66] 6 57 profile34_node395_cert).mp (by decide +kernel))

def profile34_node396_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 38 76 59 51 51 64), lower := (rows 81 38 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 65 102 76 76 64 96 64) },{ target := 5, region := (rows 17 2 12 8 16 0 127), good := (rows 81 70 76 76 81 64 64) }] }

theorem profile34_node396 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,72] 6 51 profile34_node396_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,72] 6 51 profile34_node396_cert).mp (by decide +kernel))

def profile34_node397_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 81 38 84 43 59 43 64), lower := (rows 81 38 84 8 16 32 64), losses := [{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile34_node397 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,80] 6 43 profile34_node397_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,80] 6 43 profile34_node397_cert).mp (by decide +kernel))

def profile34_node398_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 38 100 27 27 59 64), lower := (rows 81 38 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 38 38 8 0 32 127), good := (rows 65 102 102 72 64 102 64) }] }

theorem profile34_node398 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,96] 6 27 profile34_node398_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,96] 6 27 profile34_node398_cert).mp (by decide +kernel))

def profile34_node362_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile34_node362_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node362 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36] 6 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96] profile34_node362_route profile34_node362_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node363
  · exact profile34_node367
  · exact profile34_node374
  · exact profile34_node381
  · exact profile34_node382
  · exact profile34_node383
  · exact profile34_node390
  · exact profile34_node391
  · exact profile34_node392
  · exact profile34_node393
  · exact profile34_node394
  · exact profile34_node395
  · exact profile34_node396
  · exact profile34_node397
  · exact profile34_node398

def profile34_node400_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 81 50 7 108 124 108 64), lower := (rows 81 50 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 65 98 111 72 64 96 64) },{ target := 5, region := (rows 19 2 6 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile34_node400 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,3] 6 108 profile34_node400_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,3] 6 108 profile34_node400_cert).mp (by decide +kernel))

def profile34_node402_cert : CutBound 7 := { lost := (rows 32 0 32 32 0 0 0), upper := (rows 81 50 13 14 112 96 64), lower := (rows 81 50 13 14 16 32 64), losses := [{ target := 5, region := (rows 19 2 14 10 16 0 127), good := (rows 81 95 77 79 81 64 64) }] }

theorem profile34_node402 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,6] 6 96 profile34_node402_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,6] 6 96 profile34_node402_cert).mp (by decide +kernel))

def profile34_node403_cert : Bound 7 := { allowed := (rows 32 64 112 64 0 0 0), upper := (rows 81 50 13 42 84 100 64), lower := (rows 81 50 13 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 36 127), good := (rows 65 106 109 106 64 96 64) }] }

theorem profile34_node403 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,34] 6 68 profile34_node403_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,34] 6 68 profile34_node403_cert).mp (by decide +kernel))

def profile34_node404_cert : Bound 7 := { allowed := (rows 0 64 112 80 0 0 0), upper := (rows 81 50 13 44 82 98 64), lower := (rows 81 50 13 44 16 32 64), losses := [{ target := 5, region := (rows 19 2 4 8 18 0 127), good := (rows 81 83 77 76 81 64 64) }] }

theorem profile34_node404 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,36] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,36] 6 66 profile34_node404_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,36] 6 66 profile34_node404_cert).mp (by decide +kernel))

def profile34_node405_cert : Bound 7 := { allowed := (rows 32 64 112 32 0 0 0), upper := (rows 81 50 13 74 52 36 64), lower := (rows 81 50 13 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 36 127), good := (rows 65 106 109 74 64 96 64) }] }

theorem profile34_node405 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,66] 6 36 profile34_node405_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,66] 6 36 profile34_node405_cert).mp (by decide +kernel))

def profile34_node406_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 50 13 76 50 34 64), lower := (rows 81 50 13 76 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 13 0 34 127), good := (rows 77 98 77 76 64 96 64) }] }

theorem profile34_node406 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,68] 6 34 profile34_node406_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,68] 6 34 profile34_node406_cert).mp (by decide +kernel))

def profile34_node407_cert : Bound 7 := { allowed := (rows 32 64 112 16 0 0 0), upper := (rows 81 50 13 104 22 38 64), lower := (rows 81 50 13 104 16 32 64), losses := [] }

theorem profile34_node407 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,96] 6 6 profile34_node407_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9,96] 6 6 profile34_node407_cert).mp (by decide +kernel))

def profile34_node401_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node401_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node401 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,9] 6 (by decide) (choices 2) [6,34,36,66,68,96] profile34_node401_route profile34_node401_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node402
  · exact profile34_node403
  · exact profile34_node404
  · exact profile34_node405
  · exact profile34_node406
  · exact profile34_node407

def profile34_node409_cert : CutBound 7 := { lost := (rows 32 0 32 32 0 0 0), upper := (rows 81 50 14 13 112 96 64), lower := (rows 81 50 14 13 16 32 64), losses := [{ target := 5, region := (rows 19 2 6 14 16 0 127), good := (rows 81 95 79 77 81 64 64) }] }

theorem profile34_node409 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,5] 6 96 profile34_node409_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,5] 6 96 profile34_node409_cert).mp (by decide +kernel))

def profile34_node410_cert : Bound 7 := { allowed := (rows 0 64 112 80 0 0 0), upper := (rows 81 50 14 41 84 100 64), lower := (rows 81 50 14 41 16 32 64), losses := [{ target := 5, region := (rows 23 2 4 8 20 0 127), good := (rows 81 83 95 73 81 64 64) }] }

theorem profile34_node410 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,33] 6 68 profile34_node410_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,33] 6 68 profile34_node410_cert).mp (by decide +kernel))

def profile34_node411_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 50 14 44 81 97 64), lower := (rows 81 50 14 44 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 33 127), good := (rows 97 110 78 108 64 96 64) }] }

theorem profile34_node411 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,36] 6 65 profile34_node411_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,36] 6 65 profile34_node411_cert).mp (by decide +kernel))

def profile34_node412_cert : Bound 7 := { allowed := (rows 32 64 112 32 0 0 0), upper := (rows 81 50 14 73 52 36 64), lower := (rows 81 50 14 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 36 127), good := (rows 73 98 110 73 64 96 64) }] }

theorem profile34_node412 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,65] 6 36 profile34_node412_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,65] 6 36 profile34_node412_cert).mp (by decide +kernel))

def profile34_node413_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 50 14 76 49 33 64), lower := (rows 81 50 14 76 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 14 0 33 127), good := (rows 97 110 78 76 64 96 64) }] }

theorem profile34_node413 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,68] 6 33 profile34_node413_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,68] 6 33 profile34_node413_cert).mp (by decide +kernel))

def profile34_node414_cert : Bound 7 := { allowed := (rows 32 64 112 16 0 0 0), upper := (rows 81 50 14 104 21 37 64), lower := (rows 81 50 14 104 16 32 64), losses := [] }

theorem profile34_node414 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,96] 6 5 profile34_node414_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10,96] 6 5 profile34_node414_cert).mp (by decide +kernel))

def profile34_node408_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node408_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node408 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,10] 6 (by decide) (choices 2) [5,33,36,65,68,96] profile34_node408_route profile34_node408_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node409
  · exact profile34_node410
  · exact profile34_node411
  · exact profile34_node412
  · exact profile34_node413
  · exact profile34_node414

def profile34_node415_cert : Bound 7 := { allowed := (rows 0 64 80 112 0 0 0), upper := (rows 81 50 37 78 94 110 64), lower := (rows 81 50 37 8 16 32 64), losses := [{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 83 69 72 81 64 64) }] }

theorem profile34_node415 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,33] 6 78 profile34_node415_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,33] 6 78 profile34_node415_cert).mp (by decide +kernel))

def profile34_node416_cert : Bound 7 := { allowed := (rows 32 64 64 112 0 0 0), upper := (rows 81 50 38 77 93 109 64), lower := (rows 81 50 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 102 72 64 96 64) }] }

theorem profile34_node416 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,34] 6 77 profile34_node416_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,34] 6 77 profile34_node416_cert).mp (by decide +kernel))

def profile34_node417_cert : Bound 7 := { allowed := (rows 0 64 80 112 0 0 0), upper := (rows 81 50 44 79 87 103 64), lower := (rows 81 50 44 8 16 32 64), losses := [{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 83 76 72 81 64 64) }] }

theorem profile34_node417 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,40] 6 71 profile34_node417_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,40] 6 71 profile34_node417_cert).mp (by decide +kernel))

def profile34_node418_cert : Bound 7 := { allowed := (rows 32 64 32 112 0 0 0), upper := (rows 81 50 69 46 62 46 64), lower := (rows 81 50 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 98 69 72 64 96 64) }] }

theorem profile34_node418 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,65] 6 46 profile34_node418_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,65] 6 46 profile34_node418_cert).mp (by decide +kernel))

def profile34_node419_cert : Bound 7 := { allowed := (rows 32 64 32 112 0 0 0), upper := (rows 81 50 70 45 61 45 64), lower := (rows 81 50 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 102 70 72 64 96 64) }] }

theorem profile34_node419 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,66] 6 45 profile34_node419_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,66] 6 45 profile34_node419_cert).mp (by decide +kernel))

def profile34_node420_cert : Bound 7 := { allowed := (rows 32 64 32 112 0 0 0), upper := (rows 81 50 76 47 55 39 64), lower := (rows 81 50 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 65 98 76 76 64 96 64) }] }

theorem profile34_node420 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,72] 6 39 profile34_node420_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,72] 6 39 profile34_node420_cert).mp (by decide +kernel))

def profile34_node421_cert : Bound 7 := { allowed := (rows 32 64 16 112 0 0 0), upper := (rows 81 50 100 15 31 47 64), lower := (rows 81 50 100 8 16 32 64), losses := [] }

theorem profile34_node421 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,96] 6 15 profile34_node421_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48,96] 6 15 profile34_node421_cert).mp (by decide +kernel))

def profile34_node399_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node399_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node399 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,48] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile34_node399_route profile34_node399_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node400
  · exact profile34_node401
  · exact profile34_node408
  · exact profile34_node415
  · exact profile34_node416
  · exact profile34_node417
  · exact profile34_node418
  · exact profile34_node419
  · exact profile34_node420
  · exact profile34_node421

def profile34_node422_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 81 67 62 62 62 62 64), lower := (rows 81 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 17 19 4 8 16 0 127), good := (rows 83 67 68 72 83 64 64) }] }

theorem profile34_node422 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,65] 6 62 profile34_node422_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,65] 6 62 profile34_node422_cert).mp (by decide +kernel))

def profile34_node423_cert : CutBound 7 := { lost := (rows 32 48 0 0 0 0 0), upper := (rows 81 70 63 59 59 59 64), lower := (rows 81 70 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 32 127), good := (rows 65 70 70 72 64 96 64) },{ target := 5, region := (rows 17 6 4 8 16 0 127), good := (rows 81 70 70 72 81 64 64) }] }

theorem profile34_node423 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,68] 6 59 profile34_node423_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,68] 6 59 profile34_node423_cert).mp (by decide +kernel))

def profile34_node424_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 81 82 47 47 63 47 64), lower := (rows 81 82 4 8 16 32 64), losses := [{ target := 5, region := (rows 19 19 4 8 16 0 127), good := (rows 83 83 68 72 83 64 64) }] }

theorem profile34_node424 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,80] 6 47 profile34_node424_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,80] 6 47 profile34_node424_cert).mp (by decide +kernel))

def profile34_node425_cert : CutBound 7 := { lost := (rows 32 16 0 0 0 0 0), upper := (rows 81 98 63 63 63 63 64), lower := (rows 81 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 127), good := (rows 65 98 68 72 64 98 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 66 68 72 81 64 64) }] }

theorem profile34_node425 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,96] 6 63 profile34_node425_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,96] 6 63 profile34_node425_cert).mp (by decide +kernel))

def profile34_node259_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile34_node259_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile34_node259 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80] 6 (by decide) (choices 2) [5,12,17,20,33,36,48,65,68,80,96] profile34_node259_route profile34_node259_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node260
  · exact profile34_node283
  · exact profile34_node315
  · exact profile34_node316
  · exact profile34_node333
  · exact profile34_node362
  · exact profile34_node399
  · exact profile34_node422
  · exact profile34_node423
  · exact profile34_node424
  · exact profile34_node425

def profile34_node0_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile34_node0_route : Route 7 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 24 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 40 => (18,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (66,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node0 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [] 6 (by decide) (choices 2) [6,18,48,66,80] profile34_node0_route profile34_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile34_node1
  · exact profile34_node80
  · exact profile34_node178
  · exact profile34_node258
  · exact profile34_node259

theorem profile34 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [] 6 := profile34_node0


#print axioms profile34
end Delivery.SmallBudgetTenFinite7
