import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile40_node2_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 11 117 121 113 113 113), lower := (rows 11 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 7 0 19 35 67), good := (rows 119 119 4 0 16 32 64) }] }

theorem profile40_node2 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,9] 6 113 profile40_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,9] 6 113 profile40_node2_cert).mp (by decide +kernel))

def profile40_node4_cert : Bound 7 := { allowed := (rows 48 40 48 0 0 0 0), upper := (rows 11 19 13 120 112 112 112), lower := (rows 11 19 13 8 16 32 64), losses := [] }

theorem profile40_node4 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,9] 6 112 profile40_node4_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,9] 6 112 profile40_node4_cert).mp (by decide +kernel))

def profile40_node5_cert : Bound 7 := { allowed := (rows 48 40 40 0 0 0 0), upper := (rows 11 19 21 104 120 104 104), lower := (rows 11 19 21 8 16 32 64), losses := [] }

theorem profile40_node5 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,17] 6 104 profile40_node5_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,17] 6 104 profile40_node5_cert).mp (by decide +kernel))

def profile40_node6_cert : Bound 7 := { allowed := (rows 48 40 33 0 0 0 0), upper := (rows 11 19 28 105 113 97 97), lower := (rows 11 19 28 8 16 32 64), losses := [] }

theorem profile40_node6 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,24] 6 97 profile40_node6_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,24] 6 97 profile40_node6_cert).mp (by decide +kernel))

def profile40_node7_cert : Bound 7 := { allowed := (rows 48 40 24 0 0 0 0), upper := (rows 11 19 37 120 120 120 120), lower := (rows 11 19 37 8 16 32 64), losses := [] }

theorem profile40_node7 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,33] 6 120 profile40_node7_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,33] 6 120 profile40_node7_cert).mp (by decide +kernel))

def profile40_node8_cert : Bound 7 := { allowed := (rows 48 40 17 0 0 0 0), upper := (rows 11 19 44 121 113 113 113), lower := (rows 11 19 44 8 16 32 64), losses := [] }

theorem profile40_node8 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,40] 6 113 profile40_node8_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,40] 6 113 profile40_node8_cert).mp (by decide +kernel))

def profile40_node9_cert : Bound 7 := { allowed := (rows 48 40 9 0 0 0 0), upper := (rows 11 19 52 105 121 105 105), lower := (rows 11 19 52 8 16 32 64), losses := [] }

theorem profile40_node9 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,48] 6 105 profile40_node9_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,48] 6 105 profile40_node9_cert).mp (by decide +kernel))

def profile40_node11_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 11 19 69 24 56 40 104), lower := (rows 11 19 69 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 8 0 41 73), good := (rows 111 103 101 104 0 32 64) }] }

theorem profile40_node11 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,16] 6 40 profile40_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,16] 6 40 profile40_node11_cert).mp (by decide +kernel))

def profile40_node13_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 19 69 40 24 48 112), lower := (rows 11 19 69 40 24 32 64), losses := [{ target := 3, region := (rows 1 2 7 0 16 50 82), good := (rows 103 119 69 32 112 32 64) }] }

theorem profile40_node13 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32,8] 6 48 profile40_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32,8] 6 48 profile40_node13_cert).mp (by decide +kernel))

def profile40_node14_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 19 69 40 48 56 88), lower := (rows 11 19 69 40 48 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 56 32 64), good := (rows 19 19 71 48 48 48 64) }] }

theorem profile40_node14 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32,32] 6 24 profile40_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32,32] 6 24 profile40_node14_cert).mp (by decide +kernel))

def profile40_node12_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node12_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node12 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65,32] 6 (by decide) (choices 1) [8,32] profile40_node12_route profile40_node12_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node13
  · exact profile40_node14

def profile40_node10_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node10_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node10 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,65] 6 (by decide) (choices 1) [16,32] profile40_node10_route profile40_node10_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node11
  · exact profile40_node12

def profile40_node15_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 19 76 57 49 49 113), lower := (rows 11 19 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 68 0 16 32 64) }] }

theorem profile40_node15 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,72] 6 49 profile40_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,72] 6 49 profile40_node15_cert).mp (by decide +kernel))

def profile40_node16_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 11 19 84 41 57 41 105), lower := (rows 11 19 84 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 67), good := (rows 107 107 68 8 0 32 64) }] }

theorem profile40_node16 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,80] 6 41 profile40_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,80] 6 41 profile40_node16_cert).mp (by decide +kernel))

def profile40_node18_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 11 19 100 9 56 56 120), lower := (rows 11 19 100 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 25 41 73), good := (rows 126 118 100 124 16 32 64) }] }

theorem profile40_node18 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,1] 6 56 profile40_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,1] 6 56 profile40_node18_cert).mp (by decide +kernel))

def profile40_node19_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 11 19 100 24 57 41 105), lower := (rows 11 19 100 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 8 0 33 65), good := (rows 111 103 100 8 0 32 64) }] }

theorem profile40_node19 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,16] 6 41 profile40_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,16] 6 41 profile40_node19_cert).mp (by decide +kernel))

def profile40_node20_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 11 19 100 40 25 57 89), lower := (rows 11 19 100 40 16 32 64), losses := [{ target := 5, region := (rows 9 11 4 8 25 0 73), good := (rows 91 83 68 91 16 0 64) }] }

theorem profile40_node20 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,32] 6 25 profile40_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96,32] 6 25 profile40_node20_cert).mp (by decide +kernel))

def profile40_node17_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node17_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node17 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17,96] 6 (by decide) (choices 1) [1,16,32] profile40_node17_route profile40_node17_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node18
  · exact profile40_node19
  · exact profile40_node20

def profile40_node3_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile40_node3_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node3 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,17] 6 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96] profile40_node3_route profile40_node3_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node4
  · exact profile40_node5
  · exact profile40_node6
  · exact profile40_node7
  · exact profile40_node8
  · exact profile40_node9
  · exact profile40_node10
  · exact profile40_node15
  · exact profile40_node16
  · exact profile40_node17

def profile40_node21_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 26 117 121 113 113 113), lower := (rows 11 26 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 119 18 4 0 16 32 64) }] }

theorem profile40_node21 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,24] 6 113 profile40_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,24] 6 113 profile40_node21_cert).mp (by decide +kernel))

def profile40_node23_cert : Bound 7 := { allowed := (rows 48 9 48 0 0 0 0), upper := (rows 11 50 13 121 113 113 113), lower := (rows 11 50 13 8 16 32 64), losses := [] }

theorem profile40_node23 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,9] 6 113 profile40_node23_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,9] 6 113 profile40_node23_cert).mp (by decide +kernel))

def profile40_node24_cert : Bound 7 := { allowed := (rows 48 9 40 0 0 0 0), upper := (rows 11 50 21 105 121 105 105), lower := (rows 11 50 21 8 16 32 64), losses := [] }

theorem profile40_node24 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,17] 6 105 profile40_node24_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,17] 6 105 profile40_node24_cert).mp (by decide +kernel))

def profile40_node25_cert : Bound 7 := { allowed := (rows 48 9 33 0 0 0 0), upper := (rows 11 50 28 105 113 97 97), lower := (rows 11 50 28 8 16 32 64), losses := [] }

theorem profile40_node25 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,24] 6 97 profile40_node25_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,24] 6 97 profile40_node25_cert).mp (by decide +kernel))

def profile40_node26_cert : Bound 7 := { allowed := (rows 48 9 9 0 0 0 0), upper := (rows 11 50 52 73 89 105 73), lower := (rows 11 50 52 8 16 32 64), losses := [] }

theorem profile40_node26 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,48] 6 73 profile40_node26_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,48] 6 73 profile40_node26_cert).mp (by decide +kernel))

def profile40_node28_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 11 50 69 9 56 56 120), lower := (rows 11 50 69 9 16 32 64), losses := [{ target := 0, region := (rows 0 15 4 8 25 41 73), good := (rows 122 50 118 122 16 32 64) }] }

theorem profile40_node28 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65,1] 6 56 profile40_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65,1] 6 56 profile40_node28_cert).mp (by decide +kernel))

def profile40_node29_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 11 50 69 24 57 41 105), lower := (rows 11 50 69 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 33 65), good := (rows 111 34 101 8 0 32 64) }] }

theorem profile40_node29 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65,16] 6 41 profile40_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65,16] 6 41 profile40_node29_cert).mp (by decide +kernel))

def profile40_node27_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node27_route : Route 7 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node27 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,65] 6 (by decide) (choices 1) [1,16] profile40_node27_route profile40_node27_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node28
  · exact profile40_node29

def profile40_node30_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 50 76 57 49 49 113), lower := (rows 11 50 76 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 50 68 0 16 32 64) }] }

theorem profile40_node30 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,72] 6 49 profile40_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,72] 6 49 profile40_node30_cert).mp (by decide +kernel))

def profile40_node31_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 11 50 84 41 57 41 105), lower := (rows 11 50 84 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 67), good := (rows 107 107 68 8 0 32 64) }] }

theorem profile40_node31 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,80] 6 41 profile40_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48,80] 6 41 profile40_node31_cert).mp (by decide +kernel))

def profile40_node22_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile40_node22_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node22 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,48] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile40_node22_route profile40_node22_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node23
  · exact profile40_node24
  · exact profile40_node25
  · exact profile40_node26
  · exact profile40_node27
  · exact profile40_node30
  · exact profile40_node31

def profile40_node33_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 67 13 56 48 48 112), lower := (rows 11 67 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 7 4 0 127 127 127), good := (rows 115 115 119 112 112 112 112) }] }

theorem profile40_node33 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,9] 6 48 profile40_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,9] 6 48 profile40_node33_cert).mp (by decide +kernel))

def profile40_node35_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 11 67 21 24 56 40 104), lower := (rows 11 67 21 24 16 32 64), losses := [{ target := 4, region := (rows 9 15 4 8 0 41 73), good := (rows 107 99 103 107 0 32 64) }] }

theorem profile40_node35 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,16] 6 40 profile40_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,16] 6 40 profile40_node35_cert).mp (by decide +kernel))

def profile40_node37_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 67 21 40 24 48 112), lower := (rows 11 67 21 40 24 32 64), losses := [{ target := 3, region := (rows 1 6 4 0 16 52 84), good := (rows 3 67 119 32 112 32 64) }] }

theorem profile40_node37 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32,8] 6 48 profile40_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32,8] 6 48 profile40_node37_cert).mp (by decide +kernel))

def profile40_node38_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 67 21 40 48 56 88), lower := (rows 11 67 21 40 48 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 56 32 64), good := (rows 23 71 21 48 48 48 64) }] }

theorem profile40_node38 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32,32] 6 24 profile40_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32,32] 6 24 profile40_node38_cert).mp (by decide +kernel))

def profile40_node36_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node36_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node36 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17,32] 6 (by decide) (choices 1) [8,32] profile40_node36_route profile40_node36_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node37
  · exact profile40_node38

def profile40_node34_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node34_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node34 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,17] 6 (by decide) (choices 1) [16,32] profile40_node34_route profile40_node34_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node35
  · exact profile40_node36

def profile40_node39_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 67 28 57 49 49 113), lower := (rows 11 67 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 20 0 16 32 64) }] }

theorem profile40_node39 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,24] 6 49 profile40_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,24] 6 49 profile40_node39_cert).mp (by decide +kernel))

def profile40_node41_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 11 67 52 9 56 56 120), lower := (rows 11 67 52 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 15 8 25 41 73), good := (rows 126 118 52 124 16 32 64) }] }

theorem profile40_node41 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48,1] 6 56 profile40_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48,1] 6 56 profile40_node41_cert).mp (by decide +kernel))

def profile40_node42_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 11 67 52 24 57 41 105), lower := (rows 11 67 52 24 16 32 64), losses := [{ target := 4, region := (rows 9 11 4 8 0 41 73), good := (rows 107 99 36 107 0 32 64) }] }

theorem profile40_node42 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48,16] 6 41 profile40_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48,16] 6 41 profile40_node42_cert).mp (by decide +kernel))

def profile40_node40_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node40_route : Route 7 := (fun mask => match mask with | 32 => (16,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node40 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65,48] 6 (by decide) (choices 1) [1,16] profile40_node40_route profile40_node40_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node41
  · exact profile40_node42

def profile40_node32_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node32_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node32 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,65] 6 (by decide) (choices 2) [9,17,24,48] profile40_node32_route profile40_node32_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile40_node33
  · exact profile40_node34
  · exact profile40_node39
  · exact profile40_node40

def profile40_node43_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 11 74 53 57 49 49 113), lower := (rows 11 74 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65), good := (rows 119 66 4 0 16 32 64) }] }

theorem profile40_node43 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,72] 6 49 profile40_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,72] 6 49 profile40_node43_cert).mp (by decide +kernel))

def profile40_node45_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 82 13 57 49 49 113), lower := (rows 11 82 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 7 4 0 21 37 69), good := (rows 115 82 119 0 16 32 64) }] }

theorem profile40_node45 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,9] 6 49 profile40_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,9] 6 49 profile40_node45_cert).mp (by decide +kernel))

def profile40_node46_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 11 82 21 41 57 41 105), lower := (rows 11 82 21 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 15 0 39 71), good := (rows 107 107 109 8 0 32 64) }] }

theorem profile40_node46 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,17] 6 41 profile40_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,17] 6 41 profile40_node46_cert).mp (by decide +kernel))

def profile40_node47_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 82 28 41 49 33 97), lower := (rows 11 82 28 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 82 20 0 16 32 64) }] }

theorem profile40_node47 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,24] 6 33 profile40_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,24] 6 33 profile40_node47_cert).mp (by decide +kernel))

def profile40_node49_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 11 82 37 9 56 56 120), lower := (rows 11 82 37 9 16 32 64), losses := [{ target := 0, region := (rows 0 15 4 8 25 41 73), good := (rows 122 82 118 122 16 32 64) }] }

theorem profile40_node49 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,1] 6 56 profile40_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,1] 6 56 profile40_node49_cert).mp (by decide +kernel))

def profile40_node50_cert : CutBound 7 := { lost := (rows 0 0 16 0 0 0 0), upper := (rows 11 82 37 24 57 41 105), lower := (rows 11 82 37 24 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 33 65), good := (rows 111 66 101 8 0 32 64) }] }

theorem profile40_node50 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,16] 6 41 profile40_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,16] 6 41 profile40_node50_cert).mp (by decide +kernel))

def profile40_node51_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 11 82 37 40 25 57 89), lower := (rows 11 82 37 40 16 32 64), losses := [{ target := 5, region := (rows 9 15 4 8 25 0 73), good := (rows 91 82 87 91 16 0 64) }] }

theorem profile40_node51 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,32] 6 25 profile40_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33,32] 6 25 profile40_node51_cert).mp (by decide +kernel))

def profile40_node48_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node48_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node48 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,33] 6 (by decide) (choices 1) [1,16,32] profile40_node48_route profile40_node48_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node49
  · exact profile40_node50
  · exact profile40_node51

def profile40_node52_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 11 82 44 57 49 49 113), lower := (rows 11 82 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 82 36 0 16 32 64) }] }

theorem profile40_node52 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,40] 6 49 profile40_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,40] 6 49 profile40_node52_cert).mp (by decide +kernel))

def profile40_node53_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 11 82 52 41 57 41 105), lower := (rows 11 82 52 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 11 0 35 67), good := (rows 107 107 36 8 0 32 64) }] }

theorem profile40_node53 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,48] 6 41 profile40_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80,48] 6 41 profile40_node53_cert).mp (by decide +kernel))

def profile40_node44_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node44_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node44 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10,80] 6 (by decide) (choices 2) [9,17,24,33,40,48] profile40_node44_route profile40_node44_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node45
  · exact profile40_node46
  · exact profile40_node47
  · exact profile40_node48
  · exact profile40_node52
  · exact profile40_node53

def profile40_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile40_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile40_node1 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [10] 6 (by decide) (choices 2) [9,17,24,48,65,72,80] profile40_node1_route profile40_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node2
  · exact profile40_node3
  · exact profile40_node21
  · exact profile40_node22
  · exact profile40_node32
  · exact profile40_node43
  · exact profile40_node44

def profile40_node55_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 11 119 123 115 115 115), lower := (rows 25 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 18 34 66), good := (rows 17 119 4 0 16 32 64) }] }

theorem profile40_node55 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,9] 6 115 profile40_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,9] 6 115 profile40_node55_cert).mp (by decide +kernel))

def profile40_node56_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 25 26 103 107 115 99 99), lower := (rows 25 26 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 64), good := (rows 26 26 4 8 16 32 64) }] }

theorem profile40_node56 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,24] 6 99 profile40_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,24] 6 99 profile40_node56_cert).mp (by decide +kernel))

def profile40_node58_cert : Bound 7 := { allowed := (rows 32 24 56 0 0 0 0), upper := (rows 25 35 7 120 120 120 120), lower := (rows 25 35 7 8 16 32 64), losses := [] }

theorem profile40_node58 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,3] 6 120 profile40_node58_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,3] 6 120 profile40_node58_cert).mp (by decide +kernel))

def profile40_node59_cert : Bound 7 := { allowed := (rows 32 24 48 0 0 0 0), upper := (rows 25 35 13 122 114 114 114), lower := (rows 25 35 13 8 16 32 64), losses := [] }

theorem profile40_node59 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,9] 6 114 profile40_node59_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,9] 6 114 profile40_node59_cert).mp (by decide +kernel))

def profile40_node60_cert : Bound 7 := { allowed := (rows 32 24 49 0 0 0 0), upper := (rows 25 35 14 121 113 113 113), lower := (rows 25 35 14 8 16 32 64), losses := [] }

theorem profile40_node60 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,10] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,10] 6 113 profile40_node60_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,10] 6 113 profile40_node60_cert).mp (by decide +kernel))

def profile40_node61_cert : Bound 7 := { allowed := (rows 32 24 33 0 0 0 0), upper := (rows 25 35 28 107 115 99 99), lower := (rows 25 35 28 8 16 32 64), losses := [] }

theorem profile40_node61 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,24] 6 99 profile40_node61_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,24] 6 99 profile40_node61_cert).mp (by decide +kernel))

def profile40_node62_cert : Bound 7 := { allowed := (rows 32 24 24 0 0 0 0), upper := (rows 25 35 37 90 90 122 90), lower := (rows 25 35 37 8 16 32 64), losses := [] }

theorem profile40_node62 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,33] 6 90 profile40_node62_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,33] 6 90 profile40_node62_cert).mp (by decide +kernel))

def profile40_node63_cert : Bound 7 := { allowed := (rows 32 24 25 0 0 0 0), upper := (rows 25 35 38 89 89 121 89), lower := (rows 25 35 38 8 16 32 64), losses := [] }

theorem profile40_node63 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,34] 6 89 profile40_node63_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,34] 6 89 profile40_node63_cert).mp (by decide +kernel))

def profile40_node64_cert : Bound 7 := { allowed := (rows 32 24 17 0 0 0 0), upper := (rows 25 35 44 91 83 115 83), lower := (rows 25 35 44 8 16 32 64), losses := [] }

theorem profile40_node64 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,40] 6 83 profile40_node64_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,40] 6 83 profile40_node64_cert).mp (by decide +kernel))

def profile40_node65_cert : Bound 7 := { allowed := (rows 32 24 56 0 0 0 0), upper := (rows 25 35 69 58 58 58 122), lower := (rows 25 35 69 8 16 32 64), losses := [] }

theorem profile40_node65 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,65] 6 58 profile40_node65_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,65] 6 58 profile40_node65_cert).mp (by decide +kernel))

def profile40_node67_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 25 35 70 9 56 56 120), lower := (rows 25 35 70 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 25 41 73), good := (rows 120 118 70 120 16 32 64) }] }

theorem profile40_node67 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,1] 6 56 profile40_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,1] 6 56 profile40_node67_cert).mp (by decide +kernel))

def profile40_node68_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 35 70 24 57 41 105), lower := (rows 25 35 70 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 33 65), good := (rows 111 103 70 8 0 32 64) }] }

theorem profile40_node68 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,16] 6 41 profile40_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,16] 6 41 profile40_node68_cert).mp (by decide +kernel))

def profile40_node69_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 25 35 70 40 25 57 89), lower := (rows 25 35 70 40 16 32 64), losses := [{ target := 5, region := (rows 9 2 6 8 25 0 73), good := (rows 89 87 70 89 16 0 64) }] }

theorem profile40_node69 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,32] 6 25 profile40_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66,32] 6 25 profile40_node69_cert).mp (by decide +kernel))

def profile40_node66_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node66_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node66 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,66] 6 (by decide) (choices 1) [1,16,32] profile40_node66_route profile40_node66_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node67
  · exact profile40_node68
  · exact profile40_node69

def profile40_node70_cert : Bound 7 := { allowed := (rows 32 24 49 0 0 0 0), upper := (rows 25 35 76 59 51 51 115), lower := (rows 25 35 76 8 16 32 64), losses := [] }

theorem profile40_node70 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,72] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,72] 6 51 profile40_node70_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,72] 6 51 profile40_node70_cert).mp (by decide +kernel))

def profile40_node71_cert : Bound 7 := { allowed := (rows 32 24 25 0 0 0 0), upper := (rows 25 35 100 27 27 59 91), lower := (rows 25 35 100 8 16 32 64), losses := [] }

theorem profile40_node71 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,96] 6 27 profile40_node71_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33,96] 6 27 profile40_node71_cert).mp (by decide +kernel))

def profile40_node57_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile40_node57_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile40_node57 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,33] 6 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96] profile40_node57_route profile40_node57_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node58
  · exact profile40_node59
  · exact profile40_node60
  · exact profile40_node61
  · exact profile40_node62
  · exact profile40_node63
  · exact profile40_node64
  · exact profile40_node65
  · exact profile40_node66
  · exact profile40_node70
  · exact profile40_node71

def profile40_node73_cert : Bound 7 := { allowed := (rows 32 17 56 0 0 0 0), upper := (rows 25 42 7 121 113 113 113), lower := (rows 25 42 7 8 16 32 64), losses := [] }

theorem profile40_node73 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,3] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,3] 6 113 profile40_node73_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,3] 6 113 profile40_node73_cert).mp (by decide +kernel))

def profile40_node74_cert : Bound 7 := { allowed := (rows 32 17 40 0 0 0 0), upper := (rows 25 42 21 107 115 99 99), lower := (rows 25 42 21 8 16 32 64), losses := [] }

theorem profile40_node74 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,17] 6 99 profile40_node74_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,17] 6 99 profile40_node74_cert).mp (by decide +kernel))

def profile40_node75_cert : Bound 7 := { allowed := (rows 32 17 41 0 0 0 0), upper := (rows 25 42 22 105 113 97 97), lower := (rows 25 42 22 8 16 32 64), losses := [] }

theorem profile40_node75 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,18] 6 97 profile40_node75_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,18] 6 97 profile40_node75_cert).mp (by decide +kernel))

def profile40_node76_cert : Bound 7 := { allowed := (rows 32 17 24 0 0 0 0), upper := (rows 25 42 37 91 83 115 83), lower := (rows 25 42 37 8 16 32 64), losses := [] }

theorem profile40_node76 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,33] 6 83 profile40_node76_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,33] 6 83 profile40_node76_cert).mp (by decide +kernel))

def profile40_node77_cert : Bound 7 := { allowed := (rows 32 17 25 0 0 0 0), upper := (rows 25 42 38 89 81 113 81), lower := (rows 25 42 38 8 16 32 64), losses := [] }

theorem profile40_node77 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,34] 6 81 profile40_node77_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,34] 6 81 profile40_node77_cert).mp (by decide +kernel))

def profile40_node78_cert : Bound 7 := { allowed := (rows 32 17 9 0 0 0 0), upper := (rows 25 42 52 75 83 99 67), lower := (rows 25 42 52 8 16 32 64), losses := [] }

theorem profile40_node78 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,48] 6 67 profile40_node78_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,48] 6 67 profile40_node78_cert).mp (by decide +kernel))

def profile40_node79_cert : Bound 7 := { allowed := (rows 32 17 56 0 0 0 0), upper := (rows 25 42 69 59 51 51 115), lower := (rows 25 42 69 8 16 32 64), losses := [] }

theorem profile40_node79 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,65] 6 51 profile40_node79_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,65] 6 51 profile40_node79_cert).mp (by decide +kernel))

def profile40_node81_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 42 70 9 49 49 113), lower := (rows 25 42 70 9 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 25 41 73), good := (rows 113 118 70 113 16 32 64) }] }

theorem profile40_node81 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,1] 6 49 profile40_node81_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,1] 6 49 profile40_node81_cert).mp (by decide +kernel))

def profile40_node82_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 42 70 24 49 33 97), lower := (rows 25 42 70 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 33 65), good := (rows 111 42 70 8 0 32 64) }] }

theorem profile40_node82 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,16] 6 33 profile40_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,16] 6 33 profile40_node82_cert).mp (by decide +kernel))

def profile40_node83_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 25 42 70 40 17 49 81), lower := (rows 25 42 70 40 16 32 64), losses := [{ target := 0, region := (rows 0 42 4 42 16 32 64), good := (rows 26 42 78 42 16 42 64) }] }

theorem profile40_node83 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,32] 6 17 profile40_node83_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66,32] 6 17 profile40_node83_cert).mp (by decide +kernel))

def profile40_node80_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node80_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node80 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,66] 6 (by decide) (choices 1) [1,16,32] profile40_node80_route profile40_node80_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node81
  · exact profile40_node82
  · exact profile40_node83

def profile40_node84_cert : Bound 7 := { allowed := (rows 32 17 41 0 0 0 0), upper := (rows 25 42 84 43 51 35 99), lower := (rows 25 42 84 8 16 32 64), losses := [] }

theorem profile40_node84 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,80] 6 35 profile40_node84_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,80] 6 35 profile40_node84_cert).mp (by decide +kernel))

def profile40_node85_cert : Bound 7 := { allowed := (rows 32 17 25 0 0 0 0), upper := (rows 25 42 100 27 19 51 83), lower := (rows 25 42 100 8 16 32 64), losses := [] }

theorem profile40_node85 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,96] 6 19 profile40_node85_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40,96] 6 19 profile40_node85_cert).mp (by decide +kernel))

def profile40_node72_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile40_node72_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node72 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,40] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile40_node72_route profile40_node72_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node73
  · exact profile40_node74
  · exact profile40_node75
  · exact profile40_node76
  · exact profile40_node77
  · exact profile40_node78
  · exact profile40_node79
  · exact profile40_node80
  · exact profile40_node84
  · exact profile40_node85

def profile40_node87_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 67 7 56 56 56 120), lower := (rows 25 67 7 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 64), good := (rows 17 71 7 0 16 32 64) }] }

theorem profile40_node87 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,3] 6 56 profile40_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,3] 6 56 profile40_node87_cert).mp (by decide +kernel))

def profile40_node88_cert : Bound 7 := { allowed := (rows 32 56 48 0 0 0 0), upper := (rows 25 67 13 58 50 50 114), lower := (rows 25 67 13 8 16 32 64), losses := [] }

theorem profile40_node88 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,9] 6 50 profile40_node88_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,9] 6 50 profile40_node88_cert).mp (by decide +kernel))

def profile40_node89_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 25 67 14 57 49 49 113), lower := (rows 25 67 14 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67), good := (rows 115 115 118 0 16 32 64) }] }

theorem profile40_node89 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,10] 6 49 profile40_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,10] 6 49 profile40_node89_cert).mp (by decide +kernel))

def profile40_node90_cert : Bound 7 := { allowed := (rows 32 56 33 0 0 0 0), upper := (rows 25 67 28 43 51 35 99), lower := (rows 25 67 28 8 16 32 64), losses := [] }

theorem profile40_node90 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,24] 6 35 profile40_node90_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,24] 6 35 profile40_node90_cert).mp (by decide +kernel))

def profile40_node91_cert : Bound 7 := { allowed := (rows 32 56 24 0 0 0 0), upper := (rows 25 67 37 58 58 58 122), lower := (rows 25 67 37 8 16 32 64), losses := [] }

theorem profile40_node91 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,33] 6 58 profile40_node91_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,33] 6 58 profile40_node91_cert).mp (by decide +kernel))

def profile40_node93_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 25 67 38 9 56 56 120), lower := (rows 25 67 38 9 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 25 41 73), good := (rows 120 118 38 120 16 32 64) }] }

theorem profile40_node93 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,1] 6 56 profile40_node93_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,1] 6 56 profile40_node93_cert).mp (by decide +kernel))

def profile40_node94_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 67 38 24 57 41 105), lower := (rows 25 67 38 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 33 65), good := (rows 111 103 38 8 0 32 64) }] }

theorem profile40_node94 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,16] 6 41 profile40_node94_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,16] 6 41 profile40_node94_cert).mp (by decide +kernel))

def profile40_node95_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 25 67 38 40 25 57 89), lower := (rows 25 67 38 40 16 32 64), losses := [{ target := 5, region := (rows 9 11 4 8 25 0 73), good := (rows 91 83 6 91 16 0 64) }] }

theorem profile40_node95 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,32] 6 25 profile40_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34,32] 6 25 profile40_node95_cert).mp (by decide +kernel))

def profile40_node92_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node92_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node92 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,34] 6 (by decide) (choices 1) [1,16,32] profile40_node92_route profile40_node92_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node93
  · exact profile40_node94
  · exact profile40_node95

def profile40_node96_cert : Bound 7 := { allowed := (rows 32 56 17 0 0 0 0), upper := (rows 25 67 44 59 51 51 115), lower := (rows 25 67 44 8 16 32 64), losses := [] }

theorem profile40_node96 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,40] 6 51 profile40_node96_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65,40] 6 51 profile40_node96_cert).mp (by decide +kernel))

def profile40_node86_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node86_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile40_node86 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,65] 6 (by decide) (choices 2) [3,9,10,24,33,34,40] profile40_node86_route profile40_node86_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node87
  · exact profile40_node88
  · exact profile40_node89
  · exact profile40_node90
  · exact profile40_node91
  · exact profile40_node92
  · exact profile40_node96

def profile40_node99_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 25 74 7 9 48 48 112), lower := (rows 25 74 7 9 16 32 64), losses := [{ target := 0, region := (rows 0 11 4 8 127 127 127), good := (rows 122 122 118 122 112 112 112) }] }

theorem profile40_node99 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,1] 6 48 profile40_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,1] 6 48 profile40_node99_cert).mp (by decide +kernel))

def profile40_node100_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 74 7 24 49 33 97), lower := (rows 25 74 7 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 37 69), good := (rows 111 74 103 8 0 32 64) }] }

theorem profile40_node100 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,16] 6 33 profile40_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,16] 6 33 profile40_node100_cert).mp (by decide +kernel))

def profile40_node102_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 25 74 7 40 17 48 112), lower := (rows 25 74 7 40 17 32 64), losses := [{ target := 0, region := (rows 0 23 4 61 16 49 81), good := (rows 122 74 110 40 122 40 64) }] }

theorem profile40_node102 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32,1] 6 48 profile40_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32,1] 6 48 profile40_node102_cert).mp (by decide +kernel))

def profile40_node103_cert : CutBound 7 := { lost := (rows 0 32 32 0 0 0 0), upper := (rows 25 74 7 40 48 49 81), lower := (rows 25 74 7 40 48 32 64), losses := [{ target := 5, region := (rows 1 3 5 8 16 0 65), good := (rows 95 74 71 8 16 0 64) }] }

theorem profile40_node103 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32,32] 6 17 profile40_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32,32] 6 17 profile40_node103_cert).mp (by decide +kernel))

def profile40_node101_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0

def profile40_node101_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node101 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3,32] 6 (by decide) (choices 1) [1,32] profile40_node101_route profile40_node101_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node102
  · exact profile40_node103

def profile40_node98_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node98_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node98 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,3] 6 (by decide) (choices 1) [1,16,32] profile40_node98_route profile40_node98_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node99
  · exact profile40_node100
  · exact profile40_node101

def profile40_node104_cert : Bound 7 := { allowed := (rows 32 49 40 0 0 0 0), upper := (rows 25 74 21 43 51 35 99), lower := (rows 25 74 21 8 16 32 64), losses := [] }

theorem profile40_node104 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,17] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,17] 6 35 profile40_node104_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,17] 6 35 profile40_node104_cert).mp (by decide +kernel))

def profile40_node105_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 25 74 22 41 49 33 97), lower := (rows 25 74 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 9 0 33 65), good := (rows 107 74 6 8 0 32 64) }] }

theorem profile40_node105 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,18] 6 33 profile40_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,18] 6 33 profile40_node105_cert).mp (by decide +kernel))

def profile40_node106_cert : Bound 7 := { allowed := (rows 32 49 24 0 0 0 0), upper := (rows 25 74 37 59 51 51 115), lower := (rows 25 74 37 8 16 32 64), losses := [] }

theorem profile40_node106 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,33] 6 51 profile40_node106_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,33] 6 51 profile40_node106_cert).mp (by decide +kernel))

def profile40_node108_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 25 74 38 9 49 49 113), lower := (rows 25 74 38 9 16 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 25 41 73), good := (rows 113 118 38 113 16 32 64) }] }

theorem profile40_node108 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,1] 6 49 profile40_node108_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,1] 6 49 profile40_node108_cert).mp (by decide +kernel))

def profile40_node109_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 74 38 24 49 33 97), lower := (rows 25 74 38 24 16 32 64), losses := [{ target := 4, region := (rows 1 3 5 8 0 33 65), good := (rows 111 74 38 8 0 32 64) }] }

theorem profile40_node109 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,16] 6 33 profile40_node109_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,16] 6 33 profile40_node109_cert).mp (by decide +kernel))

def profile40_node110_cert : CutBound 7 := { lost := (rows 32 32 0 0 0 0 0), upper := (rows 25 74 38 40 17 49 81), lower := (rows 25 74 38 40 16 32 64), losses := [{ target := 5, region := (rows 11 11 4 8 31 0 79), good := (rows 91 91 87 91 16 0 64) }] }

theorem profile40_node110 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,32] 6 17 profile40_node110_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34,32] 6 17 profile40_node110_cert).mp (by decide +kernel))

def profile40_node107_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node107_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node107 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,34] 6 (by decide) (choices 1) [1,16,32] profile40_node107_route profile40_node107_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node108
  · exact profile40_node109
  · exact profile40_node110

def profile40_node111_cert : Bound 7 := { allowed := (rows 32 49 9 0 0 0 0), upper := (rows 25 74 52 43 51 35 99), lower := (rows 25 74 52 8 16 32 64), losses := [] }

theorem profile40_node111 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,48] 6 35 profile40_node111_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72,48] 6 35 profile40_node111_cert).mp (by decide +kernel))

def profile40_node97_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node97_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node97 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,72] 6 (by decide) (choices 2) [3,17,18,33,34,48] profile40_node97_route profile40_node97_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node98
  · exact profile40_node104
  · exact profile40_node105
  · exact profile40_node106
  · exact profile40_node107
  · exact profile40_node111

def profile40_node114_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 25 98 7 9 56 56 120), lower := (rows 25 98 7 9 16 32 64), losses := [{ target := 0, region := (rows 0 15 4 8 25 41 73), good := (rows 122 98 118 122 16 32 64) }] }

theorem profile40_node114 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,1] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,1] 6 56 profile40_node114_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,1] 6 56 profile40_node114_cert).mp (by decide +kernel))

def profile40_node115_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 25 98 7 24 57 41 105), lower := (rows 25 98 7 24 16 32 64), losses := [{ target := 4, region := (rows 1 7 5 8 0 33 65), good := (rows 111 98 103 8 0 32 64) }] }

theorem profile40_node115 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,16] 6 41 profile40_node115_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,16] 6 41 profile40_node115_cert).mp (by decide +kernel))

def profile40_node116_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 25 98 7 40 25 57 89), lower := (rows 25 98 7 40 16 32 64), losses := [{ target := 5, region := (rows 9 2 4 8 25 0 73), good := (rows 89 66 87 89 16 0 64) }] }

theorem profile40_node116 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,32] 6 25 profile40_node116_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3,32] 6 25 profile40_node116_cert).mp (by decide +kernel))

def profile40_node113_column : Nat → Fin 7 := fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node113_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node113 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,3] 6 (by decide) (choices 1) [1,16,32] profile40_node113_route profile40_node113_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile40_node114
  · exact profile40_node115
  · exact profile40_node116

def profile40_node117_cert : Bound 7 := { allowed := (rows 32 25 48 0 0 0 0), upper := (rows 25 98 13 59 51 51 115), lower := (rows 25 98 13 8 16 32 64), losses := [] }

theorem profile40_node117 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,9] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,9] 6 51 profile40_node117_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,9] 6 51 profile40_node117_cert).mp (by decide +kernel))

def profile40_node118_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 25 98 14 57 49 49 113), lower := (rows 25 98 14 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65), good := (rows 115 98 6 0 16 32 64) }] }

theorem profile40_node118 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,10] 6 49 profile40_node118_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,10] 6 49 profile40_node118_cert).mp (by decide +kernel))

def profile40_node119_cert : Bound 7 := { allowed := (rows 32 25 33 0 0 0 0), upper := (rows 25 98 28 43 51 35 99), lower := (rows 25 98 28 8 16 32 64), losses := [] }

theorem profile40_node119 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,24] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,24] 6 35 profile40_node119_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,24] 6 35 profile40_node119_cert).mp (by decide +kernel))

def profile40_node120_cert : Bound 7 := { allowed := (rows 32 25 24 0 0 0 0), upper := (rows 25 98 37 27 27 59 91), lower := (rows 25 98 37 8 16 32 64), losses := [] }

theorem profile40_node120 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,33] 6 27 profile40_node120_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,33] 6 27 profile40_node120_cert).mp (by decide +kernel))

def profile40_node121_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 25 98 38 25 25 57 89), lower := (rows 25 98 38 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 64), good := (rows 24 102 38 8 16 32 64) }] }

theorem profile40_node121 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,34] 6 25 profile40_node121_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,34] 6 25 profile40_node121_cert).mp (by decide +kernel))

def profile40_node122_cert : Bound 7 := { allowed := (rows 32 25 17 0 0 0 0), upper := (rows 25 98 44 27 19 51 83), lower := (rows 25 98 44 8 16 32 64), losses := [] }

theorem profile40_node122 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,40] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,40] 6 19 profile40_node122_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96,40] 6 19 profile40_node122_cert).mp (by decide +kernel))

def profile40_node112_column : Nat → Fin 7 := fun mask => match mask with | 65 => 6 | 66 => 6 | 72 => 6 | 80 => 6 | 96 => 6 | _ => 0

def profile40_node112_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile40_node112 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24,96] 6 (by decide) (choices 2) [3,9,10,24,33,34,40] profile40_node112_route profile40_node112_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node113
  · exact profile40_node117
  · exact profile40_node118
  · exact profile40_node119
  · exact profile40_node120
  · exact profile40_node121
  · exact profile40_node122

def profile40_node54_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile40_node54_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile40_node54 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [24] 6 (by decide) (choices 2) [9,24,33,40,65,72,96] profile40_node54_route profile40_node54_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile40_node55
  · exact profile40_node56
  · exact profile40_node57
  · exact profile40_node72
  · exact profile40_node86
  · exact profile40_node97
  · exact profile40_node112

def profile40_node125_cert : CutBound 7 := { lost := (rows 8 0 0 0 0 0 0), upper := (rows 67 11 13 56 48 48 112), lower := (rows 67 11 13 8 16 32 64), losses := [{ target := 3, region := (rows 3 2 4 0 127 127 127), good := (rows 115 115 117 112 112 112 112) }] }

theorem profile40_node125 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,9] 6 48 profile40_node125_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,9] 6 48 profile40_node125_cert).mp (by decide +kernel))

def profile40_node127_cert : CutBound 7 := { lost := (rows 16 16 0 0 0 0 0), upper := (rows 67 11 21 24 56 40 104), lower := (rows 67 11 21 24 16 32 64), losses := [{ target := 4, region := (rows 11 10 4 8 0 42 74), good := (rows 99 107 5 107 0 32 64) }] }

theorem profile40_node127 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,16] 6 40 profile40_node127_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,16] 6 40 profile40_node127_cert).mp (by decide +kernel))

def profile40_node129_cert : CutBound 7 := { lost := (rows 0 0 32 0 0 0 0), upper := (rows 67 11 21 40 24 48 112), lower := (rows 67 11 21 40 24 32 64), losses := [{ target := 5, region := (rows 1 2 7 8 26 0 64), good := (rows 87 31 21 24 24 0 64) }] }

theorem profile40_node129 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32,8] 6 48 profile40_node129_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32,8] 6 48 profile40_node129_cert).mp (by decide +kernel))

def profile40_node130_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 67 11 21 40 48 56 88), lower := (rows 67 11 21 40 48 32 64), losses := [{ target := 3, region := (rows 1 2 6 0 56 32 64), good := (rows 71 23 21 48 48 48 64) }] }

theorem profile40_node130 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32,32] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32,32] 6 24 profile40_node130_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32,32] 6 24 profile40_node130_cert).mp (by decide +kernel))

def profile40_node128_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node128_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node128 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17,32] 6 (by decide) (choices 1) [8,32] profile40_node128_route profile40_node128_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node129
  · exact profile40_node130

def profile40_node126_column : Nat → Fin 7 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0

def profile40_node126_route : Route 7 := (fun mask => (mask,id))

theorem profile40_node126 : Upper (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,33,32,18,18,18,17]) (R (n:=7) [34,33,32,18,18,18,17]) [66,9,17] 6 (by decide) (choices 1) [16,32] profile40_node126_route profile40_node126_column
    (by change RowCover 7 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile40_node127
  · exact profile40_node128


#print axioms profile40_node126
end Delivery.SmallBudgetTenFinite7
