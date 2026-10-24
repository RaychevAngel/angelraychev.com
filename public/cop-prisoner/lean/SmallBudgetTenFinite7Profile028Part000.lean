import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile28_node2_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 57 11 117 121 113 113 64), lower := (rows 57 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 7 0 19 35 127), good := (rows 117 119 68 64 80 96 64) }] }

theorem profile28_node2 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,9] 6 113 profile28_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,9] 6 113 profile28_node2_cert).mp (by decide +kernel))

def profile28_node3_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 57 26 101 105 113 97 64), lower := (rows 57 26 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 127), good := (rows 122 90 68 72 80 96 64) }] }

theorem profile28_node3 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,24] 6 97 profile28_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,24] 6 97 profile28_node3_cert).mp (by decide +kernel))

def profile28_node4_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 57 67 125 121 121 121 64), lower := (rows 57 67 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 127), good := (rows 115 67 68 64 80 96 64) }] }

theorem profile28_node4 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,65] 6 121 profile28_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,65] 6 121 profile28_node4_cert).mp (by decide +kernel))

def profile28_node5_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 57 74 117 121 113 113 64), lower := (rows 57 74 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 11 4 8 16 32 127), good := (rows 122 74 68 74 80 96 64) }] }

theorem profile28_node5 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,72] 6 113 profile28_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56,72] 6 113 profile28_node5_cert).mp (by decide +kernel))

def profile28_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile28_node1_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 33 => (9,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 96 => (72,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node1 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [56] 6 (by decide) (choices 2) [9,24,65,72] profile28_node1_route profile28_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node2
  · exact profile28_node3
  · exact profile28_node4
  · exact profile28_node5

def profile28_node7_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 89 11 117 121 113 113 64), lower := (rows 89 11 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 7 0 19 35 127), good := (rows 117 119 68 64 80 96 64) }] }

theorem profile28_node7 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,9] 6 113 profile28_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,9] 6 113 profile28_node7_cert).mp (by decide +kernel))

def profile28_node8_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 89 26 101 105 113 97 64), lower := (rows 89 26 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 127), good := (rows 90 90 68 72 80 96 64) }] }

theorem profile28_node8 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,24] 6 97 profile28_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,24] 6 97 profile28_node8_cert).mp (by decide +kernel))

def profile28_node10_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 89 35 13 120 112 112 64), lower := (rows 89 35 13 8 16 32 64), losses := [{ target := 3, region := (rows 1 7 4 0 127 127 127), good := (rows 115 115 119 112 112 112 112) }] }

theorem profile28_node10 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,9] 6 112 profile28_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,9] 6 112 profile28_node10_cert).mp (by decide +kernel))

def profile28_node11_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 89 35 28 105 113 97 64), lower := (rows 89 35 28 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 127), good := (rows 92 102 92 72 80 96 64) }] }

theorem profile28_node11 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,24] 6 97 profile28_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,24] 6 97 profile28_node11_cert).mp (by decide +kernel))

def profile28_node12_cert : CutBound 7 := { lost := (rows 0 8 8 0 0 0 0), upper := (rows 89 35 37 88 88 120 64), lower := (rows 89 35 37 8 16 32 64), losses := [{ target := 3, region := (rows 1 6 6 0 16 32 127), good := (rows 81 103 103 64 80 96 64) }] }

theorem profile28_node12 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,33] 6 88 profile28_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,33] 6 88 profile28_node12_cert).mp (by decide +kernel))

def profile28_node13_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 89 35 44 89 81 113 64), lower := (rows 89 35 44 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 127), good := (rows 115 115 100 64 80 96 64) }] }

theorem profile28_node13 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,40] 6 81 profile28_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,40] 6 81 profile28_node13_cert).mp (by decide +kernel))

def profile28_node14_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 89 35 69 56 56 56 64), lower := (rows 89 35 69 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 7 0 16 32 127), good := (rows 85 103 69 64 80 96 64) }] }

theorem profile28_node14 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,65] 6 56 profile28_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,65] 6 56 profile28_node14_cert).mp (by decide +kernel))

def profile28_node15_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 89 35 76 57 49 49 64), lower := (rows 89 35 76 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 13 8 16 32 127), good := (rows 92 102 76 76 80 96 64) }] }

theorem profile28_node15 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,72] 6 49 profile28_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,72] 6 49 profile28_node15_cert).mp (by decide +kernel))

def profile28_node16_cert : CutBound 7 := { lost := (rows 0 0 1 0 0 0 0), upper := (rows 89 35 100 25 25 57 64), lower := (rows 89 35 100 8 16 32 64), losses := [{ target := 0, region := (rows 0 2 38 8 16 32 127), good := (rows 88 102 100 72 80 100 64) }] }

theorem profile28_node16 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,96] 6 25 profile28_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33,96] 6 25 profile28_node16_cert).mp (by decide +kernel))

def profile28_node9_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile28_node9_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node9 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,33] 6 (by decide) (choices 2) [9,24,33,40,65,72,96] profile28_node9_route profile28_node9_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node10
  · exact profile28_node11
  · exact profile28_node12
  · exact profile28_node13
  · exact profile28_node14
  · exact profile28_node15
  · exact profile28_node16

def profile28_node17_cert : CutBound 7 := { lost := (rows 0 0 8 0 0 0 0), upper := (rows 89 42 117 121 113 113 64), lower := (rows 89 42 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 127), good := (rows 117 98 68 64 80 96 64) }] }

theorem profile28_node17 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,40] 6 113 profile28_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,40] 6 113 profile28_node17_cert).mp (by decide +kernel))

def profile28_node18_cert : CutBound 7 := { lost := (rows 0 8 0 0 0 0 0), upper := (rows 89 67 61 57 57 57 64), lower := (rows 89 67 4 8 16 32 64), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 127), good := (rows 83 67 68 64 80 96 64) }] }

theorem profile28_node18 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,65] 6 57 profile28_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,65] 6 57 profile28_node18_cert).mp (by decide +kernel))

def profile28_node19_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 89 74 53 57 49 49 64), lower := (rows 89 74 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 11 4 8 16 32 127), good := (rows 90 74 68 74 80 96 64) }] }

theorem profile28_node19 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,72] 6 49 profile28_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,72] 6 49 profile28_node19_cert).mp (by decide +kernel))

def profile28_node20_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 89 98 61 57 57 57 64), lower := (rows 89 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 127), good := (rows 88 98 68 72 80 98 64) }] }

theorem profile28_node20 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,96] 6 57 profile28_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88,96] 6 57 profile28_node20_cert).mp (by decide +kernel))

def profile28_node6_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile28_node6_route : Route 7 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node6 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [88] 6 (by decide) (choices 2) [9,24,33,40,65,72,96] profile28_node6_route profile28_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node7
  · exact profile28_node8
  · exact profile28_node9
  · exact profile28_node17
  · exact profile28_node18
  · exact profile28_node19
  · exact profile28_node20

def profile28_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 1 | 22 => 1 | 38 => 1 | 70 => 1 | 26 => 1 | 42 => 1 | 74 => 1 | 50 => 1 | 82 => 1 | 98 => 1 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | _ => 0

def profile28_node0_route : Route 7 := (fun mask => match mask with | 104 => (88,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 112 => (88,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node0 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [] 6 (by decide) (choices 3) [56,88] profile28_node0_route profile28_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node1
  · exact profile28_node6

theorem profile28 : Upper (D (n:=7) [50,32,32,18,18,18,2]) (R (n:=7) [50,32,32,18,18,18,2]) [] 6 := profile28_node0


#print axioms profile28
end Delivery.SmallBudgetTenFinite7
