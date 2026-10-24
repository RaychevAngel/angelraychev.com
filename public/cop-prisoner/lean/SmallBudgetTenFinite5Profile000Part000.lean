import SmallBudgetTenFinite5Common

namespace Delivery.SmallBudgetTenFinite5
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 7 31 27 27), lower := (rows 15 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile0_node2 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5] 6 27 profile0_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,5] 6 27 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 15 14 23 27 19), lower := (rows 15 14 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 14 14 4 8 16) }] }

theorem profile0_node3 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,12] 6 19 profile0_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,12] 6 19 profile0_node3_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 19 7 28 28), lower := (rows 15 19 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) }] }

theorem profile0_node5 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,3] 6 28 profile0_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,3] 6 28 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 19 13 30 22), lower := (rows 15 19 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile0_node6 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,9] 6 22 profile0_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,9] 6 22 profile0_node6_cert).mp (by decide +kernel))

def profile0_node7_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 19 14 29 21), lower := (rows 15 19 14 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 14 22 14 8 16) }] }

theorem profile0_node7 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,10] 6 21 profile0_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,10] 6 21 profile0_node7_cert).mp (by decide +kernel))

def profile0_node8_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 15 19 21 14 30), lower := (rows 15 19 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile0_node8 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,17] 6 14 profile0_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,17] 6 14 profile0_node8_cert).mp (by decide +kernel))

def profile0_node9_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 15 19 22 13 29), lower := (rows 15 19 22 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 14 22 22 8 16) }] }

theorem profile0_node9 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,18] 6 13 profile0_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,18] 6 13 profile0_node9_cert).mp (by decide +kernel))

def profile0_node10_cert : CutBound 5 := { lost := (rows 0 8 0 0 0), upper := (rows 15 19 28 15 23), lower := (rows 15 19 28 8 16), losses := [{ target := 3, region := (rows 1 3 4 0 17), good := (rows 23 19 20 0 16) }] }

theorem profile0_node10 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24] 6 7 profile0_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17,24] 6 7 profile0_node10_cert).mp (by decide +kernel))

def profile0_node4_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile0_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node4 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,17] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile0_node4_route profile0_node4_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node5
  · exact profile0_node6
  · exact profile0_node7
  · exact profile0_node8
  · exact profile0_node9
  · exact profile0_node10

def profile0_node11_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 15 22 31 27 27), lower := (rows 15 22 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 18 0 8 16) }] }

theorem profile0_node11 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20] 6 27 profile0_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14,20] 6 27 profile0_node11_cert).mp (by decide +kernel))

def profile0_node1_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile0_node1_route : Route 5 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [14] 6 (by decide) (choices 2) [5,12,17,20] profile0_node1_route profile0_node1_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node4
  · exact profile0_node11

def profile0_node13_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 7 31 27 27), lower := (rows 23 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) }] }

theorem profile0_node13 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5] 6 27 profile0_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,5] 6 27 profile0_node13_cert).mp (by decide +kernel))

def profile0_node15_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 11 7 28 28), lower := (rows 23 11 7 8 16), losses := [{ target := 0, region := (rows 0 2 4 13 21), good := (rows 30 26 30 8 16) }] }

theorem profile0_node15 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,3] 6 28 profile0_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,3] 6 28 profile0_node15_cert).mp (by decide +kernel))

def profile0_node16_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 11 13 30 22), lower := (rows 23 11 13 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile0_node16 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,9] 6 22 profile0_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,9] 6 22 profile0_node16_cert).mp (by decide +kernel))

def profile0_node17_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 11 14 29 21), lower := (rows 23 11 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 22 14 14 8 16) }] }

theorem profile0_node17 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,10] 6 21 profile0_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,10] 6 21 profile0_node17_cert).mp (by decide +kernel))

def profile0_node18_cert : CutBound 5 := { lost := (rows 0 0 0 1 0), upper := (rows 23 11 21 14 30), lower := (rows 23 11 21 8 16), losses := [{ target := 0, region := (rows 0 2 4 9 17), good := (rows 30 26 28 8 16) }] }

theorem profile0_node18 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,17] 6 14 profile0_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,17] 6 14 profile0_node18_cert).mp (by decide +kernel))

def profile0_node19_cert : CutBound 5 := { lost := (rows 0 0 1 0 0), upper := (rows 23 11 22 13 29), lower := (rows 23 11 22 8 16), losses := [{ target := 0, region := (rows 0 2 5 8 16), good := (rows 22 14 22 8 16) }] }

theorem profile0_node19 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,18] 6 13 profile0_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,18] 6 13 profile0_node19_cert).mp (by decide +kernel))

def profile0_node20_cert : CutBound 5 := { lost := (rows 0 16 0 16 0), upper := (rows 23 11 28 15 23), lower := (rows 23 11 28 8 16), losses := [{ target := 4, region := (rows 1 3 4 9 0), good := (rows 15 11 12 8 0) }] }

theorem profile0_node20 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24] 6 7 profile0_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9,24] 6 7 profile0_node20_cert).mp (by decide +kernel))

def profile0_node14_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile0_node14_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node14 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,9] 6 (by decide) (choices 2) [3,9,10,17,18,24] profile0_node14_route profile0_node14_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node15
  · exact profile0_node16
  · exact profile0_node17
  · exact profile0_node18
  · exact profile0_node19
  · exact profile0_node20

def profile0_node21_cert : CutBound 5 := { lost := (rows 0 0 0 4 0), upper := (rows 23 14 31 27 27), lower := (rows 23 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) }] }

theorem profile0_node21 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12] 6 27 profile0_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,12] 6 27 profile0_node21_cert).mp (by decide +kernel))

def profile0_node22_cert : CutBound 5 := { lost := (rows 0 4 0 0 0), upper := (rows 23 19 15 15 31), lower := (rows 23 19 4 8 16), losses := [{ target := 2, region := (rows 1 3 0 8 16), good := (rows 19 19 0 8 16) }] }

theorem profile0_node22 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,17] 6 15 profile0_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,17] 6 15 profile0_node22_cert).mp (by decide +kernel))

def profile0_node23_cert : CutBound 5 := { lost := (rows 0 1 0 0 0), upper := (rows 23 22 15 11 27), lower := (rows 23 22 4 8 16), losses := [{ target := 0, region := (rows 0 3 4 8 16), good := (rows 22 22 4 8 16) }] }

theorem profile0_node23 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,20] 6 11 profile0_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,20] 6 11 profile0_node23_cert).mp (by decide +kernel))

def profile0_node24_cert : CutBound 5 := { lost := (rows 0 0 16 16 0), upper := (rows 23 26 15 15 31), lower := (rows 23 26 4 8 16), losses := [{ target := 4, region := (rows 1 2 5 9 0), good := (rows 15 10 4 8 0) }] }

theorem profile0_node24 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24] 6 15 profile0_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22,24] 6 15 profile0_node24_cert).mp (by decide +kernel))

def profile0_node12_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile0_node12_route : Route 5 := (fun mask => (mask,id))

theorem profile0_node12 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [22] 6 (by decide) (choices 2) [5,9,12,17,20,24] profile0_node12_route profile0_node12_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node13
  · exact profile0_node14
  · exact profile0_node21
  · exact profile0_node22
  · exact profile0_node23
  · exact profile0_node24

def profile0_node0_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile0_node0_route : Route 5 := (fun mask => match mask with | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [] 6 (by decide) (choices 3) [14,22] profile0_node0_route profile0_node0_column
    (by change RowCover 5 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node1
  · exact profile0_node12

theorem profile0 : Upper (D (n:=5) [50,34,34,34,18]) (R (n:=5) [50,34,34,34,18]) [] 6 := profile0_node0


#print axioms profile0
end Delivery.SmallBudgetTenFinite5
