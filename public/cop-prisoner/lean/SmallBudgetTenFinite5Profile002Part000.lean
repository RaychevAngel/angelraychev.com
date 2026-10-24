import SmallBudgetTenFinite5Common

namespace Delivery.SmallBudgetTenFinite5
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile2_node2_cert : CutBound 5 := { lost := (rows 8 8 0 4 4), upper := (rows 7 7 31 27 27), lower := (rows 7 7 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 11 19), good := (rows 27 27 0 8 16) },{ target := 3, region := (rows 7 7 4 0 16), good := (rows 7 7 7 0 16) }] }

theorem profile2_node2 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5] 6 27 profile2_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,5] 6 27 profile2_node2_cert).mp (by decide +kernel))

def profile2_node5_cert : CutBound 5 := { lost := (rows 0 0 2 1 3), upper := (rows 7 11 21 26 28), lower := (rows 7 11 21 26 16), losses := [{ target := 0, region := (rows 0 2 4 11 21), good := (rows 30 26 28 26 16) },{ target := 1, region := (rows 1 0 7 8 26), good := (rows 21 29 21 28 16) }] }

theorem profile2_node5 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,18] 6 12 profile2_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,18] 6 12 profile2_node5_cert).mp (by decide +kernel))

def profile2_node6_cert : CutBound 5 := { lost := (rows 0 0 0 3 5), upper := (rows 7 11 21 28 26), lower := (rows 7 11 21 28 16), losses := [{ target := 0, region := (rows 0 2 4 13 19), good := (rows 30 26 28 28 16) },{ target := 1, region := (rows 1 0 4 12 16), good := (rows 13 9 29 28 16) },{ target := 2, region := (rows 1 2 0 8 18), good := (rows 19 27 17 24 16) }] }

theorem profile2_node6 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20] 6 10 profile2_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17,20] 6 10 profile2_node6_cert).mp (by decide +kernel))

def profile2_node4_column : Nat → Fin 5 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 6 => 4 | _ => 0

def profile2_node4_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node4 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,17] 6 (by decide) (choices 2) [18,20] profile2_node4_route profile2_node4_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile2_node5
  · exact profile2_node6

def profile2_node7_cert : CutBound 5 := { lost := (rows 24 0 0 2 2), upper := (rows 7 11 22 29 29), lower := (rows 7 11 22 8 16), losses := [{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 25 20 8 16) },{ target := 3, region := (rows 5 2 4 0 16), good := (rows 7 3 23 0 16) },{ target := 4, region := (rows 5 2 4 8 0), good := (rows 7 11 7 8 0) }] }

theorem profile2_node7 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18] 6 29 profile2_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,18] 6 29 profile2_node7_cert).mp (by decide +kernel))

def profile2_node9_cert : CutBound 5 := { lost := (rows 0 4 3 0 1), upper := (rows 7 11 28 25 22), lower := (rows 7 11 28 25 16), losses := [{ target := 0, region := (rows 0 2 14 8 19), good := (rows 22 30 28 28 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 5 13 28 29 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 11 26 27 16) }] }

theorem profile2_node9 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,17] 6 6 profile2_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,17] 6 6 profile2_node9_cert).mp (by decide +kernel))

def profile2_node10_cert : CutBound 5 := { lost := (rows 0 0 3 0 10), upper := (rows 7 11 28 26 21), lower := (rows 7 11 28 26 16), losses := [{ target := 0, region := (rows 0 2 12 8 16), good := (rows 6 14 28 30 16) },{ target := 1, region := (rows 1 0 14 8 19), good := (rows 21 29 28 28 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 19 20 18 16) }] }

theorem profile2_node10 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18] 6 5 profile2_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,18] 6 5 profile2_node10_cert).mp (by decide +kernel))

def profile2_node11_cert : CutBound 5 := { lost := (rows 0 0 3 3 0), upper := (rows 7 11 28 28 19), lower := (rows 7 11 28 28 16), losses := [{ target := 0, region := (rows 0 2 28 28 16), good := (rows 14 14 28 28 28) },{ target := 1, region := (rows 1 0 28 28 16), good := (rows 13 13 28 28 28) }] }

theorem profile2_node11 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,20] 6 3 profile2_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24,20] 6 3 profile2_node11_cert).mp (by decide +kernel))

def profile2_node8_column : Nat → Fin 5 := fun mask => match mask with | 3 => 4 | 5 => 4 | 6 => 4 | _ => 0

def profile2_node8_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node8 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9,24] 6 (by decide) (choices 2) [17,18,20] profile2_node8_route profile2_node8_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node9
  · exact profile2_node10
  · exact profile2_node11

def profile2_node3_column : Nat → Fin 5 := fun mask => match mask with | 3 => 4 | 9 => 4 | 10 => 4 | _ => 0

def profile2_node3_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node3 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,9] 6 (by decide) (choices 2) [17,18,24] profile2_node3_route profile2_node3_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node4
  · exact profile2_node7
  · exact profile2_node8

def profile2_node12_cert : CutBound 5 := { lost := (rows 24 0 0 4 4), upper := (rows 7 14 31 27 27), lower := (rows 7 14 4 8 16), losses := [{ target := 2, region := (rows 1 2 0 9 17), good := (rows 27 10 0 8 16) },{ target := 3, region := (rows 3 2 4 0 16), good := (rows 7 7 4 0 16) },{ target := 4, region := (rows 3 2 4 8 0), good := (rows 7 15 4 8 0) }] }

theorem profile2_node12 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12] 6 27 profile2_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,12] 6 27 profile2_node12_cert).mp (by decide +kernel))

def profile2_node14_cert : CutBound 5 := { lost := (rows 8 0 8 2 2), upper := (rows 7 26 7 29 29), lower := (rows 7 26 7 8 16), losses := [{ target := 1, region := (rows 1 0 4 13 21), good := (rows 29 24 29 8 16) },{ target := 3, region := (rows 7 2 7 0 16), good := (rows 7 23 7 0 16) }] }

theorem profile2_node14 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3] 6 29 profile2_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,3] 6 29 profile2_node14_cert).mp (by decide +kernel))

def profile2_node16_cert : CutBound 5 := { lost := (rows 0 5 2 0 1), upper := (rows 7 26 13 25 22), lower := (rows 7 26 13 25 16), losses := [{ target := 0, region := (rows 0 14 4 8 21), good := (rows 22 26 30 26 16) },{ target := 1, region := (rows 1 0 12 8 16), good := (rows 5 28 13 29 16) },{ target := 2, region := (rows 1 10 0 8 16), good := (rows 3 26 11 27 16) }] }

theorem profile2_node16 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,17] 6 6 profile2_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,17] 6 6 profile2_node16_cert).mp (by decide +kernel))

def profile2_node17_cert : CutBound 5 := { lost := (rows 0 5 0 5 2), upper := (rows 7 26 13 26 21), lower := (rows 7 26 13 26 16), losses := [{ target := 0, region := (rows 0 26 4 26 16), good := (rows 14 26 14 26 26) },{ target := 1, region := (rows 1 0 4 8 21), good := (rows 21 24 29 24 16) },{ target := 2, region := (rows 1 26 0 26 16), good := (rows 11 26 11 26 26) }] }

theorem profile2_node17 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,18] 6 5 profile2_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,18] 6 5 profile2_node17_cert).mp (by decide +kernel))

def profile2_node18_cert : CutBound 5 := { lost := (rows 0 5 0 0 12), upper := (rows 7 26 13 28 19), lower := (rows 7 26 13 28 16), losses := [{ target := 0, region := (rows 0 10 4 8 16), good := (rows 6 26 14 30 16) },{ target := 2, region := (rows 1 14 0 8 21), good := (rows 19 26 27 26 16) },{ target := 3, region := (rows 1 2 4 0 17), good := (rows 23 18 21 20 16) }] }

theorem profile2_node18 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20] 6 3 profile2_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9,20] 6 3 profile2_node18_cert).mp (by decide +kernel))

def profile2_node15_column : Nat → Fin 5 := fun mask => match mask with | 3 => 4 | 5 => 4 | 6 => 4 | _ => 0

def profile2_node15_route : Route 5 := (fun mask => (mask,id))

theorem profile2_node15 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,9] 6 (by decide) (choices 2) [17,18,20] profile2_node15_route profile2_node15_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node16
  · exact profile2_node17
  · exact profile2_node18

def profile2_node19_cert : CutBound 5 := { lost := (rows 8 0 1 2 10), upper := (rows 7 26 14 29 21), lower := (rows 7 26 14 8 16), losses := [{ target := 0, region := (rows 0 2 6 8 16), good := (rows 6 30 14 8 16) },{ target := 1, region := (rows 1 0 4 9 17), good := (rows 29 24 12 8 16) },{ target := 3, region := (rows 5 2 4 0 21), good := (rows 23 18 23 0 16) }] }

theorem profile2_node19 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,10] 6 21 profile2_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,10] 6 21 profile2_node19_cert).mp (by decide +kernel))

def profile2_node20_cert : CutBound 5 := { lost := (rows 0 5 3 0 0), upper := (rows 7 26 28 15 23), lower := (rows 7 26 28 8 16), losses := [{ target := 0, region := (rows 0 6 6 8 16), good := (rows 6 30 30 8 16) },{ target := 1, region := (rows 1 0 6 8 16), good := (rows 5 28 28 8 16) },{ target := 2, region := (rows 1 6 0 8 16), good := (rows 3 26 26 8 16) }] }

theorem profile2_node20 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24] 6 7 profile2_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24,24] 6 7 profile2_node20_cert).mp (by decide +kernel))

def profile2_node13_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile2_node13_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node13 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6,24] 6 (by decide) (choices 2) [3,9,10,24] profile2_node13_route profile2_node13_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node14
  · exact profile2_node15
  · exact profile2_node19
  · exact profile2_node20

def profile2_node1_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile2_node1_route : Route 5 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile2_node1 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [6] 6 (by decide) (choices 2) [5,9,12,24] profile2_node1_route profile2_node1_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node3
  · exact profile2_node12
  · exact profile2_node13

def profile2_node0_column : Nat → Fin 5 := fun mask => match mask with | _ => 0

def profile2_node0_route : Route 5 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 18 => (6,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (6,(fun i => match i.val with | 1 => 4 | 4 => 1 | _ => i)) | 24 => (6,(fun i => match i.val with | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [] 6 (by decide) (choices 2) [6] profile2_node0_route profile2_node0_column
    (by change RowCover 5 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node1

theorem profile2 : Upper (D (n:=5) [34,34,34,34,34]) (R (n:=5) [34,34,34,34,34]) [] 6 := profile2_node0


#print axioms profile2
end Delivery.SmallBudgetTenFinite5
