import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile1_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 51 71 75 16 32 64), lower := (rows 51 51 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile1_node2 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,49] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,49] 6 67 profile1_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,49] 6 67 profile1_node2_cert).mp (by decide +kernel))

def profile1_node3_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 51 83 103 107 16 32 64), lower := (rows 51 83 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile1_node3 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,81] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,81] 6 99 profile1_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,81] 6 99 profile1_node3_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 7 := { lost := (rows 0 1 16 16 0 0 0), upper := (rows 51 114 71 75 16 32 64), lower := (rows 51 114 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 122 114 114 114) },{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile1_node4 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,112] 6 67 profile1_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50,112] 6 67 profile1_node4_cert).mp (by decide +kernel))

def profile1_node1_column : Nat → Fin 7 := fun mask => match mask with | 13 => 2 | 21 => 2 | 37 => 2 | 69 => 2 | 25 => 3 | 41 => 3 | 73 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile1_node1_route : Route 7 := (fun mask => match mask with | 97 => (81,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [50] 6 (by decide) (choices 3) [49,81,112] profile1_node1_route profile1_node1_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node4

def profile1_node6_cert : CutBound 7 := { lost := (rows 2 0 16 16 0 0 0), upper := (rows 113 51 71 75 16 32 64), lower := (rows 113 51 4 8 16 32 64), losses := [{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 113 117 121 113 113 113) },{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile1_node6 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112,49] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112,49] 6 67 profile1_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112,49] 6 67 profile1_node6_cert).mp (by decide +kernel))

def profile1_node7_cert : CutBound 7 := { lost := (rows 2 1 0 0 0 0 0), upper := (rows 113 114 7 11 16 32 64), lower := (rows 113 114 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 122 114 114 114) },{ target := 1, region := (rows 127 0 4 8 127 127 127), good := (rows 113 113 117 121 113 113 113) }] }

theorem profile1_node7 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112,112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112,112] 6 3 profile1_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112,112] 6 3 profile1_node7_cert).mp (by decide +kernel))

def profile1_node5_column : Nat → Fin 7 := fun mask => match mask with | 13 => 2 | 21 => 2 | 37 => 2 | 69 => 2 | 25 => 3 | 41 => 3 | 73 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile1_node5_route : Route 7 := (fun mask => match mask with | 81 => (49,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 97 => (49,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node5 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [112] 6 (by decide) (choices 3) [49,112] profile1_node5_route profile1_node5_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node6
  · exact profile1_node7

def profile1_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile1_node0_route : Route 7 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 98 => (50,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [] 6 (by decide) (choices 3) [50,112] profile1_node0_route profile1_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node1
  · exact profile1_node5

theorem profile1 : Upper (D (n:=7) [50,50,32,32,2,2,2]) (R (n:=7) [50,50,32,32,2,2,2]) [] 6 := profile1_node0


#print axioms profile1
end Delivery.SmallBudgetTenFinite7
