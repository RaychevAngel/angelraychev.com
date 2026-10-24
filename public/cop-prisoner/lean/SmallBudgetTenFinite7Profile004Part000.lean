import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile4_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 23 51 101 105 16 32 64), lower := (rows 23 51 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile4_node2 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,49] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,49] 6 97 profile4_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,49] 6 97 profile4_node2_cert).mp (by decide +kernel))

def profile4_node3_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 23 99 117 121 16 32 64), lower := (rows 23 99 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 103 99 100 104 96 96 96) }] }

theorem profile4_node3 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,97] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,97] 6 113 profile4_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,97] 6 113 profile4_node3_cert).mp (by decide +kernel))

def profile4_node4_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 23 114 101 105 16 32 64), lower := (rows 23 114 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 118 114 118 122 114 114 114) }] }

theorem profile4_node4 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,112] 6 97 profile4_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22,112] 6 97 profile4_node4_cert).mp (by decide +kernel))

def profile4_node1_column : Nat → Fin 7 := fun mask => match mask with | 13 => 2 | 21 => 2 | 37 => 2 | 69 => 2 | 25 => 3 | 41 => 3 | 73 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile4_node1_route : Route 7 := (fun mask => match mask with | 81 => (49,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile4_node1 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [22] 6 (by decide) (choices 3) [49,97,112] profile4_node1_route profile4_node1_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile4_node2
  · exact profile4_node3
  · exact profile4_node4

def profile4_node5_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 51 119 117 125 16 32 64), lower := (rows 51 2 4 8 16 32 64), losses := [{ target := 6, region := (rows 3 2 4 8 127 127 0), good := (rows 51 51 52 56 48 48 48) }] }

theorem profile4_node5 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [50] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [50] 6 117 profile4_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [50] 6 117 profile4_node5_cert).mp (by decide +kernel))

def profile4_node6_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 53 115 119 123 16 32 64), lower := (rows 53 2 4 8 16 32 64), losses := [{ target := 6, region := (rows 5 2 4 8 127 127 0), good := (rows 53 50 53 56 48 48 48) }] }

theorem profile4_node6 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [52] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [52] 6 115 profile4_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [52] 6 115 profile4_node6_cert).mp (by decide +kernel))

def profile4_node8_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 113 23 103 107 16 32 64), lower := (rows 113 23 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile4_node8 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,21] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,21] 6 99 profile4_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,21] 6 99 profile4_node8_cert).mp (by decide +kernel))

def profile4_node9_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 113 51 71 79 16 32 64), lower := (rows 113 51 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 127 127), good := (rows 97 111 100 104 96 96 96) }] }

theorem profile4_node9 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,49] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,49] 6 71 profile4_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,49] 6 71 profile4_node9_cert).mp (by decide +kernel))

def profile4_node10_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 113 54 71 75 16 32 64), lower := (rows 113 54 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 6 4 8 127 127 127), good := (rows 112 118 118 120 112 112 112) }] }

theorem profile4_node10 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,52] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,52] 6 67 profile4_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,52] 6 67 profile4_node10_cert).mp (by decide +kernel))

def profile4_node11_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 113 114 7 15 16 32 64), lower := (rows 113 114 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 127 127 127), good := (rows 114 114 118 122 114 114 114) }] }

theorem profile4_node11 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,112] 6 7 profile4_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112,112] 6 7 profile4_node11_cert).mp (by decide +kernel))

def profile4_node7_column : Nat → Fin 7 := fun mask => match mask with | 13 => 3 | 25 => 3 | 41 => 3 | 73 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile4_node7_route : Route 7 := (fun mask => match mask with | 37 => (21,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 69 => (21,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 81 => (49,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 97 => (49,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 84 => (52,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 100 => (52,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile4_node7 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [112] 6 (by decide) (choices 3) [21,49,52,112] profile4_node7_route profile4_node7_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node8
  · exact profile4_node9
  · exact profile4_node10
  · exact profile4_node11

def profile4_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile4_node0_route : Route 7 := (fun mask => match mask with | 38 => (22,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 70 => (22,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 98 => (50,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 84 => (52,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 100 => (52,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile4_node0 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [] 6 (by decide) (choices 3) [22,50,52,112] profile4_node0_route profile4_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node1
  · exact profile4_node5
  · exact profile4_node6
  · exact profile4_node7

theorem profile4 : Upper (D (n:=7) [50,49,33,32,2,2,2]) (R (n:=7) [50,49,33,32,2,2,2]) [] 6 := profile4_node0


#print axioms profile4
end Delivery.SmallBudgetTenFinite7
