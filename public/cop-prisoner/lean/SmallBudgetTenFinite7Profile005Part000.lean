import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile5_node2_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 23 23 100 104 16 32 64), lower := (rows 23 23 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 127 127 127 127), good := (rows 123 123 120 120 120 120 120) }] }

theorem profile5_node2 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,21] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,21] 6 96 profile5_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,21] 6 96 profile5_node2_cert).mp (by decide +kernel))

def profile5_node3_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 23 39 116 120 16 32 64), lower := (rows 23 39 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 127 127 127 127), good := (rows 123 123 120 120 120 120 120) }] }

theorem profile5_node3 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,37] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,37] 6 112 profile5_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,37] 6 112 profile5_node3_cert).mp (by decide +kernel))

def profile5_node4_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 23 51 100 108 16 32 64), lower := (rows 23 51 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 3 0 8 127 127 127), good := (rows 115 115 112 120 112 112 112) }] }

theorem profile5_node4 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,49] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,49] 6 100 profile5_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,49] 6 100 profile5_node4_cert).mp (by decide +kernel))

def profile5_node5_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 23 54 101 105 16 32 64), lower := (rows 23 54 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 9 127 127 127), good := (rows 123 114 112 120 112 112 112) }] }

theorem profile5_node5 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,52] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,52] 6 97 profile5_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,52] 6 97 profile5_node5_cert).mp (by decide +kernel))

def profile5_node6_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 23 99 116 124 16 32 64), lower := (rows 23 99 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 3 0 8 127 127 127), good := (rows 115 115 112 120 112 112 112) }] }

theorem profile5_node6 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,97] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,97] 6 116 profile5_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,97] 6 116 profile5_node6_cert).mp (by decide +kernel))

def profile5_node7_cert : CutBound 7 := { lost := (rows 0 0 0 4 0 0 0), upper := (rows 23 102 117 121 16 32 64), lower := (rows 23 102 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 2 0 9 127 127 127), good := (rows 123 114 112 120 112 112 112) }] }

theorem profile5_node7 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,100] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,100] 6 113 profile5_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,100] 6 113 profile5_node7_cert).mp (by decide +kernel))

def profile5_node8_cert : CutBound 7 := { lost := (rows 0 4 0 0 0 0 0), upper := (rows 23 114 101 109 16 32 64), lower := (rows 23 114 4 8 16 32 64), losses := [{ target := 2, region := (rows 1 127 0 8 127 127 127), good := (rows 115 114 114 122 114 114 114) }] }

theorem profile5_node8 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,112] 6 101 profile5_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22,112] 6 101 profile5_node8_cert).mp (by decide +kernel))

def profile5_node1_column : Nat → Fin 7 := fun mask => match mask with | 13 => 3 | 25 => 3 | 41 => 3 | 73 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile5_node1_route : Route 7 := (fun mask => match mask with | 69 => (37,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 81 => (49,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 84 => (52,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile5_node1 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [22] 6 (by decide) (choices 3) [21,37,49,52,97,100,112] profile5_node1_route profile5_node1_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile5_node2
  · exact profile5_node3
  · exact profile5_node4
  · exact profile5_node5
  · exact profile5_node6
  · exact profile5_node7
  · exact profile5_node8

def profile5_node9_cert : CutBound 7 := { lost := (rows 4 0 0 0 0 0 0), upper := (rows 51 119 117 125 16 32 64), lower := (rows 51 2 4 8 16 32 64), losses := [{ target := 2, region := (rows 3 2 0 8 127 127 127), good := (rows 115 115 112 120 112 112 112) }] }

theorem profile5_node9 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [50] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [50] 6 117 profile5_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [50] 6 117 profile5_node9_cert).mp (by decide +kernel))

def profile5_node10_cert : CutBound 7 := { lost := (rows 64 0 0 0 0 0 0), upper := (rows 53 119 119 127 16 32 64), lower := (rows 53 2 4 8 16 32 64), losses := [{ target := 6, region := (rows 5 2 4 8 127 127 0), good := (rows 53 50 53 56 48 48 48) }] }

theorem profile5_node10 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [52] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [52] 6 119 profile5_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [52] 6 119 profile5_node10_cert).mp (by decide +kernel))

def profile5_node11_cert : CutBound 7 := { lost := (rows 4 0 0 0 0 0 0), upper := (rows 113 119 119 127 16 32 64), lower := (rows 113 2 4 8 16 32 64), losses := [{ target := 2, region := (rows 127 2 0 8 127 127 127), good := (rows 113 115 113 121 113 113 113) }] }

theorem profile5_node11 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [112] 6 119 profile5_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [112] 6 119 profile5_node11_cert).mp (by decide +kernel))

def profile5_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile5_node0_route : Route 7 := (fun mask => match mask with | 38 => (22,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 70 => (22,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 98 => (50,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 84 => (52,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 100 => (52,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile5_node0 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [] 6 (by decide) (choices 3) [22,50,52,112] profile5_node0_route profile5_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile5_node1
  · exact profile5_node9
  · exact profile5_node10
  · exact profile5_node11

theorem profile5 : Upper (D (n:=7) [49,49,34,32,2,2,2]) (R (n:=7) [49,49,34,32,2,2,2]) [] 6 := profile5_node0


#print axioms profile5
end Delivery.SmallBudgetTenFinite7
