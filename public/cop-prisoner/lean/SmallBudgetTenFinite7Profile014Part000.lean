import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile14_node2_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 51 19 117 121 113 32 64), lower := (rows 51 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile14_node2 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,17] 6 113 profile14_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,17] 6 113 profile14_node2_cert).mp (by decide +kernel))

def profile14_node3_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 35 85 89 81 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile14_node3 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,33] 6 81 profile14_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,33] 6 81 profile14_node3_cert).mp (by decide +kernel))

def profile14_node4_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 51 50 85 89 81 32 64), lower := (rows 51 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) }] }

theorem profile14_node4 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,48] 6 81 profile14_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,48] 6 81 profile14_node4_cert).mp (by decide +kernel))

def profile14_node5_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 67 117 121 113 32 64), lower := (rows 51 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile14_node5 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,65] 6 113 profile14_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,65] 6 113 profile14_node5_cert).mp (by decide +kernel))

def profile14_node6_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 51 82 117 121 113 32 64), lower := (rows 51 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) }] }

theorem profile14_node6 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,80] 6 113 profile14_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,80] 6 113 profile14_node6_cert).mp (by decide +kernel))

def profile14_node7_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 51 98 85 89 81 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 114 98 102 106 114 98 98) }] }

theorem profile14_node7 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,96] 6 81 profile14_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50,96] 6 81 profile14_node7_cert).mp (by decide +kernel))

def profile14_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile14_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile14_node1 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [50] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile14_node1_route profile14_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node2
  · exact profile14_node3
  · exact profile14_node4
  · exact profile14_node5
  · exact profile14_node6
  · exact profile14_node7

def profile14_node8_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 99 115 117 121 113 32 64), lower := (rows 99 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile14_node8 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [98] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [98] 6 113 profile14_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [98] 6 113 profile14_node8_cert).mp (by decide +kernel))

def profile14_node10_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 113 19 119 123 115 32 64), lower := (rows 113 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile14_node10 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,17] 6 115 profile14_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,17] 6 115 profile14_node10_cert).mp (by decide +kernel))

def profile14_node11_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 113 35 87 91 83 32 64), lower := (rows 113 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile14_node11 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,33] 6 83 profile14_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,33] 6 83 profile14_node11_cert).mp (by decide +kernel))

def profile14_node12_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 113 50 87 91 83 32 64), lower := (rows 113 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 127 127), good := (rows 114 114 100 104 114 96 96) }] }

theorem profile14_node12 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,48] 6 83 profile14_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,48] 6 83 profile14_node12_cert).mp (by decide +kernel))

def profile14_node13_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 113 98 23 27 19 32 64), lower := (rows 113 98 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 127 4 8 16 127 127), good := (rows 114 98 102 106 114 98 98) }] }

theorem profile14_node13 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,96] 6 19 profile14_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112,96] 6 19 profile14_node13_cert).mp (by decide +kernel))

def profile14_node9_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile14_node9_route : Route 7 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node9 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [112] 6 (by decide) (choices 2) [17,33,48,96] profile14_node9_route profile14_node9_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node10
  · exact profile14_node11
  · exact profile14_node12
  · exact profile14_node13

def profile14_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile14_node0_route : Route 7 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node0 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [] 6 (by decide) (choices 3) [50,98,112] profile14_node0_route profile14_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node1
  · exact profile14_node8
  · exact profile14_node9

theorem profile14 : Upper (D (n:=7) [50,33,32,32,19,2,2]) (R (n:=7) [50,33,32,32,19,2,2]) [] 6 := profile14_node0


#print axioms profile14
end Delivery.SmallBudgetTenFinite7
