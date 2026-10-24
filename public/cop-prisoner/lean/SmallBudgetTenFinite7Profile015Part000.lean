import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile15_node2_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 51 19 118 122 114 32 64), lower := (rows 51 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile15_node2 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,17] 6 114 profile15_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,17] 6 114 profile15_node2_cert).mp (by decide +kernel))

def profile15_node3_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 35 86 90 82 32 64), lower := (rows 51 35 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile15_node3 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,33] 6 82 profile15_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,33] 6 82 profile15_node3_cert).mp (by decide +kernel))

def profile15_node4_cert : CutBound 7 := { lost := (rows 0 0 32 32 0 0 0), upper := (rows 51 50 87 91 83 32 64), lower := (rows 51 50 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 127), good := (rows 95 82 68 72 80 64 64) }] }

theorem profile15_node4 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,48] 6 83 profile15_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,48] 6 83 profile15_node4_cert).mp (by decide +kernel))

def profile15_node5_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 67 118 122 114 32 64), lower := (rows 51 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile15_node5 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,65] 6 114 profile15_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,65] 6 114 profile15_node5_cert).mp (by decide +kernel))

def profile15_node6_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 51 82 119 123 115 32 64), lower := (rows 51 82 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 19 4 8 16 0 127), good := (rows 83 82 68 72 82 64 64) }] }

theorem profile15_node6 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,80] 6 115 profile15_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,80] 6 115 profile15_node6_cert).mp (by decide +kernel))

def profile15_node7_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 51 98 87 91 83 32 64), lower := (rows 51 98 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 127 4 8 0 127 127), good := (rows 99 98 102 106 98 98 98) }] }

theorem profile15_node7 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,96] 6 83 profile15_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50,96] 6 83 profile15_node7_cert).mp (by decide +kernel))

def profile15_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile15_node1_route : Route 7 := (fun mask => (mask,id))

theorem profile15_node1 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [50] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile15_node1_route profile15_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile15_node2
  · exact profile15_node3
  · exact profile15_node4
  · exact profile15_node5
  · exact profile15_node6
  · exact profile15_node7

def profile15_node8_cert : CutBound 7 := { lost := (rows 16 0 0 0 0 0 0), upper := (rows 99 115 119 123 115 32 64), lower := (rows 99 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 127 127), good := (rows 99 99 100 104 96 96 96) }] }

theorem profile15_node8 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [98] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [98] 6 115 profile15_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [98] 6 115 profile15_node8_cert).mp (by decide +kernel))

def profile15_node9_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 113 115 119 123 115 32 64), lower := (rows 113 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 17 0 4 8 16 127 127), good := (rows 113 96 100 104 113 96 96) }] }

theorem profile15_node9 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [112] 6 115 profile15_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [112] 6 115 profile15_node9_cert).mp (by decide +kernel))

def profile15_node0_column : Nat → Fin 7 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 52 => 2 | 84 => 2 | 100 => 2 | 56 => 3 | 88 => 3 | 104 => 3 | _ => 0

def profile15_node0_route : Route 7 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile15_node0 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [] 6 (by decide) (choices 3) [50,98,112] profile15_node0_route profile15_node0_column
    (by change RowCover 7 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile15_node1
  · exact profile15_node8
  · exact profile15_node9

theorem profile15 : Upper (D (n:=7) [49,34,32,32,19,2,2]) (R (n:=7) [49,34,32,32,19,2,2]) [] 6 := profile15_node0


#print axioms profile15
end Delivery.SmallBudgetTenFinite7
