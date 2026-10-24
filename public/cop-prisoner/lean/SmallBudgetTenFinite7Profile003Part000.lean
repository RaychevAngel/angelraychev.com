import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile3_node2_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 55 19 102 106 16 32 64), lower := (rows 55 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile3_node2 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,17] 6 98 profile3_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,17] 6 98 profile3_node2_cert).mp (by decide +kernel))

def profile3_node3_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 55 50 71 75 16 32 64), lower := (rows 55 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile3_node3 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,48] 6 67 profile3_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,48] 6 67 profile3_node3_cert).mp (by decide +kernel))

def profile3_node4_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 55 67 118 122 16 32 64), lower := (rows 55 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 103 99 100 104 96 96 96) }] }

theorem profile3_node4 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,65] 6 114 profile3_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,65] 6 114 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 55 82 103 107 16 32 64), lower := (rows 55 82 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile3_node5 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,80] 6 99 profile3_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54,80] 6 99 profile3_node5_cert).mp (by decide +kernel))

def profile3_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile3_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile3_node1 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [54] 6 (by decide) (choices 2) [17,48,65,80] profile3_node1_route profile3_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node2
  · exact profile3_node3
  · exact profile3_node4
  · exact profile3_node5

def profile3_node8_cert : CutBound 7 := { lost := (rows 0 0 0 2 0 0 0), upper := (rows 115 7 22 104 16 32 64), lower := (rows 115 7 22 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 4 127 127 127 127), good := (rows 121 125 124 120 120 120 120) }] }

theorem profile3_node8 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5,18] 6 96 profile3_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5,18] 6 96 profile3_node8_cert).mp (by decide +kernel))

def profile3_node9_cert : CutBound 7 := { lost := (rows 0 0 2 0 0 0 0), upper := (rows 115 7 52 74 16 32 64), lower := (rows 115 7 52 8 16 32 64), losses := [{ target := 1, region := (rows 1 0 127 8 127 127 127), good := (rows 117 117 116 124 116 116 116) }] }

theorem profile3_node9 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5,48] 6 66 profile3_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5,48] 6 66 profile3_node9_cert).mp (by decide +kernel))

def profile3_node7_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile3_node7_route : Route 7 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile3_node7 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,5] 6 (by decide) (choices 2) [18,48] profile3_node7_route profile3_node7_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node8
  · exact profile3_node9

def profile3_node10_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 115 19 102 110 16 32 64), lower := (rows 115 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 7 11 0 127 127), good := (rows 111 111 100 104 96 96 96) }] }

theorem profile3_node10 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,17] 6 102 profile3_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,17] 6 102 profile3_node10_cert).mp (by decide +kernel))

def profile3_node11_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 115 22 103 107 16 32 64), lower := (rows 115 22 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 102 100 104 96 96 96) }] }

theorem profile3_node11 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,20] 6 99 profile3_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,20] 6 99 profile3_node11_cert).mp (by decide +kernel))

def profile3_node12_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 115 50 71 79 16 32 64), lower := (rows 115 50 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 9 0 127 127), good := (rows 111 98 100 104 96 96 96) }] }

theorem profile3_node12 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,48] 6 71 profile3_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114,48] 6 71 profile3_node12_cert).mp (by decide +kernel))

def profile3_node6_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile3_node6_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile3_node6 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [114] 6 (by decide) (choices 2) [5,17,20,48] profile3_node6_route profile3_node6_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node7
  · exact profile3_node10
  · exact profile3_node11
  · exact profile3_node12

def profile3_node13_cert : CutBound 7 := { lost := (rows 2 0 0 0 0 0 0), upper := (rows 117 115 119 123 16 32 64), lower := (rows 117 2 4 8 16 32 64), losses := [{ target := 1, region := (rows 5 0 4 8 127 127 127), good := (rows 117 112 117 120 112 112 112) }] }

theorem profile3_node13 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [116] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [116] 6 115 profile3_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [116] 6 115 profile3_node13_cert).mp (by decide +kernel))

def profile3_node0_column : Nat → Fin 7 := fun mask => match mask with | 30 => 3 | 46 => 3 | 78 => 3 | 58 => 3 | 90 => 3 | 106 => 3 | 60 => 3 | 92 => 3 | 108 => 3 | 120 => 3 | _ => 0

def profile3_node0_route : Route 7 := (fun mask => match mask with | 86 => (54,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 102 => (54,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [] 6 (by decide) (choices 4) [54,114,116] profile3_node0_route profile3_node0_column
    (by change RowCover 7 4 (choices 4); exact cover ⟨4,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile3_node1
  · exact profile3_node6
  · exact profile3_node13

theorem profile3 : Upper (D (n:=7) [65,34,33,32,2,2,2]) (R (n:=7) [65,34,33,32,2,2,2]) [] 6 := profile3_node0


#print axioms profile3
end Delivery.SmallBudgetTenFinite7
