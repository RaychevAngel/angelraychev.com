import SmallBudgetTenFinite7Common

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile39_node2_cert : CutBound 7 := { lost := (rows 0 32 0 0 0 0 0), upper := (rows 49 19 117 121 113 113 64), lower := (rows 49 19 4 8 16 32 64), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 127), good := (rows 83 83 68 72 80 64 64) }] }

theorem profile39_node2 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,17] 6 113 profile39_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,17] 6 113 profile39_node2_cert).mp (by decide +kernel))

def profile39_node3_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 49 50 117 121 113 113 64), lower := (rows 49 50 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 127), good := (rows 114 114 68 72 80 96 64) }] }

theorem profile39_node3 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,48] 6 113 profile39_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,48] 6 113 profile39_node3_cert).mp (by decide +kernel))

def profile39_node4_cert : CutBound 7 := { lost := (rows 0 16 0 0 0 0 0), upper := (rows 49 67 117 121 113 113 64), lower := (rows 49 67 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 127), good := (rows 99 67 68 72 64 96 64) }] }

theorem profile39_node4 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,65] 6 113 profile39_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,65] 6 113 profile39_node4_cert).mp (by decide +kernel))

def profile39_node5_cert : CutBound 7 := { lost := (rows 0 1 0 0 0 0 0), upper := (rows 49 82 117 121 113 113 64), lower := (rows 49 82 4 8 16 32 64), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 127), good := (rows 114 82 68 72 82 96 64) }] }

theorem profile39_node5 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,80] 6 113 profile39_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48,80] 6 113 profile39_node5_cert).mp (by decide +kernel))

def profile39_node1_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile39_node1_route : Route 7 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile39_node1 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [48] 6 (by decide) (choices 2) [17,48,65,80] profile39_node1_route profile39_node1_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile39_node2
  · exact profile39_node3
  · exact profile39_node4
  · exact profile39_node5

def profile39_node6_cert : CutBound 7 := { lost := (rows 32 0 0 0 0 0 0), upper := (rows 81 115 117 121 113 113 64), lower := (rows 81 2 4 8 16 32 64), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 66 68 72 81 64 64) }] }

theorem profile39_node6 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [80] 6 113 profile39_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [80] 6 113 profile39_node6_cert).mp (by decide +kernel))

def profile39_node0_column : Nat → Fin 7 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile39_node0_route : Route 7 := (fun mask => match mask with | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile39_node0 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [] 6 (by decide) (choices 2) [48,80] profile39_node0_route profile39_node0_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile39_node1
  · exact profile39_node6

theorem profile39 : Upper (D (n:=7) [34,32,32,32,19,19,2]) (R (n:=7) [34,32,32,32,19,19,2]) [] 6 := profile39_node0


#print axioms profile39
end Delivery.SmallBudgetTenFinite7
