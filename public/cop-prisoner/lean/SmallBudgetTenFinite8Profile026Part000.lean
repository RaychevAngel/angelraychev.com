import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile26_node2_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 49 50 212 216 208 240 64 128), lower := (rows 49 50 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile26_node2 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,48] 6 208 profile26_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,48] 6 208 profile26_node2_cert).mp (by decide +kernel))

def profile26_node3_cert : CutBound 8 := { lost := (rows 0 160 0 0 0 0 0 0), upper := (rows 49 82 244 248 240 240 64 128), lower := (rows 49 82 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 19 4 8 16 0 255 255), good := (rows 211 210 196 200 210 192 192 192) },{ target := 7, region := (rows 1 19 4 8 16 32 255 0), good := (rows 115 82 68 72 82 96 64 64) }] }

theorem profile26_node3 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,80] 6 240 profile26_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,80] 6 240 profile26_node3_cert).mp (by decide +kernel))

def profile26_node4_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 49 98 212 216 208 240 64 128), lower := (rows 49 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 35 4 8 0 32 255 255), good := (rows 227 226 196 200 192 226 192 192) },{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile26_node4 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,96] 6 208 profile26_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,96] 6 208 profile26_node4_cert).mp (by decide +kernel))

def profile26_node5_cert : CutBound 8 := { lost := (rows 0 48 0 0 0 0 0 0), upper := (rows 49 194 244 248 240 240 64 128), lower := (rows 49 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 226 194 194) },{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 211 194 198 202 210 194 194 194) }] }

theorem profile26_node5 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,192] 6 240 profile26_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48,192] 6 240 profile26_node5_cert).mp (by decide +kernel))

def profile26_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile26_node1_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile26_node1 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [48] 6 (by decide) (choices 2) [48,80,96,192] profile26_node1_route profile26_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile26_node2
  · exact profile26_node3
  · exact profile26_node4
  · exact profile26_node5

def profile26_node6_cert : CutBound 8 := { lost := (rows 160 0 0 0 0 0 0 0), upper := (rows 81 242 244 248 240 240 64 128), lower := (rows 81 2 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 17 2 4 8 16 0 255 255), good := (rows 209 194 196 200 209 192 192 192) },{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 66 68 72 81 96 64 64) }] }

theorem profile26_node6 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [80] 6 240 profile26_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [80] 6 240 profile26_node6_cert).mp (by decide +kernel))

def profile26_node7_cert : CutBound 8 := { lost := (rows 144 0 0 0 0 0 0 0), upper := (rows 97 242 244 248 240 240 64 128), lower := (rows 97 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 7, region := (rows 33 2 4 8 16 32 255 0), good := (rows 97 66 68 72 80 97 64 64) }] }

theorem profile26_node7 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [96] 6 240 profile26_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [96] 6 240 profile26_node7_cert).mp (by decide +kernel))

def profile26_node8_cert : CutBound 8 := { lost := (rows 48 0 0 0 0 0 0 0), upper := (rows 193 242 244 248 240 240 64 128), lower := (rows 193 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) },{ target := 5, region := (rows 255 2 4 8 16 0 255 255), good := (rows 193 195 197 201 209 193 193 193) }] }

theorem profile26_node8 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [192] 6 240 profile26_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [192] 6 240 profile26_node8_cert).mp (by decide +kernel))

def profile26_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile26_node0_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile26_node0 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [] 6 (by decide) (choices 2) [48,80,96,192] profile26_node0_route profile26_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile26_node1
  · exact profile26_node6
  · exact profile26_node7
  · exact profile26_node8

theorem profile26 : Upper (D (n:=8) [32,32,32,32,20,18,2,2]) (R (n:=8) [32,32,32,32,20,18,2,2]) [] 6 := profile26_node0


#print axioms profile26
end Delivery.SmallBudgetTenFinite8
