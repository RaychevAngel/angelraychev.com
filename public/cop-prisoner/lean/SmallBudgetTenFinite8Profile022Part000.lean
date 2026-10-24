import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile22_node2_cert : CutBound 8 := { lost := (rows 64 64 0 0 0 0 0 0), upper := (rows 19 19 244 248 240 240 64 128), lower := (rows 19 19 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 19 19 4 8 16 32 0 255), good := (rows 147 147 132 136 147 160 128 128) }] }

theorem profile22_node2 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,17] 6 240 profile22_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,17] 6 240 profile22_node2_cert).mp (by decide +kernel))

def profile22_node4_cert : CutBound 8 := { lost := (rows 0 0 128 0 0 0 0 0), upper := (rows 19 35 84 216 208 240 64 128), lower := (rows 19 35 84 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 2 21 8 16 32 255 0), good := (rows 87 103 84 72 84 96 64 64) }] }

theorem profile22_node4 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33,80] 6 208 profile22_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33,80] 6 208 profile22_node4_cert).mp (by decide +kernel))

def profile22_node5_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 19 35 196 216 208 240 64 128), lower := (rows 19 35 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 199 231 196 204 196 228 196 196) }] }

theorem profile22_node5 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33,192] 6 208 profile22_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33,192] 6 208 profile22_node5_cert).mp (by decide +kernel))

def profile22_node3_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile22_node3_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile22_node3 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,33] 6 (by decide) (choices 2) [80,192] profile22_node3_route profile22_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node4
  · exact profile22_node5

def profile22_node6_cert : CutBound 8 := { lost := (rows 64 0 0 0 0 0 0 0), upper := (rows 19 50 213 217 209 241 64 128), lower := (rows 19 50 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 3 2 4 8 16 32 0 255), good := (rows 147 179 132 136 144 160 128 128) }] }

theorem profile22_node6 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,48] 6 209 profile22_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,48] 6 209 profile22_node6_cert).mp (by decide +kernel))

def profile22_node7_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 19 67 244 248 240 240 64 128), lower := (rows 19 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) }] }

theorem profile22_node7 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,65] 6 240 profile22_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,65] 6 240 profile22_node7_cert).mp (by decide +kernel))

def profile22_node8_cert : CutBound 8 := { lost := (rows 64 0 0 0 0 0 0 0), upper := (rows 19 82 245 249 241 241 64 128), lower := (rows 19 82 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 3 2 4 8 16 32 0 255), good := (rows 147 147 132 136 144 160 128 128) }] }

theorem profile22_node8 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,80] 6 241 profile22_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,80] 6 241 profile22_node8_cert).mp (by decide +kernel))

def profile22_node9_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 19 98 213 217 209 241 64 128), lower := (rows 19 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 195 226 196 200 192 226 192 192) }] }

theorem profile22_node9 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,96] 6 209 profile22_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,96] 6 209 profile22_node9_cert).mp (by decide +kernel))

def profile22_node10_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 19 194 245 249 241 241 64 128), lower := (rows 19 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) }] }

theorem profile22_node10 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,192] 6 241 profile22_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18,192] 6 241 profile22_node10_cert).mp (by decide +kernel))

def profile22_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile22_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile22_node1 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [18] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile22_node1_route profile22_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node2
  · exact profile22_node3
  · exact profile22_node6
  · exact profile22_node7
  · exact profile22_node8
  · exact profile22_node9
  · exact profile22_node10

def profile22_node13_cert : CutBound 8 := { lost := (rows 0 0 128 0 0 0 0 0), upper := (rows 35 19 84 216 208 240 64 128), lower := (rows 35 19 84 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 2 22 8 16 32 255 0), good := (rows 103 87 84 72 84 96 64 64) }] }

theorem profile22_node13 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17,80] 6 208 profile22_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17,80] 6 208 profile22_node13_cert).mp (by decide +kernel))

def profile22_node14_cert : CutBound 8 := { lost := (rows 0 0 16 0 0 0 0 0), upper := (rows 35 19 196 216 208 240 64 128), lower := (rows 35 19 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 231 199 196 204 196 228 196 196) }] }

theorem profile22_node14 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17,192] 6 208 profile22_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17,192] 6 208 profile22_node14_cert).mp (by decide +kernel))

def profile22_node12_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile22_node12_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile22_node12 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,17] 6 (by decide) (choices 2) [80,192] profile22_node12_route profile22_node12_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile22_node13
  · exact profile22_node14

def profile22_node15_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 67 212 216 208 240 64 128), lower := (rows 35 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 35 4 8 0 32 255 255), good := (rows 227 195 196 200 192 227 192 192) }] }

theorem profile22_node15 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,65] 6 208 profile22_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,65] 6 208 profile22_node15_cert).mp (by decide +kernel))

def profile22_node16_cert : CutBound 8 := { lost := (rows 0 128 0 0 0 0 0 0), upper := (rows 35 82 213 217 209 241 64 128), lower := (rows 35 82 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 18 4 8 16 32 255 0), good := (rows 99 82 68 72 82 96 64 64) }] }

theorem profile22_node16 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,80] 6 209 profile22_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,80] 6 209 profile22_node16_cert).mp (by decide +kernel))

def profile22_node17_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 35 194 213 217 209 241 64 128), lower := (rows 35 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 227 194 194) }] }

theorem profile22_node17 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,192] 6 209 profile22_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34,192] 6 209 profile22_node17_cert).mp (by decide +kernel))

def profile22_node11_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile22_node11_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile22_node11 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [34] 6 (by decide) (choices 2) [17,65,80,192] profile22_node11_route profile22_node11_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node12
  · exact profile22_node15
  · exact profile22_node16
  · exact profile22_node17

def profile22_node19_cert : CutBound 8 := { lost := (rows 0 64 0 0 0 0 0 0), upper := (rows 49 19 214 218 210 242 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 179 147 132 136 144 160 128 128) }] }

theorem profile22_node19 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,17] 6 210 profile22_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,17] 6 210 profile22_node19_cert).mp (by decide +kernel))

def profile22_node20_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 49 67 214 218 210 242 64 128), lower := (rows 49 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 227 195 196 200 192 224 192 192) }] }

theorem profile22_node20 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,65] 6 210 profile22_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,65] 6 210 profile22_node20_cert).mp (by decide +kernel))

def profile22_node21_cert : CutBound 8 := { lost := (rows 0 128 0 0 0 0 0 0), upper := (rows 49 82 215 219 211 243 64 128), lower := (rows 49 82 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 19 4 8 16 32 255 0), good := (rows 115 82 68 72 82 96 64 64) }] }

theorem profile22_node21 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,80] 6 211 profile22_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,80] 6 211 profile22_node21_cert).mp (by decide +kernel))

def profile22_node22_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 49 194 215 219 211 243 64 128), lower := (rows 49 194 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 226 194 194) }] }

theorem profile22_node22 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,192] 6 211 profile22_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48,192] 6 211 profile22_node22_cert).mp (by decide +kernel))

def profile22_node18_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile22_node18_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile22_node18 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [48] 6 (by decide) (choices 2) [17,65,80,192] profile22_node18_route profile22_node18_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile22_node19
  · exact profile22_node20
  · exact profile22_node21
  · exact profile22_node22

def profile22_node23_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 67 243 245 249 241 241 64 128), lower := (rows 67 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) }] }

theorem profile22_node23 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [66] 6 241 profile22_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [66] 6 241 profile22_node23_cert).mp (by decide +kernel))

def profile22_node24_cert : CutBound 8 := { lost := (rows 128 0 0 0 0 0 0 0), upper := (rows 81 243 247 251 243 243 64 128), lower := (rows 81 2 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 66 68 72 81 96 64 64) }] }

theorem profile22_node24 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [80] 6 243 profile22_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [80] 6 243 profile22_node24_cert).mp (by decide +kernel))

def profile22_node25_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 97 211 215 219 211 243 64 128), lower := (rows 97 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) }] }

theorem profile22_node25 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [96] 6 211 profile22_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [96] 6 211 profile22_node25_cert).mp (by decide +kernel))

def profile22_node26_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 193 243 247 251 243 243 64 128), lower := (rows 193 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) }] }

theorem profile22_node26 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [192] 6 243 profile22_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [192] 6 243 profile22_node26_cert).mp (by decide +kernel))

def profile22_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile22_node0_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile22_node0 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [] 6 (by decide) (choices 2) [18,34,48,66,80,96,192] profile22_node0_route profile22_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile22_node1
  · exact profile22_node11
  · exact profile22_node18
  · exact profile22_node23
  · exact profile22_node24
  · exact profile22_node25
  · exact profile22_node26

theorem profile22 : Upper (D (n:=8) [33,33,32,32,19,17,2,2]) (R (n:=8) [33,33,32,32,19,17,2,2]) [] 6 := profile22_node0


#print axioms profile22
end Delivery.SmallBudgetTenFinite8
