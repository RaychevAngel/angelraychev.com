import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile16_node3_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 7 19 37 200 208 224 64 128), lower := (rows 7 19 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 254 250 252 248 248 248 248 248) }] }

theorem profile16_node3 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,33] 6 192 profile16_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,33] 6 192 profile16_node3_cert).mp (by decide +kernel))

def profile16_node4_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 7 19 69 232 240 224 64 128), lower := (rows 7 19 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 254 250 252 248 248 248 248 248) }] }

theorem profile16_node4 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,65] 6 224 profile16_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,65] 6 224 profile16_node4_cert).mp (by decide +kernel))

def profile16_node5_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 7 19 100 201 209 225 64 128), lower := (rows 7 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 198 210 228 200 208 228 192 192) }] }

theorem profile16_node5 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,96] 6 193 profile16_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,96] 6 193 profile16_node5_cert).mp (by decide +kernel))

def profile16_node6_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 7 19 196 233 241 225 64 128), lower := (rows 7 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 198 214 196 204 212 228 196 196) }] }

theorem profile16_node6 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,192] 6 225 profile16_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17,192] 6 225 profile16_node6_cert).mp (by decide +kernel))

def profile16_node2_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile16_node2_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node2 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,17] 6 (by decide) (choices 2) [33,65,96,192] profile16_node2_route profile16_node2_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node3
  · exact profile16_node4
  · exact profile16_node5
  · exact profile16_node6

def profile16_node8_cert : CutBound 8 := { lost := (rows 128 0 128 0 0 0 0 0), upper := (rows 7 50 69 201 209 225 64 128), lower := (rows 7 50 69 8 16 32 64 128), losses := [{ target := 7, region := (rows 3 2 7 8 16 32 255 0), good := (rows 71 119 69 72 80 96 64 64) }] }

theorem profile16_node8 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48,65] 6 193 profile16_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48,65] 6 193 profile16_node8_cert).mp (by decide +kernel))

def profile16_node9_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 7 50 196 201 209 225 64 128), lower := (rows 7 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 198 246 196 204 212 228 196 196) }] }

theorem profile16_node9 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48,192] 6 193 profile16_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48,192] 6 193 profile16_node9_cert).mp (by decide +kernel))

def profile16_node7_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node7_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node7 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,48] 6 (by decide) (choices 2) [65,192] profile16_node7_route profile16_node7_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node8
  · exact profile16_node9

def profile16_node10_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 7 67 245 249 241 241 64 128), lower := (rows 7 67 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 5 7 4 8 16 32 255 0), good := (rows 71 67 71 72 80 96 64 64) }] }

theorem profile16_node10 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,65] 6 241 profile16_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,65] 6 241 profile16_node10_cert).mp (by decide +kernel))

def profile16_node11_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 7 82 229 233 241 225 64 128), lower := (rows 7 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 198 210 196 200 210 224 192 192) }] }

theorem profile16_node11 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,80] 6 225 profile16_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,80] 6 225 profile16_node11_cert).mp (by decide +kernel))

def profile16_node12_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 7 194 245 249 241 241 64 128), lower := (rows 7 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 198 194 198 202 210 226 194 194) }] }

theorem profile16_node12 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,192] 6 241 profile16_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6,192] 6 241 profile16_node12_cert).mp (by decide +kernel))

def profile16_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile16_node1_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node1 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [6] 6 (by decide) (choices 2) [17,48,65,80,192] profile16_node1_route profile16_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile16_node2
  · exact profile16_node7
  · exact profile16_node10
  · exact profile16_node11
  · exact profile16_node12

def profile16_node15_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 19 7 37 200 208 224 64 128), lower := (rows 19 7 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 254 252 248 248 248 248 248) }] }

theorem profile16_node15 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,33] 6 192 profile16_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,33] 6 192 profile16_node15_cert).mp (by decide +kernel))

def profile16_node16_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 19 7 69 232 240 224 64 128), lower := (rows 19 7 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 254 252 248 248 248 248 248) }] }

theorem profile16_node16 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,65] 6 224 profile16_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,65] 6 224 profile16_node16_cert).mp (by decide +kernel))

def profile16_node17_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 19 7 100 201 209 225 64 128), lower := (rows 19 7 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 210 198 228 200 208 228 192 192) }] }

theorem profile16_node17 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,96] 6 193 profile16_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,96] 6 193 profile16_node17_cert).mp (by decide +kernel))

def profile16_node18_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 19 7 196 233 241 225 64 128), lower := (rows 19 7 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 214 198 196 204 212 228 196 196) }] }

theorem profile16_node18 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,192] 6 225 profile16_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5,192] 6 225 profile16_node18_cert).mp (by decide +kernel))

def profile16_node14_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile16_node14_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node14 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,5] 6 (by decide) (choices 2) [33,65,96,192] profile16_node14_route profile16_node14_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node15
  · exact profile16_node16
  · exact profile16_node17
  · exact profile16_node18

def profile16_node20_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 19 35 69 204 212 228 64 128), lower := (rows 19 35 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 255 255), good := (rows 210 226 252 200 208 224 192 192) }] }

theorem profile16_node20 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33,65] 6 196 profile16_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33,65] 6 196 profile16_node20_cert).mp (by decide +kernel))

def profile16_node21_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 19 35 196 205 213 229 64 128), lower := (rows 19 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 214 230 196 204 212 228 196 196) }] }

theorem profile16_node21 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33,192] 6 197 profile16_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33,192] 6 197 profile16_node21_cert).mp (by decide +kernel))

def profile16_node19_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node19_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node19 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,33] 6 (by decide) (choices 2) [65,192] profile16_node19_route profile16_node19_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node20
  · exact profile16_node21

def profile16_node23_cert : CutBound 8 := { lost := (rows 0 0 128 0 0 0 0 0), upper := (rows 19 38 69 201 209 225 64 128), lower := (rows 19 38 69 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 2 5 8 16 32 255 0), good := (rows 87 102 69 72 80 96 64 64) }] }

theorem profile16_node23 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36,65] 6 193 profile16_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36,65] 6 193 profile16_node23_cert).mp (by decide +kernel))

def profile16_node24_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 19 38 196 201 209 225 64 128), lower := (rows 19 38 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 255 8 16 32 255 255), good := (rows 214 230 196 204 212 230 196 196) }] }

theorem profile16_node24 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36,192] 6 193 profile16_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36,192] 6 193 profile16_node24_cert).mp (by decide +kernel))

def profile16_node22_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node22_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node22 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,36] 6 (by decide) (choices 2) [65,192] profile16_node22_route profile16_node22_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node23
  · exact profile16_node24

def profile16_node25_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 19 67 229 237 245 229 64 128), lower := (rows 19 67 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 17 19 4 8 16 32 255 0), good := (rows 83 67 68 72 83 96 64 64) }] }

theorem profile16_node25 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,65] 6 229 profile16_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,65] 6 229 profile16_node25_cert).mp (by decide +kernel))

def profile16_node26_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 19 70 229 233 241 225 64 128), lower := (rows 19 70 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 255 255), good := (rows 210 198 198 200 208 224 192 192) }] }

theorem profile16_node26 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,68] 6 225 profile16_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,68] 6 225 profile16_node26_cert).mp (by decide +kernel))

def profile16_node27_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 19 98 197 205 213 229 64 128), lower := (rows 19 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 210 226 196 200 208 226 192 192) }] }

theorem profile16_node27 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,96] 6 197 profile16_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,96] 6 197 profile16_node27_cert).mp (by decide +kernel))

def profile16_node28_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 19 194 229 237 245 229 64 128), lower := (rows 19 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) }] }

theorem profile16_node28 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,192] 6 229 profile16_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18,192] 6 229 profile16_node28_cert).mp (by decide +kernel))

def profile16_node13_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile16_node13_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node13 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [18] 6 (by decide) (choices 2) [5,33,36,65,68,96,192] profile16_node13_route profile16_node13_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile16_node14
  · exact profile16_node19
  · exact profile16_node22
  · exact profile16_node25
  · exact profile16_node26
  · exact profile16_node27
  · exact profile16_node28

def profile16_node31_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 49 7 7 200 208 224 64 128), lower := (rows 49 7 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 254 254 248 248 248 248 248) }] }

theorem profile16_node31 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,3] 6 192 profile16_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,3] 6 192 profile16_node31_cert).mp (by decide +kernel))

def profile16_node32_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 49 7 69 202 210 226 64 128), lower := (rows 49 7 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 240 254 196 200 208 224 192 192) }] }

theorem profile16_node32 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,65] 6 194 profile16_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,65] 6 194 profile16_node32_cert).mp (by decide +kernel))

def profile16_node33_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 49 7 70 201 209 225 64 128), lower := (rows 49 7 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 240 198 198 200 208 224 192 192) }] }

theorem profile16_node33 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,66] 6 193 profile16_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,66] 6 193 profile16_node33_cert).mp (by decide +kernel))

def profile16_node34_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 49 7 196 203 211 227 64 128), lower := (rows 49 7 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 244 198 196 204 212 228 196 196) }] }

theorem profile16_node34 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,192] 6 195 profile16_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5,192] 6 195 profile16_node34_cert).mp (by decide +kernel))

def profile16_node30_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node30_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node30 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,5] 6 (by decide) (choices 2) [3,65,66,192] profile16_node30_route profile16_node30_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node31
  · exact profile16_node32
  · exact profile16_node33
  · exact profile16_node34

def profile16_node35_cert : CutBound 8 := { lost := (rows 0 128 0 0 0 0 0 0), upper := (rows 49 67 199 207 215 231 64 128), lower := (rows 49 67 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 67 68 72 80 96 64 64) }] }

theorem profile16_node35 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,65] 6 199 profile16_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,65] 6 199 profile16_node35_cert).mp (by decide +kernel))

def profile16_node36_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 49 70 199 203 211 227 64 128), lower := (rows 49 70 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 255 255), good := (rows 240 198 198 200 208 224 192 192) }] }

theorem profile16_node36 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,68] 6 195 profile16_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,68] 6 195 profile16_node36_cert).mp (by decide +kernel))

def profile16_node37_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 49 194 199 207 215 231 64 128), lower := (rows 49 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 198 202 210 226 194 194) }] }

theorem profile16_node37 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,192] 6 199 profile16_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48,192] 6 199 profile16_node37_cert).mp (by decide +kernel))

def profile16_node29_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 12 => 3 | 20 => 4 | 36 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node29_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node29 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [48] 6 (by decide) (choices 2) [5,65,68,192] profile16_node29_route profile16_node29_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node30
  · exact profile16_node35
  · exact profile16_node36
  · exact profile16_node37

def profile16_node38_cert : CutBound 8 := { lost := (rows 128 0 0 0 0 0 0 0), upper := (rows 67 247 245 253 245 245 64 128), lower := (rows 67 2 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 3 2 4 8 16 32 255 0), good := (rows 67 67 68 72 80 96 64 64) }] }

theorem profile16_node38 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [66] 6 245 profile16_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [66] 6 245 profile16_node38_cert).mp (by decide +kernel))

def profile16_node39_cert : CutBound 8 := { lost := (rows 128 0 0 0 0 0 0 0), upper := (rows 81 231 231 239 247 231 64 128), lower := (rows 81 2 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 17 2 4 8 16 32 255 0), good := (rows 81 66 68 72 81 96 64 64) }] }

theorem profile16_node39 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [80] 6 231 profile16_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [80] 6 231 profile16_node39_cert).mp (by decide +kernel))

def profile16_node42_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 7 7 248 240 240 64 128), lower := (rows 193 7 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 254 254 248 248 248 248 248) }] }

theorem profile16_node42 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,3] 6 240 profile16_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,3] 6 240 profile16_node42_cert).mp (by decide +kernel))

def profile16_node43_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 7 21 234 242 226 64 128), lower := (rows 193 7 21 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 34 255 255), good := (rows 192 254 212 200 208 224 192 192) }] }

theorem profile16_node43 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,17] 6 226 profile16_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,17] 6 226 profile16_node43_cert).mp (by decide +kernel))

def profile16_node45_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 7 22 41 208 224 64 128), lower := (rows 193 7 22 41 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 255 255 255 255), good := (rows 240 246 246 248 240 240 240 240) }] }

theorem profile16_node45 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,33] 6 192 profile16_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,33] 6 192 profile16_node45_cert).mp (by decide +kernel))

def profile16_node46_cert : Bound 8 := { allowed := (rows 0 192 193 128 0 0 0 0), upper := (rows 193 7 22 73 176 160 64 128), lower := (rows 193 7 22 73 16 32 64 128), losses := [] }

theorem profile16_node46 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,65] 6 160 profile16_node46_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,65] 6 160 profile16_node46_cert).mp (by decide +kernel))

def profile16_node47_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 7 22 104 145 161 64 128), lower := (rows 193 7 22 104 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 255 255), good := (rows 192 198 214 232 208 232 192 192) }] }

theorem profile16_node47 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,96] 6 129 profile16_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,96] 6 129 profile16_node47_cert).mp (by decide +kernel))

def profile16_node48_cert : Bound 8 := { allowed := (rows 0 192 193 1 0 0 0 0), upper := (rows 193 7 22 200 49 33 64 128), lower := (rows 193 7 22 200 16 32 64 128), losses := [] }

theorem profile16_node48 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,192] 6 33 profile16_node48_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18,192] 6 33 profile16_node48_cert).mp (by decide +kernel))

def profile16_node44_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile16_node44_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node44 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,18] 6 (by decide) (choices 2) [33,65,96,192] profile16_node44_route profile16_node44_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node45
  · exact profile16_node46
  · exact profile16_node47
  · exact profile16_node48

def profile16_node50_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 7 52 11 208 224 64 128), lower := (rows 193 7 52 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 255 255 255 255), good := (rows 244 246 244 254 244 244 244 244) }] }

theorem profile16_node50 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,3] 6 192 profile16_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,3] 6 192 profile16_node50_cert).mp (by decide +kernel))

def profile16_node51_cert : Bound 8 := { allowed := (rows 0 192 193 128 0 0 0 0), upper := (rows 193 7 52 73 146 162 64 128), lower := (rows 193 7 52 73 16 32 64 128), losses := [] }

theorem profile16_node51 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,65] 6 130 profile16_node51_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,65] 6 130 profile16_node51_cert).mp (by decide +kernel))

def profile16_node52_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 7 52 74 145 161 64 128), lower := (rows 193 7 52 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 255 255), good := (rows 192 206 244 202 208 224 192 192) }] }

theorem profile16_node52 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,66] 6 129 profile16_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,66] 6 129 profile16_node52_cert).mp (by decide +kernel))

def profile16_node53_cert : Bound 8 := { allowed := (rows 0 192 193 1 0 0 0 0), upper := (rows 193 7 52 200 19 35 64 128), lower := (rows 193 7 52 200 16 32 64 128), losses := [] }

theorem profile16_node53 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,192] 6 3 profile16_node53_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48,192] 6 3 profile16_node53_cert).mp (by decide +kernel))

def profile16_node49_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node49_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node49 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,48] 6 (by decide) (choices 2) [3,65,66,192] profile16_node49_route profile16_node49_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node50
  · exact profile16_node51
  · exact profile16_node52
  · exact profile16_node53

def profile16_node54_cert : Bound 8 := { allowed := (rows 0 192 128 193 0 0 0 0), upper := (rows 193 7 69 186 178 178 64 128), lower := (rows 193 7 69 8 16 32 64 128), losses := [] }

theorem profile16_node54 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,65] 6 178 profile16_node54_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,65] 6 178 profile16_node54_cert).mp (by decide +kernel))

def profile16_node55_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 7 70 185 177 177 64 128), lower := (rows 193 7 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 198 198 200 208 224 192 192) }] }

theorem profile16_node55 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,66] 6 177 profile16_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,66] 6 177 profile16_node55_cert).mp (by decide +kernel))

def profile16_node56_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 7 84 171 179 163 64 128), lower := (rows 193 7 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 255 255), good := (rows 192 198 212 200 212 224 192 192) }] }

theorem profile16_node56 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,80] 6 163 profile16_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,80] 6 163 profile16_node56_cert).mp (by decide +kernel))

def profile16_node57_cert : Bound 8 := { allowed := (rows 0 192 1 193 0 0 0 0), upper := (rows 193 7 196 59 51 51 64 128), lower := (rows 193 7 196 8 16 32 64 128), losses := [] }

theorem profile16_node57 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,192] 6 51 profile16_node57_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5,192] 6 51 profile16_node57_cert).mp (by decide +kernel))

def profile16_node41_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile16_node41_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node41 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,5] 6 (by decide) (choices 2) [3,17,18,48,65,66,80,192] profile16_node41_route profile16_node41_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile16_node42
  · exact profile16_node43
  · exact profile16_node44
  · exact profile16_node49
  · exact profile16_node54
  · exact profile16_node55
  · exact profile16_node56
  · exact profile16_node57

def profile16_node59_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 19 7 236 244 228 64 128), lower := (rows 193 19 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 255 255), good := (rows 192 210 254 200 208 224 192 192) }] }

theorem profile16_node59 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,3] 6 228 profile16_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,3] 6 228 profile16_node59_cert).mp (by decide +kernel))

def profile16_node62_cert : CutBound 8 := { lost := (rows 0 0 64 64 0 0 0 0), upper := (rows 193 19 37 14 80 160 64 128), lower := (rows 193 19 37 14 80 32 64 128), losses := [{ target := 6, region := (rows 1 2 7 10 16 255 0 255), good := (rows 165 191 165 174 176 160 160 160) }] }

theorem profile16_node62 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,6,64] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,6,64] 6 128 profile16_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,6,64] 6 128 profile16_node62_cert).mp (by decide +kernel))

def profile16_node61_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0

def profile16_node61_route : Route 8 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node61 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,6] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,6] 6 (by decide) (choices 1) [64] profile16_node61_route profile16_node61_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile16_node62

def profile16_node63_cert : Bound 8 := { allowed := (rows 0 192 192 129 0 0 0 0), upper := (rows 193 19 37 74 148 164 64 128), lower := (rows 193 19 37 74 16 32 64 128), losses := [] }

theorem profile16_node63 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,66] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,66] 6 132 profile16_node63_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,66] 6 132 profile16_node63_cert).mp (by decide +kernel))

def profile16_node64_cert : Bound 8 := { allowed := (rows 0 192 192 129 0 0 0 0), upper := (rows 193 19 37 76 146 162 64 128), lower := (rows 193 19 37 76 16 32 64 128), losses := [] }

theorem profile16_node64 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,68] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,68] 6 130 profile16_node64_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,68] 6 130 profile16_node64_cert).mp (by decide +kernel))

def profile16_node65_cert : Bound 8 := { allowed := (rows 0 192 192 1 0 0 0 0), upper := (rows 193 19 37 200 22 38 64 128), lower := (rows 193 19 37 200 16 32 64 128), losses := [] }

theorem profile16_node65 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,192] 6 6 profile16_node65_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33,192] 6 6 profile16_node65_cert).mp (by decide +kernel))

def profile16_node60_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node60_route : Route 8 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node60 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,33] 6 (by decide) (choices 2) [6,66,68,192] profile16_node60_route profile16_node60_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node61
  · exact profile16_node63
  · exact profile16_node64
  · exact profile16_node65

def profile16_node67_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 19 38 13 208 224 64 128), lower := (rows 193 19 38 13 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 255 255 255 255), good := (rows 240 246 246 252 240 240 240 240) }] }

theorem profile16_node67 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,5] 6 192 profile16_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,5] 6 192 profile16_node67_cert).mp (by decide +kernel))

def profile16_node68_cert : Bound 8 := { allowed := (rows 0 192 193 128 0 0 0 0), upper := (rows 193 19 38 73 148 164 64 128), lower := (rows 193 19 38 73 16 32 64 128), losses := [] }

theorem profile16_node68 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,65] 6 132 profile16_node68_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,65] 6 132 profile16_node68_cert).mp (by decide +kernel))

def profile16_node69_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 19 38 76 145 161 64 128), lower := (rows 193 19 38 76 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 255 255), good := (rows 192 210 238 204 208 224 192 192) }] }

theorem profile16_node69 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,68] 6 129 profile16_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,68] 6 129 profile16_node69_cert).mp (by decide +kernel))

def profile16_node70_cert : Bound 8 := { allowed := (rows 0 192 193 1 0 0 0 0), upper := (rows 193 19 38 200 21 37 64 128), lower := (rows 193 19 38 200 16 32 64 128), losses := [] }

theorem profile16_node70 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,192] 6 5 profile16_node70_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34,192] 6 5 profile16_node70_cert).mp (by decide +kernel))

def profile16_node66_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node66_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node66 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,34] 6 (by decide) (choices 2) [5,65,68,192] profile16_node66_route profile16_node66_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node67
  · exact profile16_node68
  · exact profile16_node69
  · exact profile16_node70

def profile16_node71_cert : Bound 8 := { allowed := (rows 0 192 128 193 0 0 0 0), upper := (rows 193 19 69 174 182 166 64 128), lower := (rows 193 19 69 8 16 32 64 128), losses := [] }

theorem profile16_node71 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,65] 6 166 profile16_node71_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,65] 6 166 profile16_node71_cert).mp (by decide +kernel))

def profile16_node72_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 19 70 173 181 165 64 128), lower := (rows 193 19 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 214 198 200 208 224 192 192) }] }

theorem profile16_node72 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,66] 6 165 profile16_node72_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,66] 6 165 profile16_node72_cert).mp (by decide +kernel))

def profile16_node73_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 19 100 143 151 167 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 192 210 228 200 208 228 192 192) }] }

theorem profile16_node73 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,96] 6 135 profile16_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,96] 6 135 profile16_node73_cert).mp (by decide +kernel))

def profile16_node74_cert : Bound 8 := { allowed := (rows 0 192 1 193 0 0 0 0), upper := (rows 193 19 196 47 55 39 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [] }

theorem profile16_node74 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,192] 6 39 profile16_node74_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17,192] 6 39 profile16_node74_cert).mp (by decide +kernel))

def profile16_node58_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile16_node58_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node58 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,17] 6 (by decide) (choices 2) [3,33,34,65,66,96,192] profile16_node58_route profile16_node58_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile16_node59
  · exact profile16_node60
  · exact profile16_node66
  · exact profile16_node71
  · exact profile16_node72
  · exact profile16_node73
  · exact profile16_node74

def profile16_node77_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 193 22 7 41 208 224 64 128), lower := (rows 193 22 7 41 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 255 255 255 255), good := (rows 240 246 246 248 240 240 240 240) }] }

theorem profile16_node77 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,33] 6 192 profile16_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,33] 6 192 profile16_node77_cert).mp (by decide +kernel))

def profile16_node78_cert : Bound 8 := { allowed := (rows 0 193 192 128 0 0 0 0), upper := (rows 193 22 7 73 176 160 64 128), lower := (rows 193 22 7 73 16 32 64 128), losses := [] }

theorem profile16_node78 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,65] 6 160 profile16_node78_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,65] 6 160 profile16_node78_cert).mp (by decide +kernel))

def profile16_node79_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 22 7 104 145 161 64 128), lower := (rows 193 22 7 104 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 255 255), good := (rows 192 214 198 232 208 232 192 192) }] }

theorem profile16_node79 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,96] 6 129 profile16_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,96] 6 129 profile16_node79_cert).mp (by decide +kernel))

def profile16_node80_cert : Bound 8 := { allowed := (rows 0 193 192 1 0 0 0 0), upper := (rows 193 22 7 200 49 33 64 128), lower := (rows 193 22 7 200 16 32 64 128), losses := [] }

theorem profile16_node80 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,192] 6 33 profile16_node80_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3,192] 6 33 profile16_node80_cert).mp (by decide +kernel))

def profile16_node76_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile16_node76_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node76 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,3] 6 (by decide) (choices 2) [33,65,96,192] profile16_node76_route profile16_node76_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node77
  · exact profile16_node78
  · exact profile16_node79
  · exact profile16_node80

def profile16_node82_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 193 22 37 11 208 224 64 128), lower := (rows 193 22 37 11 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 255 255 255 255), good := (rows 240 246 246 250 240 240 240 240) }] }

theorem profile16_node82 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,3] 6 192 profile16_node82_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,3] 6 192 profile16_node82_cert).mp (by decide +kernel))

def profile16_node83_cert : Bound 8 := { allowed := (rows 0 193 192 128 0 0 0 0), upper := (rows 193 22 37 73 146 162 64 128), lower := (rows 193 22 37 73 16 32 64 128), losses := [] }

theorem profile16_node83 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,65] 6 130 profile16_node83_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,65] 6 130 profile16_node83_cert).mp (by decide +kernel))

def profile16_node84_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 22 37 74 145 161 64 128), lower := (rows 193 22 37 74 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 16 32 255 255), good := (rows 192 222 228 202 208 224 192 192) }] }

theorem profile16_node84 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,66] 6 129 profile16_node84_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,66] 6 129 profile16_node84_cert).mp (by decide +kernel))

def profile16_node85_cert : Bound 8 := { allowed := (rows 0 193 192 1 0 0 0 0), upper := (rows 193 22 37 200 19 35 64 128), lower := (rows 193 22 37 200 16 32 64 128), losses := [] }

theorem profile16_node85 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,192] 6 3 profile16_node85_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33,192] 6 3 profile16_node85_cert).mp (by decide +kernel))

def profile16_node81_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node81_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node81 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,33] 6 (by decide) (choices 2) [3,65,66,192] profile16_node81_route profile16_node81_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node82
  · exact profile16_node83
  · exact profile16_node84
  · exact profile16_node85

def profile16_node87_cert : CutBound 8 := { lost := (rows 0 64 64 0 0 0 0 0), upper := (rows 193 22 38 73 145 161 64 128), lower := (rows 193 22 38 73 16 32 64 128), losses := [{ target := 6, region := (rows 1 11 13 8 25 41 0 255), good := (rows 183 150 166 191 144 160 128 128) }] }

theorem profile16_node87 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34,65] 6 129 profile16_node87_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34,65] 6 129 profile16_node87_cert).mp (by decide +kernel))

def profile16_node88_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 22 38 200 17 33 64 128), lower := (rows 193 22 38 200 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 16 32 255 255), good := (rows 200 222 238 200 216 232 200 200) }] }

theorem profile16_node88 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34,192] 6 1 profile16_node88_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34,192] 6 1 profile16_node88_cert).mp (by decide +kernel))

def profile16_node86_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node86_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node86 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,34] 6 (by decide) (choices 2) [65,192] profile16_node86_route profile16_node86_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile16_node87
  · exact profile16_node88

def profile16_node89_cert : CutBound 8 := { lost := (rows 0 64 0 64 0 0 0 0), upper := (rows 193 22 69 171 179 163 64 128), lower := (rows 193 22 69 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 6 4 12 20 36 0 255), good := (rows 129 190 191 136 144 160 128 128) }] }

theorem profile16_node89 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,65] 6 163 profile16_node89_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,65] 6 163 profile16_node89_cert).mp (by decide +kernel))

def profile16_node90_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 193 22 70 169 177 161 64 128), lower := (rows 193 22 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 22 8 16 32 255 255), good := (rows 192 214 198 200 214 224 192 192) }] }

theorem profile16_node90 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,66] 6 161 profile16_node90_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,66] 6 161 profile16_node90_cert).mp (by decide +kernel))

def profile16_node91_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 22 100 139 147 163 64 128), lower := (rows 193 22 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 192 214 228 200 208 228 192 192) }] }

theorem profile16_node91 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,96] 6 131 profile16_node91_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,96] 6 131 profile16_node91_cert).mp (by decide +kernel))

def profile16_node92_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 193 22 196 43 51 35 64 128), lower := (rows 193 22 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 255 8 16 32 255 255), good := (rows 196 214 196 204 214 228 196 196) }] }

theorem profile16_node92 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,192] 6 35 profile16_node92_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20,192] 6 35 profile16_node92_cert).mp (by decide +kernel))

def profile16_node75_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile16_node75_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node75 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,20] 6 (by decide) (choices 2) [3,33,34,65,66,96,192] profile16_node75_route profile16_node75_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile16_node76
  · exact profile16_node81
  · exact profile16_node86
  · exact profile16_node89
  · exact profile16_node90
  · exact profile16_node91
  · exact profile16_node92

def profile16_node95_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 193 50 7 13 208 224 64 128), lower := (rows 193 50 7 13 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 255 255 255 255), good := (rows 242 242 246 254 242 242 242 242) }] }

theorem profile16_node95 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,5] 6 192 profile16_node95_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,5] 6 192 profile16_node95_cert).mp (by decide +kernel))

def profile16_node96_cert : Bound 8 := { allowed := (rows 0 193 192 128 0 0 0 0), upper := (rows 193 50 7 73 148 164 64 128), lower := (rows 193 50 7 73 16 32 64 128), losses := [] }

theorem profile16_node96 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,65] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,65] 6 132 profile16_node96_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,65] 6 132 profile16_node96_cert).mp (by decide +kernel))

def profile16_node97_cert : CutBound 8 := { lost := (rows 0 0 0 1 0 0 0 0), upper := (rows 193 50 7 76 145 161 64 128), lower := (rows 193 50 7 76 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 255 255), good := (rows 192 242 206 204 208 224 192 192) }] }

theorem profile16_node97 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,68] 6 129 profile16_node97_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,68] 6 129 profile16_node97_cert).mp (by decide +kernel))

def profile16_node98_cert : Bound 8 := { allowed := (rows 0 193 192 1 0 0 0 0), upper := (rows 193 50 7 200 21 37 64 128), lower := (rows 193 50 7 200 16 32 64 128), losses := [] }

theorem profile16_node98 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,192] 6 5 profile16_node98_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3,192] 6 5 profile16_node98_cert).mp (by decide +kernel))

def profile16_node94_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node94_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node94 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,3] 6 (by decide) (choices 2) [5,65,68,192] profile16_node94_route profile16_node94_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node95
  · exact profile16_node96
  · exact profile16_node97
  · exact profile16_node98

def profile16_node99_cert : CutBound 8 := { lost := (rows 0 64 0 64 0 0 0 0), upper := (rows 193 50 69 143 151 167 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 6 4 12 20 36 0 255), good := (rows 129 178 191 136 144 160 128 128) }] }

theorem profile16_node99 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,65] 6 135 profile16_node99_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,65] 6 135 profile16_node99_cert).mp (by decide +kernel))

def profile16_node100_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 50 70 141 149 165 64 128), lower := (rows 193 50 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 255 255), good := (rows 192 246 198 200 208 224 192 192) }] }

theorem profile16_node100 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,66] 6 133 profile16_node100_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,66] 6 133 profile16_node100_cert).mp (by decide +kernel))

def profile16_node101_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 193 50 196 15 23 39 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 246 196 204 212 228 196 196) }] }

theorem profile16_node101 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,192] 6 7 profile16_node101_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48,192] 6 7 profile16_node101_cert).mp (by decide +kernel))

def profile16_node93_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile16_node93_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node93 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,48] 6 (by decide) (choices 2) [3,65,66,192] profile16_node93_route profile16_node93_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile16_node94
  · exact profile16_node99
  · exact profile16_node100
  · exact profile16_node101

def profile16_node102_cert : CutBound 8 := { lost := (rows 0 0 64 64 0 0 0 0), upper := (rows 193 67 183 191 183 183 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 2 6 10 18 34 0 255), good := (rows 129 191 132 136 144 160 128 128) }] }

theorem profile16_node102 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,65] 6 183 profile16_node102_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,65] 6 183 profile16_node102_cert).mp (by decide +kernel))

def profile16_node103_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 193 70 183 187 179 179 64 128), lower := (rows 193 70 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 255 255), good := (rows 192 198 198 200 208 224 192 192) }] }

theorem profile16_node103 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,68] 6 179 profile16_node103_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,68] 6 179 profile16_node103_cert).mp (by decide +kernel))

def profile16_node104_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 193 82 167 175 183 167 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 192 210 196 200 210 224 192 192) }] }

theorem profile16_node104 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,80] 6 167 profile16_node104_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,80] 6 167 profile16_node104_cert).mp (by decide +kernel))

def profile16_node105_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 193 194 55 63 55 55 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) }] }

theorem profile16_node105 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,192] 6 55 profile16_node105_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192,192] 6 55 profile16_node105_cert).mp (by decide +kernel))

def profile16_node40_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile16_node40_route : Route 8 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node40 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [192] 6 (by decide) (choices 2) [5,17,20,48,65,68,80,192] profile16_node40_route profile16_node40_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile16_node41
  · exact profile16_node58
  · exact profile16_node75
  · exact profile16_node93
  · exact profile16_node102
  · exact profile16_node103
  · exact profile16_node104
  · exact profile16_node105

def profile16_node0_column : Nat → Fin 8 := fun mask => match mask with | 10 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile16_node0_route : Route 8 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 20 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 36 => (18,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 68 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 132 => (66,(fun i => match i.val with | 1 => 2 | 2 => 1 | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile16_node0 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [] 6 (by decide) (choices 2) [6,18,48,66,80,192] profile16_node0_route profile16_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile16_node1
  · exact profile16_node13
  · exact profile16_node29
  · exact profile16_node38
  · exact profile16_node39
  · exact profile16_node40

theorem profile16 : Upper (D (n:=8) [34,33,33,32,17,17,2,2]) (R (n:=8) [34,33,33,32,17,17,2,2]) [] 6 := profile16_node0


#print axioms profile16
end Delivery.SmallBudgetTenFinite8
