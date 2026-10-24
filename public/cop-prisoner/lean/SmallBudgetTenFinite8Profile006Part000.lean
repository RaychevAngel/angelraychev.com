import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile6_node2_cert : CutBound 8 := { lost := (rows 0 64 0 0 0 0 0 0), upper := (rows 23 35 228 232 240 32 64 128), lower := (rows 23 35 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 183 163 164 168 176 160 160 160) }] }

theorem profile6_node2 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22,33] 6 224 profile6_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22,33] 6 224 profile6_node2_cert).mp (by decide +kernel))

def profile6_node3_cert : CutBound 8 := { lost := (rows 0 128 0 0 0 0 0 0), upper := (rows 23 98 229 233 241 32 64 128), lower := (rows 23 98 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 255 4 8 16 255 255 0), good := (rows 119 98 102 106 114 98 98 98) }] }

theorem profile6_node3 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22,96] 6 225 profile6_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22,96] 6 225 profile6_node3_cert).mp (by decide +kernel))

def profile6_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node1_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node1 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [22] 6 (by decide) (choices 2) [33,96] profile6_node1_route profile6_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile6_node2
  · exact profile6_node3

def profile6_node6_cert : CutBound 8 := { lost := (rows 0 32 0 32 0 0 0 0), upper := (rows 39 19 100 200 208 32 64 128), lower := (rows 39 19 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 255 255 0 255 255), good := (rows 223 219 220 216 216 216 216 216) }] }

theorem profile6_node6 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17,96] 6 192 profile6_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17,96] 6 192 profile6_node6_cert).mp (by decide +kernel))

def profile6_node7_cert : CutBound 8 := { lost := (rows 0 0 32 0 0 0 0 0), upper := (rows 39 19 196 232 240 32 64 128), lower := (rows 39 19 196 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 199 215 196 204 212 196 196 196) }] }

theorem profile6_node7 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17,192] 6 224 profile6_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17,192] 6 224 profile6_node7_cert).mp (by decide +kernel))

def profile6_node5_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node5_route : Route 8 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node5 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,17] 6 (by decide) (choices 2) [96,192] profile6_node5_route profile6_node5_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile6_node6
  · exact profile6_node7

def profile6_node8_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 39 35 212 216 208 32 64 128), lower := (rows 39 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 223 223 220 220 220 220 220 220) }] }

theorem profile6_node8 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,33] 6 208 profile6_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,33] 6 208 profile6_node8_cert).mp (by decide +kernel))

def profile6_node9_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 39 50 197 201 209 32 64 128), lower := (rows 39 50 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 210 196 200 208 192 192 192) }] }

theorem profile6_node9 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,48] 6 193 profile6_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,48] 6 193 profile6_node9_cert).mp (by decide +kernel))

def profile6_node10_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 39 67 244 248 240 32 64 128), lower := (rows 39 67 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 199 195 196 200 208 192 192 192) }] }

theorem profile6_node10 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,65] 6 240 profile6_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,65] 6 240 profile6_node10_cert).mp (by decide +kernel))

def profile6_node11_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 39 82 229 233 241 32 64 128), lower := (rows 39 82 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 255 255), good := (rows 199 210 196 200 210 192 192 192) }] }

theorem profile6_node11 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,80] 6 225 profile6_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,80] 6 225 profile6_node11_cert).mp (by decide +kernel))

def profile6_node12_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 39 98 213 217 209 32 64 128), lower := (rows 39 98 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile6_node12 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,96] 6 209 profile6_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,96] 6 209 profile6_node12_cert).mp (by decide +kernel))

def profile6_node13_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 39 194 245 249 241 32 64 128), lower := (rows 39 194 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 199 194 198 202 210 194 194 194) }] }

theorem profile6_node13 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,192] 6 241 profile6_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38,192] 6 241 profile6_node13_cert).mp (by decide +kernel))

def profile6_node4_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile6_node4_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node4 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [38] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile6_node4_route profile6_node4_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node5
  · exact profile6_node8
  · exact profile6_node9
  · exact profile6_node10
  · exact profile6_node11
  · exact profile6_node12
  · exact profile6_node13

def profile6_node16_cert : CutBound 8 := { lost := (rows 0 0 0 32 0 0 0 0), upper := (rows 51 7 100 200 208 32 64 128), lower := (rows 51 7 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 255 255 0 255 255), good := (rows 219 223 220 216 216 216 216 216) }] }

theorem profile6_node16 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5,96] 6 192 profile6_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5,96] 6 192 profile6_node16_cert).mp (by decide +kernel))

def profile6_node17_cert : CutBound 8 := { lost := (rows 0 32 32 0 0 0 0 0), upper := (rows 51 7 196 232 240 32 64 128), lower := (rows 51 7 196 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 255 8 16 0 255 255), good := (rows 215 199 196 204 212 196 196 196) }] }

theorem profile6_node17 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5,192] 6 224 profile6_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5,192] 6 224 profile6_node17_cert).mp (by decide +kernel))

def profile6_node15_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node15_route : Route 8 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node15 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,5] 6 (by decide) (choices 2) [96,192] profile6_node15_route profile6_node15_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile6_node16
  · exact profile6_node17

def profile6_node18_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 51 35 196 204 212 32 64 128), lower := (rows 51 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 223 223 220 220 220 220 220 220) }] }

theorem profile6_node18 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,33] 6 196 profile6_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,33] 6 196 profile6_node18_cert).mp (by decide +kernel))

def profile6_node19_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 51 38 197 201 209 32 64 128), lower := (rows 51 38 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 198 196 200 208 192 192 192) }] }

theorem profile6_node19 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,36] 6 193 profile6_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,36] 6 193 profile6_node19_cert).mp (by decide +kernel))

def profile6_node20_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 51 67 228 236 244 32 64 128), lower := (rows 51 67 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) }] }

theorem profile6_node20 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,65] 6 228 profile6_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,65] 6 228 profile6_node20_cert).mp (by decide +kernel))

def profile6_node21_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 51 70 229 233 241 32 64 128), lower := (rows 51 70 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 255 255), good := (rows 211 198 198 200 208 192 192 192) }] }

theorem profile6_node21 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,68] 6 225 profile6_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,68] 6 225 profile6_node21_cert).mp (by decide +kernel))

def profile6_node22_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 51 98 197 205 213 32 64 128), lower := (rows 51 98 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile6_node22 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,96] 6 197 profile6_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,96] 6 197 profile6_node22_cert).mp (by decide +kernel))

def profile6_node23_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 51 194 229 237 245 32 64 128), lower := (rows 51 194 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 211 194 198 202 210 194 194 194) }] }

theorem profile6_node23 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,192] 6 229 profile6_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50,192] 6 229 profile6_node23_cert).mp (by decide +kernel))

def profile6_node14_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 12 => 3 | 20 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node14_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node14 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [50] 6 (by decide) (choices 2) [5,33,36,65,68,96,192] profile6_node14_route profile6_node14_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node15
  · exact profile6_node18
  · exact profile6_node19
  · exact profile6_node20
  · exact profile6_node21
  · exact profile6_node22
  · exact profile6_node23

def profile6_node24_cert : CutBound 8 := { lost := (rows 128 0 0 0 0 0 0 0), upper := (rows 99 247 245 253 245 32 64 128), lower := (rows 99 2 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 3 2 4 8 16 255 255 0), good := (rows 99 99 100 104 112 96 96 96) }] }

theorem profile6_node24 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [98] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [98] 6 245 profile6_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [98] 6 245 profile6_node24_cert).mp (by decide +kernel))

def profile6_node25_cert : CutBound 8 := { lost := (rows 128 0 0 0 0 0 0 0), upper := (rows 113 231 231 239 247 32 64 128), lower := (rows 113 2 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 17 2 4 8 16 255 255 0), good := (rows 113 98 100 104 113 96 96 96) }] }

theorem profile6_node25 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [112] 6 231 profile6_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [112] 6 231 profile6_node25_cert).mp (by decide +kernel))

def profile6_node29_cert : CutBound 8 := { lost := (rows 0 32 32 0 0 0 0 0), upper := (rows 225 7 22 104 144 32 64 128), lower := (rows 225 7 22 104 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 7 8 255 0 255 255), good := (rows 215 215 214 216 208 208 208 208) }] }

theorem profile6_node29 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,18,96] 6 128 profile6_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,18,96] 6 128 profile6_node29_cert).mp (by decide +kernel))

def profile6_node28_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node28_route : Route 8 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node28 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,18] 6 (by decide) (choices 2) [96] profile6_node28_route profile6_node28_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node29

def profile6_node30_cert : CutBound 8 := { lost := (rows 0 0 0 32 0 0 0 0), upper := (rows 225 7 38 216 208 32 64 128), lower := (rows 225 7 38 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 255 255 0 255 255), good := (rows 217 223 222 216 216 216 216 216) }] }

theorem profile6_node30 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,34] 6 208 profile6_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,34] 6 208 profile6_node30_cert).mp (by decide +kernel))

def profile6_node31_cert : CutBound 8 := { lost := (rows 0 0 0 32 0 0 0 0), upper := (rows 225 7 52 202 210 32 64 128), lower := (rows 225 7 52 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 255 255), good := (rows 193 223 212 200 208 192 192 192) }] }

theorem profile6_node31 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,48] 6 194 profile6_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,48] 6 194 profile6_node31_cert).mp (by decide +kernel))

def profile6_node32_cert : CutBound 8 := { lost := (rows 0 0 0 32 0 0 0 0), upper := (rows 225 7 100 154 146 32 64 128), lower := (rows 225 7 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) }] }

theorem profile6_node32 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,96] 6 146 profile6_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5,96] 6 146 profile6_node32_cert).mp (by decide +kernel))

def profile6_node27_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile6_node27_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node27 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,5] 6 (by decide) (choices 2) [18,34,48,96] profile6_node27_route profile6_node27_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node28
  · exact profile6_node30
  · exact profile6_node31
  · exact profile6_node32

def profile6_node34_cert : CutBound 8 := { lost := (rows 0 0 0 32 0 0 0 0), upper := (rows 225 19 38 204 212 32 64 128), lower := (rows 225 19 38 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 255 255), good := (rows 193 211 222 200 208 192 192 192) }] }

theorem profile6_node34 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17,34] 6 196 profile6_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17,34] 6 196 profile6_node34_cert).mp (by decide +kernel))

def profile6_node35_cert : CutBound 8 := { lost := (rows 0 0 128 0 0 0 0 0), upper := (rows 225 19 100 142 150 32 64 128), lower := (rows 225 19 100 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 2 255 8 16 255 255 0), good := (rows 101 119 100 108 116 100 100 100) }] }

theorem profile6_node35 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17,96] 6 134 profile6_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17,96] 6 134 profile6_node35_cert).mp (by decide +kernel))

def profile6_node33_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node33_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node33 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,17] 6 (by decide) (choices 2) [34,96] profile6_node33_route profile6_node33_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile6_node34
  · exact profile6_node35

def profile6_node38_cert : CutBound 8 := { lost := (rows 0 32 32 0 0 0 0 0), upper := (rows 225 22 7 104 144 32 64 128), lower := (rows 225 22 7 104 16 32 64 128), losses := [{ target := 5, region := (rows 1 7 5 8 255 0 255 255), good := (rows 215 214 215 216 208 208 208 208) }] }

theorem profile6_node38 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,3,96] 6 128 profile6_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,3,96] 6 128 profile6_node38_cert).mp (by decide +kernel))

def profile6_node37_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node37_route : Route 8 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node37 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,3] 6 (by decide) (choices 2) [96] profile6_node37_route profile6_node37_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile6_node38

def profile6_node39_cert : CutBound 8 := { lost := (rows 0 32 0 32 0 0 0 0), upper := (rows 225 22 37 202 210 32 64 128), lower := (rows 225 22 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 6 4 14 22 0 255 255), good := (rows 193 222 223 200 208 192 192 192) }] }

theorem profile6_node39 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,33] 6 194 profile6_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,33] 6 194 profile6_node39_cert).mp (by decide +kernel))

def profile6_node40_cert : CutBound 8 := { lost := (rows 0 0 0 32 0 0 0 0), upper := (rows 225 22 38 201 209 32 64 128), lower := (rows 225 22 38 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 217 214 198 200 208 192 192 192) }] }

theorem profile6_node40 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,34] 6 193 profile6_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,34] 6 193 profile6_node40_cert).mp (by decide +kernel))

def profile6_node41_cert : CutBound 8 := { lost := (rows 0 128 128 0 0 0 0 0), upper := (rows 225 22 100 139 147 32 64 128), lower := (rows 225 22 100 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 18 255 8 16 255 255 0), good := (rows 101 118 100 108 118 100 100 100) }] }

theorem profile6_node41 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,96] 6 131 profile6_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20,96] 6 131 profile6_node41_cert).mp (by decide +kernel))

def profile6_node36_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile6_node36_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node36 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,20] 6 (by decide) (choices 2) [3,33,34,96] profile6_node36_route profile6_node36_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node37
  · exact profile6_node39
  · exact profile6_node40
  · exact profile6_node41

def profile6_node42_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 225 35 214 222 214 32 64 128), lower := (rows 225 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) }] }

theorem profile6_node42 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,33] 6 214 profile6_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,33] 6 214 profile6_node42_cert).mp (by decide +kernel))

def profile6_node43_cert : CutBound 8 := { lost := (rows 0 64 0 0 0 0 0 0), upper := (rows 225 38 215 219 211 32 64 128), lower := (rows 225 38 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 6 4 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) }] }

theorem profile6_node43 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,36] 6 211 profile6_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,36] 6 211 profile6_node43_cert).mp (by decide +kernel))

def profile6_node44_cert : CutBound 8 := { lost := (rows 0 64 0 0 0 0 0 0), upper := (rows 225 50 199 207 215 32 64 128), lower := (rows 225 50 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 18 4 8 16 255 0 255), good := (rows 161 178 164 168 178 160 160 160) }] }

theorem profile6_node44 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,48] 6 199 profile6_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,48] 6 199 profile6_node44_cert).mp (by decide +kernel))

def profile6_node45_cert : CutBound 8 := { lost := (rows 0 128 0 0 0 0 0 0), upper := (rows 225 98 151 159 151 32 64 128), lower := (rows 225 98 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 1 255 4 8 16 255 255 0), good := (rows 99 98 102 106 114 98 98 98) }] }

theorem profile6_node45 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,96] 6 151 profile6_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224,96] 6 151 profile6_node45_cert).mp (by decide +kernel))

def profile6_node26_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 12 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile6_node26_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node26 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [224] 6 (by decide) (choices 2) [5,17,20,33,36,48,96] profile6_node26_route profile6_node26_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node27
  · exact profile6_node33
  · exact profile6_node36
  · exact profile6_node42
  · exact profile6_node43
  · exact profile6_node44
  · exact profile6_node45

def profile6_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 3 | 26 => 3 | 42 => 3 | 74 => 3 | 138 => 3 | 28 => 3 | 44 => 3 | 76 => 3 | 140 => 3 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile6_node0_route : Route 8 := (fun mask => match mask with | 70 => (38,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 134 => (38,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 162 => (98,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 194 => (98,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 84 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 148 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 100 => (98,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 164 => (98,(fun i => match i.val with | 1 => 2 | 2 => 1 | 6 => 7 | 7 => 6 | _ => i)) | 196 => (98,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile6_node0 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [] 6 (by decide) (choices 3) [22,38,50,98,112,224] profile6_node0_route profile6_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node1
  · exact profile6_node4
  · exact profile6_node14
  · exact profile6_node24
  · exact profile6_node25
  · exact profile6_node26

theorem profile6 : Upper (D (n:=8) [49,33,33,32,17,2,2,2]) (R (n:=8) [49,33,33,32,17,2,2,2]) [] 6 := profile6_node0


#print axioms profile6
end Delivery.SmallBudgetTenFinite8
