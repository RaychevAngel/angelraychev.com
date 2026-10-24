import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile28_node2_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 11 245 249 241 241 241 128), lower := (rows 25 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 7 0 19 35 67 255), good := (rows 245 247 132 128 144 160 192 128) }] }

theorem profile28_node2 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,9] 6 241 profile28_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,9] 6 241 profile28_node2_cert).mp (by decide +kernel))

def profile28_node3_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 25 26 229 233 241 225 225 128), lower := (rows 25 26 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 64 255), good := (rows 154 154 132 136 144 160 192 128) }] }

theorem profile28_node3 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,24] 6 225 profile28_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,24] 6 225 profile28_node3_cert).mp (by decide +kernel))

def profile28_node5_cert : Bound 8 := { allowed := (rows 128 152 144 0 0 0 0 0), upper := (rows 25 35 13 216 208 240 208 128), lower := (rows 25 35 13 8 16 32 64 128), losses := [] }

theorem profile28_node5 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,9] 6 208 profile28_node5_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,9] 6 208 profile28_node5_cert).mp (by decide +kernel))

def profile28_node6_cert : Bound 8 := { allowed := (rows 128 152 129 0 0 0 0 0), upper := (rows 25 35 28 201 209 225 193 128), lower := (rows 25 35 28 8 16 32 64 128), losses := [] }

theorem profile28_node6 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,24] 6 193 profile28_node6_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,24] 6 193 profile28_node6_cert).mp (by decide +kernel))

def profile28_node8_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 25 35 69 24 152 168 200 128), lower := (rows 25 35 69 24 16 32 64 128), losses := [{ target := 4, region := (rows 1 7 7 8 0 41 73 255), good := (rows 239 231 231 232 128 160 192 128) }] }

theorem profile28_node8 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,16] 6 136 profile28_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,16] 6 136 profile28_node8_cert).mp (by decide +kernel))

def profile28_node10_cert : CutBound 8 := { lost := (rows 0 8 8 0 0 0 0 0), upper := (rows 25 35 69 136 24 176 208 128), lower := (rows 25 35 69 136 24 32 64 128), losses := [{ target := 3, region := (rows 1 7 7 0 16 49 81 255), good := (rows 247 231 231 128 240 160 192 128) }] }

theorem profile28_node10 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128,8] 6 144 profile28_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128,8] 6 144 profile28_node10_cert).mp (by decide +kernel))

def profile28_node11_cert : CutBound 8 := { lost := (rows 0 128 128 0 0 0 0 0), upper := (rows 25 35 69 136 144 56 88 128), lower := (rows 25 35 69 136 144 32 64 128), losses := [{ target := 7, region := (rows 1 7 7 8 16 33 65 0), good := (rows 127 103 103 8 16 32 64 0) }] }

theorem profile28_node11 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128,128] 6 24 profile28_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128,128] 6 24 profile28_node11_cert).mp (by decide +kernel))

def profile28_node9_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile28_node9_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node9 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65,128] 6 (by decide) (choices 1) [8,128] profile28_node9_route profile28_node9_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node10
  · exact profile28_node11

def profile28_node7_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile28_node7_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node7 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,65] 6 (by decide) (choices 1) [16,128] profile28_node7_route profile28_node7_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node8
  · exact profile28_node9

def profile28_node12_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 25 35 76 153 145 177 209 128), lower := (rows 25 35 76 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67 255), good := (rows 243 243 196 128 144 160 192 128) }] }

theorem profile28_node12 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,72] 6 145 profile28_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,72] 6 145 profile28_node12_cert).mp (by decide +kernel))

def profile28_node13_cert : Bound 8 := { allowed := (rows 128 152 24 0 0 0 0 0), upper := (rows 25 35 133 216 216 248 216 128), lower := (rows 25 35 133 8 16 32 64 128), losses := [] }

theorem profile28_node13 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,129] 6 216 profile28_node13_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,129] 6 216 profile28_node13_cert).mp (by decide +kernel))

def profile28_node14_cert : Bound 8 := { allowed := (rows 128 152 17 0 0 0 0 0), upper := (rows 25 35 140 217 209 241 209 128), lower := (rows 25 35 140 8 16 32 64 128), losses := [] }

theorem profile28_node14 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,136] 6 209 profile28_node14_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,136] 6 209 profile28_node14_cert).mp (by decide +kernel))

def profile28_node15_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 25 35 196 153 153 185 217 128), lower := (rows 25 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 68 8 16 32 64 255), good := (rows 152 162 196 136 144 160 196 128) }] }

theorem profile28_node15 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,192] 6 153 profile28_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33,192] 6 153 profile28_node15_cert).mp (by decide +kernel))

def profile28_node4_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile28_node4_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node4 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,33] 6 (by decide) (choices 2) [9,24,65,72,129,136,192] profile28_node4_route profile28_node4_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node5
  · exact profile28_node6
  · exact profile28_node7
  · exact profile28_node12
  · exact profile28_node13
  · exact profile28_node14
  · exact profile28_node15

def profile28_node16_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 42 213 217 209 241 209 128), lower := (rows 25 42 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 162 132 128 144 160 192 128) }] }

theorem profile28_node16 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,40] 6 209 profile28_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,40] 6 209 profile28_node16_cert).mp (by decide +kernel))

def profile28_node18_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 25 98 13 153 145 177 209 128), lower := (rows 25 98 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 7 4 0 21 37 69 255), good := (rows 243 226 247 128 144 160 192 128) }] }

theorem profile28_node18 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,9] 6 145 profile28_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,9] 6 145 profile28_node18_cert).mp (by decide +kernel))

def profile28_node19_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 25 98 28 137 145 161 193 128), lower := (rows 25 98 28 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 5 8 16 32 64 255), good := (rows 156 226 156 136 144 160 192 128) }] }

theorem profile28_node19 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,24] 6 129 profile28_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,24] 6 129 profile28_node19_cert).mp (by decide +kernel))

def profile28_node20_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 25 98 133 153 153 185 217 128), lower := (rows 25 98 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 255), good := (rows 149 226 133 128 144 160 192 128) }] }

theorem profile28_node20 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,129] 6 153 profile28_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,129] 6 153 profile28_node20_cert).mp (by decide +kernel))

def profile28_node21_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 25 98 140 153 145 177 209 128), lower := (rows 25 98 140 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 13 8 16 32 64 255), good := (rows 156 226 140 140 144 160 192 128) }] }

theorem profile28_node21 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,136] 6 145 profile28_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96,136] 6 145 profile28_node21_cert).mp (by decide +kernel))

def profile28_node17_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile28_node17_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node17 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,96] 6 (by decide) (choices 2) [9,24,129,136] profile28_node17_route profile28_node17_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node18
  · exact profile28_node19
  · exact profile28_node20
  · exact profile28_node21

def profile28_node22_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 25 131 253 249 249 249 249 128), lower := (rows 25 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 147 131 132 128 144 160 192 128) }] }

theorem profile28_node22 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,129] 6 249 profile28_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,129] 6 249 profile28_node22_cert).mp (by decide +kernel))

def profile28_node23_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 25 138 245 249 241 241 241 128), lower := (rows 25 138 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 11 4 8 16 32 64 255), good := (rows 154 138 132 138 144 160 192 128) }] }

theorem profile28_node23 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,136] 6 241 profile28_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,136] 6 241 profile28_node23_cert).mp (by decide +kernel))

def profile28_node24_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 25 162 221 217 217 249 217 128), lower := (rows 25 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 64 255), good := (rows 152 162 132 136 144 162 192 128) }] }

theorem profile28_node24 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,160] 6 217 profile28_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24,160] 6 217 profile28_node24_cert).mp (by decide +kernel))

def profile28_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile28_node1_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile28_node1 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [24] 6 (by decide) (choices 2) [9,24,33,40,96,129,136,160] profile28_node1_route profile28_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node2
  · exact profile28_node3
  · exact profile28_node4
  · exact profile28_node16
  · exact profile28_node17
  · exact profile28_node22
  · exact profile28_node23
  · exact profile28_node24

def profile28_node26_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 41 11 213 217 209 241 209 128), lower := (rows 41 11 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 7 0 19 35 67 255), good := (rows 245 247 132 128 144 160 192 128) }] }

theorem profile28_node26 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,9] 6 209 profile28_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,9] 6 209 profile28_node26_cert).mp (by decide +kernel))

def profile28_node28_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 41 19 13 216 208 240 208 128), lower := (rows 41 19 13 8 16 32 64 128), losses := [] }

theorem profile28_node28 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,9] 6 208 profile28_node28_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,9] 6 208 profile28_node28_cert).mp (by decide +kernel))

def profile28_node29_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 41 19 21 200 216 232 200 128), lower := (rows 41 19 21 8 16 32 64 128), losses := [] }

theorem profile28_node29 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,17] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,17] 6 200 profile28_node29_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,17] 6 200 profile28_node29_cert).mp (by decide +kernel))

def profile28_node30_cert : Bound 8 := { allowed := (rows 144 136 129 0 0 0 0 0), upper := (rows 41 19 28 201 209 225 193 128), lower := (rows 41 19 28 8 16 32 64 128), losses := [] }

theorem profile28_node30 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,24] 6 193 profile28_node30_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,24] 6 193 profile28_node30_cert).mp (by decide +kernel))

def profile28_node32_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 41 19 69 24 152 168 200 128), lower := (rows 41 19 69 24 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 15 8 0 41 73 255), good := (rows 237 231 229 237 128 160 192 128) }] }

theorem profile28_node32 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65,16] 6 136 profile28_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65,16] 6 136 profile28_node32_cert).mp (by decide +kernel))

def profile28_node33_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 19 69 136 152 184 216 128), lower := (rows 41 19 69 136 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 255 0 32 64 255), good := (rows 169 139 205 136 136 169 200 136) }] }

theorem profile28_node33 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65,128] 6 152 profile28_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65,128] 6 152 profile28_node33_cert).mp (by decide +kernel))

def profile28_node31_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile28_node31_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node31 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,65] 6 (by decide) (choices 1) [16,128] profile28_node31_route profile28_node31_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node32
  · exact profile28_node33

def profile28_node34_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 19 76 153 145 177 209 128), lower := (rows 41 19 76 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67 255), good := (rows 243 243 196 128 144 160 192 128) }] }

theorem profile28_node34 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,72] 6 145 profile28_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,72] 6 145 profile28_node34_cert).mp (by decide +kernel))

def profile28_node35_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 19 84 137 153 169 201 128), lower := (rows 41 19 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile28_node35 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,80] 6 137 profile28_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,80] 6 137 profile28_node35_cert).mp (by decide +kernel))

def profile28_node36_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 41 19 133 216 216 248 216 128), lower := (rows 41 19 133 8 16 32 64 128), losses := [] }

theorem profile28_node36 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,129] 6 216 profile28_node36_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,129] 6 216 profile28_node36_cert).mp (by decide +kernel))

def profile28_node37_cert : Bound 8 := { allowed := (rows 144 136 17 0 0 0 0 0), upper := (rows 41 19 140 217 209 241 209 128), lower := (rows 41 19 140 8 16 32 64 128), losses := [] }

theorem profile28_node37 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,136] 6 209 profile28_node37_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,136] 6 209 profile28_node37_cert).mp (by decide +kernel))

def profile28_node38_cert : Bound 8 := { allowed := (rows 144 136 9 0 0 0 0 0), upper := (rows 41 19 148 201 217 233 201 128), lower := (rows 41 19 148 8 16 32 64 128), losses := [] }

theorem profile28_node38 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,144] 6 201 profile28_node38_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,144] 6 201 profile28_node38_cert).mp (by decide +kernel))

def profile28_node39_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 41 19 196 153 153 185 217 128), lower := (rows 41 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 68 8 16 32 64 255), good := (rows 168 146 196 136 144 160 196 128) }] }

theorem profile28_node39 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,192] 6 153 profile28_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17,192] 6 153 profile28_node39_cert).mp (by decide +kernel))

def profile28_node27_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile28_node27_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node27 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,17] 6 (by decide) (choices 2) [9,17,24,65,72,80,129,136,144,192] profile28_node27_route profile28_node27_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node28
  · exact profile28_node29
  · exact profile28_node30
  · exact profile28_node31
  · exact profile28_node34
  · exact profile28_node35
  · exact profile28_node36
  · exact profile28_node37
  · exact profile28_node38
  · exact profile28_node39

def profile28_node40_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 41 26 213 217 209 241 209 128), lower := (rows 41 26 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 146 132 128 144 160 192 128) }] }

theorem profile28_node40 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,24] 6 209 profile28_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,24] 6 209 profile28_node40_cert).mp (by decide +kernel))

def profile28_node42_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 67 13 152 144 176 208 128), lower := (rows 41 67 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 7 4 0 255 255 255 255), good := (rows 243 243 247 240 240 240 240 240) }] }

theorem profile28_node42 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,9] 6 144 profile28_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,9] 6 144 profile28_node42_cert).mp (by decide +kernel))

def profile28_node44_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 41 67 21 24 152 168 200 128), lower := (rows 41 67 21 24 16 32 64 128), losses := [{ target := 4, region := (rows 9 15 4 8 0 41 73 255), good := (rows 235 227 231 235 128 160 192 128) }] }

theorem profile28_node44 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17,16] 6 136 profile28_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17,16] 6 136 profile28_node44_cert).mp (by decide +kernel))

def profile28_node45_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 67 21 136 152 184 216 128), lower := (rows 41 67 21 136 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 255 0 32 64 255), good := (rows 169 203 141 136 136 169 200 136) }] }

theorem profile28_node45 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17,128] 6 152 profile28_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17,128] 6 152 profile28_node45_cert).mp (by decide +kernel))

def profile28_node43_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile28_node43_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node43 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,17] 6 (by decide) (choices 1) [16,128] profile28_node43_route profile28_node43_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node44
  · exact profile28_node45

def profile28_node46_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 67 28 153 145 177 209 128), lower := (rows 41 67 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 19 35 67 255), good := (rows 243 243 148 128 144 160 192 128) }] }

theorem profile28_node46 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,24] 6 145 profile28_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,24] 6 145 profile28_node46_cert).mp (by decide +kernel))

def profile28_node47_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 41 67 133 152 152 184 216 128), lower := (rows 41 67 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 7 0 16 32 64 255), good := (rows 165 199 133 128 144 160 192 128) }] }

theorem profile28_node47 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,129] 6 152 profile28_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,129] 6 152 profile28_node47_cert).mp (by decide +kernel))

def profile28_node48_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 41 67 140 153 145 177 209 128), lower := (rows 41 67 140 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 13 8 16 32 64 255), good := (rows 172 198 140 140 144 160 192 128) }] }

theorem profile28_node48 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,136] 6 145 profile28_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,136] 6 145 profile28_node48_cert).mp (by decide +kernel))

def profile28_node49_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 41 67 148 153 153 185 217 128), lower := (rows 41 67 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 64 255), good := (rows 168 194 148 136 148 160 192 128) }] }

theorem profile28_node49 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,144] 6 153 profile28_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65,144] 6 153 profile28_node49_cert).mp (by decide +kernel))

def profile28_node41_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile28_node41_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node41 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,65] 6 (by decide) (choices 2) [9,17,24,129,136,144] profile28_node41_route profile28_node41_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node42
  · exact profile28_node43
  · exact profile28_node46
  · exact profile28_node47
  · exact profile28_node48
  · exact profile28_node49

def profile28_node50_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 41 74 149 153 145 177 209 128), lower := (rows 41 74 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 255), good := (rows 245 194 132 128 144 160 192 128) }] }

theorem profile28_node50 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,72] 6 145 profile28_node50_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,72] 6 145 profile28_node50_cert).mp (by decide +kernel))

def profile28_node52_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 82 13 153 145 177 209 128), lower := (rows 41 82 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 7 4 0 21 37 69 255), good := (rows 243 210 247 128 144 160 192 128) }] }

theorem profile28_node52 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,9] 6 145 profile28_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,9] 6 145 profile28_node52_cert).mp (by decide +kernel))

def profile28_node53_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 82 21 137 153 169 201 128), lower := (rows 41 82 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile28_node53 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,17] 6 137 profile28_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,17] 6 137 profile28_node53_cert).mp (by decide +kernel))

def profile28_node54_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 82 28 137 145 161 193 128), lower := (rows 41 82 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 17 33 65 255), good := (rows 243 210 148 128 144 160 192 128) }] }

theorem profile28_node54 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,24] 6 129 profile28_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,24] 6 129 profile28_node54_cert).mp (by decide +kernel))

def profile28_node55_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 41 82 133 153 153 185 217 128), lower := (rows 41 82 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 255), good := (rows 165 210 133 128 144 160 192 128) }] }

theorem profile28_node55 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,129] 6 153 profile28_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,129] 6 153 profile28_node55_cert).mp (by decide +kernel))

def profile28_node56_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 41 82 140 153 145 177 209 128), lower := (rows 41 82 140 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 13 8 16 32 64 255), good := (rows 172 210 140 140 144 160 192 128) }] }

theorem profile28_node56 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,136] 6 145 profile28_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,136] 6 145 profile28_node56_cert).mp (by decide +kernel))

def profile28_node57_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 41 82 148 137 153 169 201 128), lower := (rows 41 82 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 64 255), good := (rows 168 214 148 136 148 160 192 128) }] }

theorem profile28_node57 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,144] 6 137 profile28_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80,144] 6 137 profile28_node57_cert).mp (by decide +kernel))

def profile28_node51_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile28_node51_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node51 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,80] 6 (by decide) (choices 2) [9,17,24,129,136,144] profile28_node51_route profile28_node51_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node52
  · exact profile28_node53
  · exact profile28_node54
  · exact profile28_node55
  · exact profile28_node56
  · exact profile28_node57

def profile28_node58_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 131 221 217 217 249 217 128), lower := (rows 41 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 163 131 132 128 144 160 192 128) }] }

theorem profile28_node58 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,129] 6 217 profile28_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,129] 6 217 profile28_node58_cert).mp (by decide +kernel))

def profile28_node59_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 41 138 213 217 209 241 209 128), lower := (rows 41 138 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 11 4 8 16 32 64 255), good := (rows 170 138 132 138 144 160 192 128) }] }

theorem profile28_node59 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,136] 6 209 profile28_node59_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,136] 6 209 profile28_node59_cert).mp (by decide +kernel))

def profile28_node60_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 41 146 221 217 217 249 217 128), lower := (rows 41 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 64 255), good := (rows 168 146 132 136 146 160 192 128) }] }

theorem profile28_node60 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,144] 6 217 profile28_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,144] 6 217 profile28_node60_cert).mp (by decide +kernel))

def profile28_node61_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 41 194 157 153 153 185 217 128), lower := (rows 41 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 66 4 8 16 32 64 255), good := (rows 168 194 132 136 144 160 194 128) }] }

theorem profile28_node61 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,192] 6 153 profile28_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40,192] 6 153 profile28_node61_cert).mp (by decide +kernel))

def profile28_node25_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile28_node25_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node25 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [40] 6 (by decide) (choices 2) [9,17,24,65,72,80,129,136,144,192] profile28_node25_route profile28_node25_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node26
  · exact profile28_node27
  · exact profile28_node40
  · exact profile28_node41
  · exact profile28_node50
  · exact profile28_node51
  · exact profile28_node58
  · exact profile28_node59
  · exact profile28_node60
  · exact profile28_node61

def profile28_node64_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 97 11 13 152 144 176 208 128), lower := (rows 97 11 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 255 2 4 0 255 255 255 255), good := (rows 241 243 245 241 241 241 241 241) }] }

theorem profile28_node64 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,9] 6 144 profile28_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,9] 6 144 profile28_node64_cert).mp (by decide +kernel))

def profile28_node66_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 97 11 21 24 152 168 200 128), lower := (rows 97 11 21 24 16 32 64 128), losses := [{ target := 4, region := (rows 11 10 4 8 0 42 74 255), good := (rows 225 235 133 235 128 160 192 128) }] }

theorem profile28_node66 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17,16] 6 136 profile28_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17,16] 6 136 profile28_node66_cert).mp (by decide +kernel))

def profile28_node67_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 97 11 21 136 152 184 216 128), lower := (rows 97 11 21 136 16 32 64 128), losses := [{ target := 4, region := (rows 1 7 4 255 0 32 64 255), good := (rows 235 139 143 136 136 168 200 136) }] }

theorem profile28_node67 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17,128] 6 152 profile28_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17,128] 6 152 profile28_node67_cert).mp (by decide +kernel))

def profile28_node65_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile28_node65_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node65 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,17] 6 (by decide) (choices 1) [16,128] profile28_node65_route profile28_node65_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile28_node66
  · exact profile28_node67

def profile28_node68_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 97 11 28 153 145 177 209 128), lower := (rows 97 11 28 8 16 32 64 128), losses := [{ target := 3, region := (rows 255 2 4 0 255 255 255 255), good := (rows 241 243 245 241 241 241 241 241) }] }

theorem profile28_node68 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,24] 6 145 profile28_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,24] 6 145 profile28_node68_cert).mp (by decide +kernel))

def profile28_node69_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 97 11 133 152 152 184 216 128), lower := (rows 97 11 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 7 0 16 32 64 255), good := (rows 229 135 133 128 144 160 192 128) }] }

theorem profile28_node69 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,129] 6 152 profile28_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,129] 6 152 profile28_node69_cert).mp (by decide +kernel))

def profile28_node70_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 97 11 140 153 145 177 209 128), lower := (rows 97 11 140 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 14 8 16 32 64 255), good := (rows 224 142 140 140 144 160 192 128) }] }

theorem profile28_node70 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,136] 6 145 profile28_node70_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,136] 6 145 profile28_node70_cert).mp (by decide +kernel))

def profile28_node71_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 97 11 148 153 153 185 217 128), lower := (rows 97 11 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 64 255), good := (rows 224 138 148 136 148 160 192 128) }] }

theorem profile28_node71 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,144] 6 153 profile28_node71_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9,144] 6 153 profile28_node71_cert).mp (by decide +kernel))

def profile28_node63_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile28_node63_route : Route 8 := (fun mask => (mask,id))

theorem profile28_node63 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,9] 6 (by decide) (choices 2) [9,17,24,129,136,144] profile28_node63_route profile28_node63_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile28_node64
  · exact profile28_node65
  · exact profile28_node68
  · exact profile28_node69
  · exact profile28_node70
  · exact profile28_node71

def profile28_node73_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 97 26 13 153 145 177 209 128), lower := (rows 97 26 13 8 16 32 64 128), losses := [{ target := 3, region := (rows 255 2 4 0 255 255 255 255), good := (rows 241 243 245 241 241 241 241 241) }] }

theorem profile28_node73 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,9] 6 145 profile28_node73_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,9] 6 145 profile28_node73_cert).mp (by decide +kernel))

def profile28_node74_cert : CutBound 8 := { lost := (rows 0 1 1 0 0 0 0 0), upper := (rows 97 26 28 137 145 161 193 128), lower := (rows 97 26 28 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 6 6 8 16 32 64 255), good := (rows 224 158 158 136 144 160 192 128) }] }

theorem profile28_node74 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,24] 6 129 profile28_node74_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,24] 6 129 profile28_node74_cert).mp (by decide +kernel))

def profile28_node75_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 97 26 133 153 153 185 217 128), lower := (rows 97 26 133 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 255), good := (rows 229 146 133 128 144 160 192 128) }] }

theorem profile28_node75 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,129] 6 153 profile28_node75_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,129] 6 153 profile28_node75_cert).mp (by decide +kernel))

def profile28_node76_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 97 26 140 153 145 177 209 128), lower := (rows 97 26 140 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 14 8 16 32 64 255), good := (rows 224 158 140 140 144 160 192 128) }] }

theorem profile28_node76 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,136] 6 145 profile28_node76_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24,136] 6 145 profile28_node76_cert).mp (by decide +kernel))

def profile28_node72_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile28_node72_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node72 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,24] 6 (by decide) (choices 2) [9,24,129,136] profile28_node72_route profile28_node72_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node73
  · exact profile28_node74
  · exact profile28_node75
  · exact profile28_node76

def profile28_node77_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 97 131 157 153 153 185 217 128), lower := (rows 97 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 227 131 132 128 144 160 192 128) }] }

theorem profile28_node77 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,129] 6 153 profile28_node77_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,129] 6 153 profile28_node77_cert).mp (by decide +kernel))

def profile28_node78_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 97 138 157 153 153 185 217 128), lower := (rows 97 138 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 10 4 8 16 32 64 255), good := (rows 224 138 132 138 144 160 192 128) }] }

theorem profile28_node78 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,136] 6 153 profile28_node78_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96,136] 6 153 profile28_node78_cert).mp (by decide +kernel))

def profile28_node62_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile28_node62_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile28_node62 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [96] 6 (by decide) (choices 2) [9,24,129,136] profile28_node62_route profile28_node62_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile28_node63
  · exact profile28_node72
  · exact profile28_node77
  · exact profile28_node78

def profile28_node79_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 137 251 253 249 249 249 249 128), lower := (rows 137 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 4 8 0 32 64 255), good := (rows 137 130 132 137 128 160 192 128) }] }

theorem profile28_node79 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [136] 6 249 profile28_node79_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [136] 6 249 profile28_node79_cert).mp (by decide +kernel))

def profile28_node80_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 161 219 221 217 217 249 217 128), lower := (rows 161 2 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 33 2 4 0 16 32 64 255), good := (rows 161 130 132 128 144 161 192 128) }] }

theorem profile28_node80 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [160] 6 217 profile28_node80_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [160] 6 217 profile28_node80_cert).mp (by decide +kernel))

def profile28_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile28_node0_route : Route 8 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile28_node0 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [] 6 (by decide) (choices 2) [24,40,96,136,160] profile28_node0_route profile28_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile28_node1
  · exact profile28_node25
  · exact profile28_node62
  · exact profile28_node79
  · exact profile28_node80

theorem profile28 : Upper (D (n:=8) [34,32,32,18,18,17,17,2]) (R (n:=8) [34,32,32,18,18,17,17,2]) [] 6 := profile28_node0


#print axioms profile28
end Delivery.SmallBudgetTenFinite8
