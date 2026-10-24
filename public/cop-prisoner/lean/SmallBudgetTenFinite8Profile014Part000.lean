import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile14_node3_cert : CutBound 8 := { lost := (rows 128 128 128 0 0 0 0 0), upper := (rows 7 11 100 232 240 32 64 128), lower := (rows 7 11 100 8 16 32 64 128), losses := [{ target := 7, region := (rows 11 10 255 8 16 255 255 0), good := (rows 103 111 100 111 116 100 100 100) }] }

theorem profile14_node3 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,9,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,9,96] 6 224 profile14_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,9,96] 6 224 profile14_node3_cert).mp (by decide +kernel))

def profile14_node2_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node2_route : Route 8 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node2 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,9] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,9] 6 (by decide) (choices 2) [96] profile14_node2_route profile14_node2_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile14_node3

def profile14_node4_cert : CutBound 8 := { lost := (rows 192 192 0 0 0 0 0 0), upper := (rows 7 35 236 232 248 32 64 128), lower := (rows 7 35 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 5 7 4 8 16 255 0 255), good := (rows 167 163 167 168 176 160 160 160) },{ target := 7, region := (rows 5 7 4 8 16 255 255 0), good := (rows 103 99 103 104 112 96 96 96) }] }

theorem profile14_node4 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,33] 6 232 profile14_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,33] 6 232 profile14_node4_cert).mp (by decide +kernel))

def profile14_node6_cert : CutBound 8 := { lost := (rows 64 64 64 32 32 0 0 0), upper := (rows 7 42 37 200 208 32 64 128), lower := (rows 7 42 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 255 255 0 255 255), good := (rows 223 218 221 216 216 216 216 216) },{ target := 6, region := (rows 11 10 15 8 16 255 0 255), good := (rows 167 175 165 175 176 160 160 160) }] }

theorem profile14_node6 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,33] 6 192 profile14_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,33] 6 192 profile14_node6_cert).mp (by decide +kernel))

def profile14_node7_cert : CutBound 8 := { lost := (rows 32 64 32 0 0 0 0 0), upper := (rows 7 42 69 232 240 32 64 128), lower := (rows 7 42 69 8 16 32 64 128), losses := [{ target := 5, region := (rows 3 2 7 8 16 0 255 255), good := (rows 199 207 197 200 208 192 192 192) },{ target := 6, region := (rows 1 10 4 8 16 255 0 255), good := (rows 167 170 165 170 176 160 160 160) }] }

theorem profile14_node7 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,65] 6 224 profile14_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,65] 6 224 profile14_node7_cert).mp (by decide +kernel))

def profile14_node8_cert : CutBound 8 := { lost := (rows 0 64 0 32 32 0 0 0), upper := (rows 7 42 100 201 209 32 64 128), lower := (rows 7 42 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 223 202 196 200 208 192 192 192) },{ target := 6, region := (rows 1 10 4 8 16 255 0 255), good := (rows 167 170 164 170 176 160 160 160) }] }

theorem profile14_node8 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,96] 6 193 profile14_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,96] 6 193 profile14_node8_cert).mp (by decide +kernel))

def profile14_node9_cert : CutBound 8 := { lost := (rows 32 64 32 0 0 0 0 0), upper := (rows 7 42 196 233 241 32 64 128), lower := (rows 7 42 196 8 16 32 64 128), losses := [{ target := 5, region := (rows 3 2 255 8 16 0 255 255), good := (rows 199 207 196 204 212 196 196 196) },{ target := 6, region := (rows 1 10 4 8 16 255 0 255), good := (rows 167 170 164 170 176 160 160 160) }] }

theorem profile14_node9 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,192] 6 225 profile14_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40,192] 6 225 profile14_node9_cert).mp (by decide +kernel))

def profile14_node5_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node5_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile14_node5 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,40] 6 (by decide) (choices 2) [33,65,96,192] profile14_node5_route profile14_node5_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node6
  · exact profile14_node7
  · exact profile14_node8
  · exact profile14_node9

def profile14_node11_cert : CutBound 8 := { lost := (rows 128 128 128 0 0 0 0 0), upper := (rows 7 98 13 232 240 32 64 128), lower := (rows 7 98 13 8 16 32 64 128), losses := [{ target := 7, region := (rows 13 255 12 8 16 255 255 0), good := (rows 103 98 111 111 114 98 98 98) }] }

theorem profile14_node11 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,9] 6 224 profile14_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,9] 6 224 profile14_node11_cert).mp (by decide +kernel))

def profile14_node12_cert : CutBound 8 := { lost := (rows 64 0 64 32 32 0 0 0), upper := (rows 7 98 37 200 216 32 64 128), lower := (rows 7 98 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 255 255 0 255 255), good := (rows 223 218 221 216 216 216 216 216) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile14_node12 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,33] 6 200 profile14_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,33] 6 200 profile14_node12_cert).mp (by decide +kernel))

def profile14_node13_cert : CutBound 8 := { lost := (rows 0 0 64 32 32 0 0 0), upper := (rows 7 98 44 201 209 32 64 128), lower := (rows 7 98 44 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 223 194 204 200 208 192 192 192) },{ target := 6, region := (rows 1 2 12 8 16 255 0 255), good := (rows 167 162 172 172 176 160 160 160) }] }

theorem profile14_node13 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,40] 6 193 profile14_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,40] 6 193 profile14_node13_cert).mp (by decide +kernel))

def profile14_node14_cert : CutBound 8 := { lost := (rows 0 0 0 96 96 0 0 0), upper := (rows 7 98 100 137 153 32 64 128), lower := (rows 7 98 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 9 17 255 0 255), good := (rows 191 162 164 168 176 160 160 160) }] }

theorem profile14_node14 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,96] 6 137 profile14_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,96] 6 137 profile14_node14_cert).mp (by decide +kernel))

def profile14_node15_cert : CutBound 8 := { lost := (rows 96 0 96 0 0 0 0 0), upper := (rows 7 98 133 232 248 32 64 128), lower := (rows 7 98 133 8 16 32 64 128), losses := [{ target := 5, region := (rows 3 2 7 8 16 0 255 255), good := (rows 199 199 197 200 208 192 192 192) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile14_node15 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,129] 6 232 profile14_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,129] 6 232 profile14_node15_cert).mp (by decide +kernel))

def profile14_node16_cert : CutBound 8 := { lost := (rows 128 128 96 0 0 0 0 0), upper := (rows 7 98 140 233 241 32 64 128), lower := (rows 7 98 140 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 255 255), good := (rows 199 194 204 204 208 192 192 192) },{ target := 6, region := (rows 1 2 12 8 16 255 0 255), good := (rows 167 162 172 172 176 160 160 160) },{ target := 7, region := (rows 5 255 4 8 16 255 255 0), good := (rows 103 98 111 106 114 98 98 98) }] }

theorem profile14_node16 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,136] 6 225 profile14_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,136] 6 225 profile14_node16_cert).mp (by decide +kernel))

def profile14_node17_cert : CutBound 8 := { lost := (rows 64 0 64 32 32 0 0 0), upper := (rows 7 98 164 201 217 32 64 128), lower := (rows 7 98 164 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) }] }

theorem profile14_node17 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,160] 6 201 profile14_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96,160] 6 201 profile14_node17_cert).mp (by decide +kernel))

def profile14_node10_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node10_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node10 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6,96] 6 (by decide) (choices 2) [9,33,40,96,129,136,160] profile14_node10_route profile14_node10_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node11
  · exact profile14_node12
  · exact profile14_node13
  · exact profile14_node14
  · exact profile14_node15
  · exact profile14_node16
  · exact profile14_node17

def profile14_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node1_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node1 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [6] 6 (by decide) (choices 2) [9,33,40,96] profile14_node1_route profile14_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node2
  · exact profile14_node4
  · exact profile14_node5
  · exact profile14_node10

def profile14_node19_cert : CutBound 8 := { lost := (rows 192 192 0 0 0 0 0 0), upper := (rows 35 7 236 232 248 32 64 128), lower := (rows 35 7 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 7 6 4 8 16 255 0 255), good := (rows 163 167 167 168 176 160 160 160) },{ target := 7, region := (rows 7 6 4 8 16 255 255 0), good := (rows 99 103 103 104 112 96 96 96) }] }

theorem profile14_node19 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,5] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,5] 6 232 profile14_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,5] 6 232 profile14_node19_cert).mp (by decide +kernel))

def profile14_node21_cert : CutBound 8 := { lost := (rows 0 32 0 32 32 0 0 0), upper := (rows 35 14 37 200 208 32 64 128), lower := (rows 35 14 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 6 4 255 255 0 255 255), good := (rows 219 222 223 216 216 216 216 216) }] }

theorem profile14_node21 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,33] 6 192 profile14_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,33] 6 192 profile14_node21_cert).mp (by decide +kernel))

def profile14_node22_cert : CutBound 8 := { lost := (rows 192 128 160 0 0 0 0 0), upper := (rows 35 14 69 232 240 32 64 128), lower := (rows 35 14 69 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 199 206 197 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 175 165 168 176 160 160 160) },{ target := 7, region := (rows 11 10 15 8 16 255 255 0), good := (rows 103 111 101 111 112 96 96 96) }] }

theorem profile14_node22 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,65] 6 224 profile14_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,65] 6 224 profile14_node22_cert).mp (by decide +kernel))

def profile14_node23_cert : CutBound 8 := { lost := (rows 64 0 0 32 32 0 0 0), upper := (rows 35 14 100 201 209 32 64 128), lower := (rows 35 14 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 219 206 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 175 164 168 176 160 160 160) }] }

theorem profile14_node23 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,96] 6 193 profile14_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,96] 6 193 profile14_node23_cert).mp (by decide +kernel))

def profile14_node24_cert : CutBound 8 := { lost := (rows 64 32 32 0 0 0 0 0), upper := (rows 35 14 196 233 241 32 64 128), lower := (rows 35 14 196 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 10 255 8 16 0 255 255), good := (rows 199 206 196 206 212 196 196 196) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 175 164 168 176 160 160 160) }] }

theorem profile14_node24 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,192] 6 225 profile14_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12,192] 6 225 profile14_node24_cert).mp (by decide +kernel))

def profile14_node20_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node20_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile14_node20 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,12] 6 (by decide) (choices 2) [33,65,96,192] profile14_node20_route profile14_node20_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile14_node21
  · exact profile14_node22
  · exact profile14_node23
  · exact profile14_node24

def profile14_node25_cert : CutBound 8 := { lost := (rows 0 0 32 32 32 0 0 0), upper := (rows 35 35 204 204 220 32 64 128), lower := (rows 35 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 223 223 220 220 220 220 220 220) }] }

theorem profile14_node25 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,33] 6 204 profile14_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,33] 6 204 profile14_node25_cert).mp (by decide +kernel))

def profile14_node26_cert : CutBound 8 := { lost := (rows 0 0 32 32 32 0 0 0), upper := (rows 35 38 205 201 217 32 64 128), lower := (rows 35 38 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 198 196 200 208 192 192 192) }] }

theorem profile14_node26 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,36] 6 201 profile14_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,36] 6 201 profile14_node26_cert).mp (by decide +kernel))

def profile14_node27_cert : CutBound 8 := { lost := (rows 192 160 0 0 0 0 0 0), upper := (rows 35 67 236 236 252 32 64 128), lower := (rows 35 67 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile14_node27 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,65] 6 236 profile14_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,65] 6 236 profile14_node27_cert).mp (by decide +kernel))

def profile14_node28_cert : CutBound 8 := { lost := (rows 192 160 0 0 0 0 0 0), upper := (rows 35 70 237 233 249 32 64 128), lower := (rows 35 70 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 255 255), good := (rows 195 198 198 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 167 164 168 176 160 160 160) },{ target := 7, region := (rows 7 6 4 8 16 255 255 0), good := (rows 99 103 103 104 112 96 96 96) }] }

theorem profile14_node28 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,68] 6 233 profile14_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,68] 6 233 profile14_node28_cert).mp (by decide +kernel))

def profile14_node29_cert : CutBound 8 := { lost := (rows 0 0 32 32 32 0 0 0), upper := (rows 35 98 205 205 221 32 64 128), lower := (rows 35 98 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile14_node29 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,96] 6 205 profile14_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,96] 6 205 profile14_node29_cert).mp (by decide +kernel))

def profile14_node30_cert : CutBound 8 := { lost := (rows 192 32 0 0 0 0 0 0), upper := (rows 35 194 237 237 253 32 64 128), lower := (rows 35 194 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 195 194 198 202 210 194 194 194) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 3 2 4 8 16 255 255 0), good := (rows 99 99 100 104 112 96 96 96) }] }

theorem profile14_node30 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,192] 6 237 profile14_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34,192] 6 237 profile14_node30_cert).mp (by decide +kernel))

def profile14_node18_column : Nat → Fin 8 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node18_route : Route 8 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile14_node18 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [34] 6 (by decide) (choices 2) [5,12,33,36,65,68,96,192] profile14_node18_route profile14_node18_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node19
  · exact profile14_node20
  · exact profile14_node25
  · exact profile14_node26
  · exact profile14_node27
  · exact profile14_node28
  · exact profile14_node29
  · exact profile14_node30

def profile14_node33_cert : CutBound 8 := { lost := (rows 128 128 128 0 0 0 0 0), upper := (rows 97 7 14 232 240 32 64 128), lower := (rows 97 7 14 8 16 32 64 128), losses := [{ target := 7, region := (rows 255 14 12 8 16 255 255 0), good := (rows 97 103 111 111 113 97 97 97) }] }

theorem profile14_node33 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,10] 6 224 profile14_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,10] 6 224 profile14_node33_cert).mp (by decide +kernel))

def profile14_node34_cert : CutBound 8 := { lost := (rows 0 64 64 32 32 0 0 0), upper := (rows 97 7 38 200 216 32 64 128), lower := (rows 97 7 38 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 255 255 0 255 255), good := (rows 217 223 222 216 216 216 216 216) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) }] }

theorem profile14_node34 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,34] 6 200 profile14_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,34] 6 200 profile14_node34_cert).mp (by decide +kernel))

def profile14_node35_cert : CutBound 8 := { lost := (rows 0 0 64 32 32 0 0 0), upper := (rows 97 7 44 202 210 32 64 128), lower := (rows 97 7 44 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 255 255), good := (rows 193 223 204 200 208 192 192 192) },{ target := 6, region := (rows 1 2 12 8 16 255 0 255), good := (rows 161 167 172 172 176 160 160 160) }] }

theorem profile14_node35 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,40] 6 194 profile14_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,40] 6 194 profile14_node35_cert).mp (by decide +kernel))

def profile14_node36_cert : CutBound 8 := { lost := (rows 0 0 0 96 96 0 0 0), upper := (rows 97 7 100 138 154 32 64 128), lower := (rows 97 7 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 10 18 255 0 255), good := (rows 161 191 164 168 176 160 160 160) }] }

theorem profile14_node36 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,96] 6 138 profile14_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,96] 6 138 profile14_node36_cert).mp (by decide +kernel))

def profile14_node37_cert : CutBound 8 := { lost := (rows 0 96 96 0 0 0 0 0), upper := (rows 97 7 134 232 248 32 64 128), lower := (rows 97 7 134 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 199 199 198 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) }] }

theorem profile14_node37 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,130] 6 232 profile14_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,130] 6 232 profile14_node37_cert).mp (by decide +kernel))

def profile14_node38_cert : CutBound 8 := { lost := (rows 128 128 96 0 0 0 0 0), upper := (rows 97 7 140 234 242 32 64 128), lower := (rows 97 7 140 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 255 255), good := (rows 193 199 204 204 208 192 192 192) },{ target := 6, region := (rows 1 2 12 8 16 255 0 255), good := (rows 161 167 172 172 176 160 160 160) },{ target := 7, region := (rows 255 6 4 8 16 255 255 0), good := (rows 97 103 111 105 113 97 97 97) }] }

theorem profile14_node38 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,136] 6 226 profile14_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,136] 6 226 profile14_node38_cert).mp (by decide +kernel))

def profile14_node39_cert : CutBound 8 := { lost := (rows 0 64 64 32 32 0 0 0), upper := (rows 97 7 164 202 218 32 64 128), lower := (rows 97 7 164 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) }] }

theorem profile14_node39 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,160] 6 202 profile14_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5,160] 6 202 profile14_node39_cert).mp (by decide +kernel))

def profile14_node32_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node32_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node32 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,5] 6 (by decide) (choices 2) [10,34,40,96,130,136,160] profile14_node32_route profile14_node32_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node33
  · exact profile14_node34
  · exact profile14_node35
  · exact profile14_node36
  · exact profile14_node37
  · exact profile14_node38
  · exact profile14_node39

def profile14_node41_cert : CutBound 8 := { lost := (rows 128 128 128 0 0 0 0 0), upper := (rows 97 14 7 232 240 32 64 128), lower := (rows 97 14 7 8 16 32 64 128), losses := [{ target := 7, region := (rows 255 10 14 8 16 255 255 0), good := (rows 97 111 103 111 113 97 97 97) }] }

theorem profile14_node41 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,3] 6 224 profile14_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,3] 6 224 profile14_node41_cert).mp (by decide +kernel))

def profile14_node42_cert : CutBound 8 := { lost := (rows 0 32 0 32 32 0 0 0), upper := (rows 97 14 37 202 210 32 64 128), lower := (rows 97 14 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 6 4 14 22 0 255 255), good := (rows 193 222 223 200 208 192 192 192) }] }

theorem profile14_node42 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,33] 6 194 profile14_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,33] 6 194 profile14_node42_cert).mp (by decide +kernel))

def profile14_node43_cert : CutBound 8 := { lost := (rows 0 64 64 32 32 0 0 0), upper := (rows 97 14 38 201 209 32 64 128), lower := (rows 97 14 38 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 255 255), good := (rows 217 206 198 200 208 192 192 192) },{ target := 6, region := (rows 1 10 14 8 16 255 0 255), good := (rows 161 174 166 174 176 160 160 160) }] }

theorem profile14_node43 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,34] 6 193 profile14_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,34] 6 193 profile14_node43_cert).mp (by decide +kernel))

def profile14_node44_cert : CutBound 8 := { lost := (rows 128 128 128 0 0 0 0 0), upper := (rows 97 14 100 139 147 32 64 128), lower := (rows 97 14 100 8 16 32 64 128), losses := [{ target := 7, region := (rows 255 10 255 8 16 255 255 0), good := (rows 101 111 101 111 117 101 101 101) }] }

theorem profile14_node44 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,96] 6 131 profile14_node44_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,96] 6 131 profile14_node44_cert).mp (by decide +kernel))

def profile14_node45_cert : CutBound 8 := { lost := (rows 128 0 96 0 0 0 0 0), upper := (rows 97 14 133 234 242 32 64 128), lower := (rows 97 14 133 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 206 197 200 208 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 255 0 255), good := (rows 165 174 165 168 176 160 160 160) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 111 101 105 113 97 97 97) }] }

theorem profile14_node45 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,129] 6 226 profile14_node45_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,129] 6 226 profile14_node45_cert).mp (by decide +kernel))

def profile14_node46_cert : CutBound 8 := { lost := (rows 0 96 96 0 0 0 0 0), upper := (rows 97 14 134 233 241 32 64 128), lower := (rows 97 14 134 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 10 14 8 16 0 255 255), good := (rows 193 206 198 206 208 192 192 192) },{ target := 6, region := (rows 1 10 14 8 16 255 0 255), good := (rows 161 174 166 174 176 160 160 160) }] }

theorem profile14_node46 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,130] 6 225 profile14_node46_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,130] 6 225 profile14_node46_cert).mp (by decide +kernel))

def profile14_node47_cert : CutBound 8 := { lost := (rows 128 64 64 0 0 0 0 0), upper := (rows 97 14 164 203 211 32 64 128), lower := (rows 97 14 164 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 10 255 8 16 255 0 255), good := (rows 165 174 164 174 180 164 164 164) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 111 101 105 113 97 97 97) }] }

theorem profile14_node47 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,160] 6 195 profile14_node47_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12,160] 6 195 profile14_node47_cert).mp (by decide +kernel))

def profile14_node40_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node40_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node40 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,12] 6 (by decide) (choices 2) [3,33,34,96,129,130,160] profile14_node40_route profile14_node40_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node41
  · exact profile14_node42
  · exact profile14_node43
  · exact profile14_node44
  · exact profile14_node45
  · exact profile14_node46
  · exact profile14_node47

def profile14_node48_cert : CutBound 8 := { lost := (rows 0 0 32 32 32 0 0 0), upper := (rows 97 35 206 206 222 32 64 128), lower := (rows 97 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) }] }

theorem profile14_node48 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,33] 6 206 profile14_node48_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,33] 6 206 profile14_node48_cert).mp (by decide +kernel))

def profile14_node49_cert : CutBound 8 := { lost := (rows 128 192 0 0 0 0 0 0), upper := (rows 97 38 207 203 219 32 64 128), lower := (rows 97 38 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 6 4 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) },{ target := 7, region := (rows 255 6 4 8 16 255 255 0), good := (rows 97 103 103 105 113 97 97 97) }] }

theorem profile14_node49 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,36] 6 203 profile14_node49_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,36] 6 203 profile14_node49_cert).mp (by decide +kernel))

def profile14_node51_cert : CutBound 8 := { lost := (rows 0 0 0 96 96 0 0 0), upper := (rows 97 98 7 140 156 32 64 128), lower := (rows 97 98 7 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 255 255), good := (rows 193 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 12 20 255 0 255), good := (rows 161 162 191 168 176 160 160 160) }] }

theorem profile14_node51 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,3] 6 140 profile14_node51_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,3] 6 140 profile14_node51_cert).mp (by decide +kernel))

def profile14_node52_cert : CutBound 8 := { lost := (rows 128 128 128 0 0 0 0 0), upper := (rows 97 98 13 142 150 32 64 128), lower := (rows 97 98 13 8 16 32 64 128), losses := [{ target := 7, region := (rows 255 255 12 8 16 255 255 0), good := (rows 99 99 111 111 115 99 99 99) }] }

theorem profile14_node52 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,9] 6 134 profile14_node52_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,9] 6 134 profile14_node52_cert).mp (by decide +kernel))

def profile14_node53_cert : CutBound 8 := { lost := (rows 128 128 128 0 0 0 0 0), upper := (rows 97 98 14 141 149 32 64 128), lower := (rows 97 98 14 8 16 32 64 128), losses := [{ target := 7, region := (rows 255 255 12 8 16 255 255 0), good := (rows 99 99 111 111 115 99 99 99) }] }

theorem profile14_node53 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,10] 6 133 profile14_node53_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,10] 6 133 profile14_node53_cert).mp (by decide +kernel))

def profile14_node54_cert : CutBound 8 := { lost := (rows 128 128 96 0 0 0 0 0), upper := (rows 97 98 133 142 158 32 64 128), lower := (rows 97 98 133 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 255 0 255), good := (rows 165 162 165 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile14_node54 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,129] 6 142 profile14_node54_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,129] 6 142 profile14_node54_cert).mp (by decide +kernel))

def profile14_node55_cert : CutBound 8 := { lost := (rows 128 128 96 0 0 0 0 0), upper := (rows 97 98 134 141 157 32 64 128), lower := (rows 97 98 134 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 2 6 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile14_node55 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,130] 6 141 profile14_node55_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,130] 6 141 profile14_node55_cert).mp (by decide +kernel))

def profile14_node56_cert : CutBound 8 := { lost := (rows 128 128 96 0 0 0 0 0), upper := (rows 97 98 140 143 151 32 64 128), lower := (rows 97 98 140 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 255 255), good := (rows 193 194 204 204 208 192 192 192) },{ target := 6, region := (rows 1 2 12 8 16 255 0 255), good := (rows 161 162 172 172 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 111 107 115 99 99 99) }] }

theorem profile14_node56 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,136] 6 135 profile14_node56_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96,136] 6 135 profile14_node56_cert).mp (by decide +kernel))

def profile14_node50_column : Nat → Fin 8 := fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 4 | 40 => 5 | 72 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile14_node50_route : Route 8 := (fun mask => (mask,id))

theorem profile14_node50 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,96] 6 (by decide) (choices 2) [3,9,10,129,130,136] profile14_node50_route profile14_node50_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node51
  · exact profile14_node52
  · exact profile14_node53
  · exact profile14_node54
  · exact profile14_node55
  · exact profile14_node56

def profile14_node57_cert : CutBound 8 := { lost := (rows 128 96 0 0 0 0 0 0), upper := (rows 97 131 238 238 254 32 64 128), lower := (rows 97 131 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 101 105 113 97 97 97) }] }

theorem profile14_node57 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,129] 6 238 profile14_node57_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,129] 6 238 profile14_node57_cert).mp (by decide +kernel))

def profile14_node58_cert : CutBound 8 := { lost := (rows 128 96 0 0 0 0 0 0), upper := (rows 97 134 239 235 251 32 64 128), lower := (rows 97 134 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 6 4 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 103 101 105 113 97 97 97) }] }

theorem profile14_node58 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,132] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,132] 6 235 profile14_node58_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,132] 6 235 profile14_node58_cert).mp (by decide +kernel))

def profile14_node60_cert : CutBound 8 := { lost := (rows 0 64 64 32 32 0 0 0), upper := (rows 97 162 7 204 220 32 64 128), lower := (rows 97 162 7 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 4 12 20 0 255 255), good := (rows 193 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) }] }

theorem profile14_node60 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,3] 6 204 profile14_node60_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,3] 6 204 profile14_node60_cert).mp (by decide +kernel))

def profile14_node61_cert : CutBound 8 := { lost := (rows 128 64 128 0 0 0 0 0), upper := (rows 97 162 13 206 214 32 64 128), lower := (rows 97 162 13 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 163 162 175 170 178 162 162 162) },{ target := 7, region := (rows 255 2 12 8 16 255 255 0), good := (rows 97 99 109 109 113 97 97 97) }] }

theorem profile14_node61 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,9] 6 198 profile14_node61_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,9] 6 198 profile14_node61_cert).mp (by decide +kernel))

def profile14_node62_cert : CutBound 8 := { lost := (rows 128 64 64 0 0 0 0 0), upper := (rows 97 162 14 205 213 32 64 128), lower := (rows 97 162 14 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 255 12 8 16 255 0 255), good := (rows 163 162 174 174 178 162 162 162) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 111 105 113 97 97 97) }] }

theorem profile14_node62 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,10] 6 197 profile14_node62_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,10] 6 197 profile14_node62_cert).mp (by decide +kernel))

def profile14_node63_cert : CutBound 8 := { lost := (rows 0 64 32 64 64 0 0 0), upper := (rows 97 162 69 142 158 32 64 128), lower := (rows 97 162 69 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 4 12 20 255 0 255), good := (rows 163 162 191 170 178 162 162 162) }] }

theorem profile14_node63 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,65] 6 142 profile14_node63_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,65] 6 142 profile14_node63_cert).mp (by decide +kernel))

def profile14_node64_cert : CutBound 8 := { lost := (rows 128 64 160 0 0 0 0 0), upper := (rows 97 162 70 141 157 32 64 128), lower := (rows 97 162 70 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 163 162 166 170 178 162 162 162) },{ target := 7, region := (rows 255 2 6 8 16 255 255 0), good := (rows 97 103 103 105 113 97 97 97) }] }

theorem profile14_node64 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,66] 6 141 profile14_node64_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,66] 6 141 profile14_node64_cert).mp (by decide +kernel))

def profile14_node65_cert : CutBound 8 := { lost := (rows 128 64 160 0 0 0 0 0), upper := (rows 97 162 76 143 151 32 64 128), lower := (rows 97 162 76 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 255 255), good := (rows 193 194 204 204 208 192 192 192) },{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 163 162 174 170 178 162 162 162) },{ target := 7, region := (rows 255 2 12 8 16 255 255 0), good := (rows 97 99 109 109 113 97 97 97) }] }

theorem profile14_node65 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,72] 6 135 profile14_node65_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,72] 6 135 profile14_node65_cert).mp (by decide +kernel))

def profile14_node66_cert : CutBound 8 := { lost := (rows 0 64 96 0 0 0 0 0), upper := (rows 97 162 133 78 94 32 64 128), lower := (rows 97 162 133 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) }] }

theorem profile14_node66 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,129] 6 78 profile14_node66_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,129] 6 78 profile14_node66_cert).mp (by decide +kernel))

def profile14_node67_cert : CutBound 8 := { lost := (rows 0 64 96 0 0 0 0 0), upper := (rows 97 162 134 77 93 32 64 128), lower := (rows 97 162 134 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 255 255 8 16 255 0 255), good := (rows 167 166 166 174 182 166 166 166) }] }

theorem profile14_node67 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,130] 6 77 profile14_node67_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,130] 6 77 profile14_node67_cert).mp (by decide +kernel))

def profile14_node68_cert : CutBound 8 := { lost := (rows 0 64 96 0 0 0 0 0), upper := (rows 97 162 140 79 87 32 64 128), lower := (rows 97 162 140 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 255 255), good := (rows 193 194 204 204 208 192 192 192) },{ target := 6, region := (rows 1 255 12 8 16 255 0 255), good := (rows 163 162 174 174 178 162 162 162) }] }

theorem profile14_node68 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,136] 6 71 profile14_node68_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,136] 6 71 profile14_node68_cert).mp (by decide +kernel))

def profile14_node69_cert : CutBound 8 := { lost := (rows 128 64 32 0 0 0 0 0), upper := (rows 97 162 196 15 31 32 64 128), lower := (rows 97 162 196 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 197 198 196 204 212 196 196 196) },{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 163 162 166 170 178 162 162 162) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 101 105 113 97 97 97) }] }

theorem profile14_node69 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,192] 6 15 profile14_node69_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160,192] 6 15 profile14_node69_cert).mp (by decide +kernel))

def profile14_node59_column : Nat → Fin 8 := fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile14_node59_route : Route 8 := (fun mask => (mask,id))

theorem profile14_node59 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96,160] 6 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] profile14_node59_route profile14_node59_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node60
  · exact profile14_node61
  · exact profile14_node62
  · exact profile14_node63
  · exact profile14_node64
  · exact profile14_node65
  · exact profile14_node66
  · exact profile14_node67
  · exact profile14_node68
  · exact profile14_node69

def profile14_node31_column : Nat → Fin 8 := fun mask => match mask with | 17 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node31_route : Route 8 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node31 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [96] 6 (by decide) (choices 2) [5,12,33,36,96,129,132,160] profile14_node31_route profile14_node31_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile14_node32
  · exact profile14_node40
  · exact profile14_node48
  · exact profile14_node49
  · exact profile14_node50
  · exact profile14_node57
  · exact profile14_node58
  · exact profile14_node59

def profile14_node0_column : Nat → Fin 8 := fun mask => match mask with | 18 => 4 | 20 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile14_node0_route : Route 8 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 132 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 40 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 72 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile14_node0 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [] 6 (by decide) (choices 2) [6,34,96] profile14_node0_route profile14_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile14_node1
  · exact profile14_node18
  · exact profile14_node31

theorem profile14 : Upper (D (n:=8) [33,33,33,33,32,2,2,2]) (R (n:=8) [33,33,33,33,32,2,2,2]) [] 6 := profile14_node0


#print axioms profile14
end Delivery.SmallBudgetTenFinite8
