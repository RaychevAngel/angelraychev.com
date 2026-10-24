import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile4_node2_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 51 35 197 201 209 32 64 128), lower := (rows 51 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 223 223 196 200 208 192 192 192) }] }

theorem profile4_node2 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,33] 6 193 profile4_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,33] 6 193 profile4_node2_cert).mp (by decide +kernel))

def profile4_node3_cert : CutBound 8 := { lost := (rows 128 160 0 0 0 0 0 0), upper := (rows 51 67 229 233 241 32 64 128), lower := (rows 51 67 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) },{ target := 7, region := (rows 17 19 4 8 16 255 255 0), good := (rows 115 99 100 104 115 96 96 96) }] }

theorem profile4_node3 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,65] 6 225 profile4_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,65] 6 225 profile4_node3_cert).mp (by decide +kernel))

def profile4_node4_cert : CutBound 8 := { lost := (rows 0 1 32 32 0 0 0 0), upper := (rows 51 98 197 201 209 32 64 128), lower := (rows 51 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 242 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile4_node4 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,96] 6 193 profile4_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,96] 6 193 profile4_node4_cert).mp (by decide +kernel))

def profile4_node5_cert : CutBound 8 := { lost := (rows 0 33 0 0 0 0 0 0), upper := (rows 51 194 229 233 241 32 64 128), lower := (rows 51 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 242 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 211 194 198 202 210 194 194 194) }] }

theorem profile4_node5 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,192] 6 225 profile4_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50,192] 6 225 profile4_node5_cert).mp (by decide +kernel))

def profile4_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile4_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node1 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [50] 6 (by decide) (choices 2) [33,65,96,192] profile4_node1_route profile4_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node2
  · exact profile4_node3
  · exact profile4_node4
  · exact profile4_node5

def profile4_node7_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 99 19 229 233 241 32 64 128), lower := (rows 99 19 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 19 18 4 8 16 255 255 0), good := (rows 99 115 100 104 115 96 96 96) }] }

theorem profile4_node7 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,17] 6 225 profile4_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,17] 6 225 profile4_node7_cert).mp (by decide +kernel))

def profile4_node8_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 99 35 213 217 209 32 64 128), lower := (rows 99 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 223 223 196 200 208 192 192 192) }] }

theorem profile4_node8 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,33] 6 209 profile4_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,33] 6 209 profile4_node8_cert).mp (by decide +kernel))

def profile4_node9_cert : CutBound 8 := { lost := (rows 0 1 32 32 0 0 0 0), upper := (rows 99 50 197 201 209 32 64 128), lower := (rows 99 50 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 255 255 255), good := (rows 226 242 228 232 242 224 224 224) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 210 196 200 208 192 192 192) }] }

theorem profile4_node9 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,48] 6 193 profile4_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,48] 6 193 profile4_node9_cert).mp (by decide +kernel))

def profile4_node10_cert : CutBound 8 := { lost := (rows 0 1 32 32 0 0 0 0), upper := (rows 99 98 149 153 145 32 64 128), lower := (rows 99 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile4_node10 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,96] 6 145 profile4_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,96] 6 145 profile4_node10_cert).mp (by decide +kernel))

def profile4_node11_cert : CutBound 8 := { lost := (rows 0 96 0 0 0 0 0 0), upper := (rows 99 131 245 249 241 32 64 128), lower := (rows 99 131 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) }] }

theorem profile4_node11 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,129] 6 241 profile4_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,129] 6 241 profile4_node11_cert).mp (by decide +kernel))

def profile4_node12_cert : CutBound 8 := { lost := (rows 0 33 0 0 0 0 0 0), upper := (rows 99 146 229 233 241 32 64 128), lower := (rows 99 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 255 255 255), good := (rows 226 242 228 232 242 224 224 224) },{ target := 5, region := (rows 1 18 4 8 16 0 255 255), good := (rows 195 210 196 200 210 192 192 192) }] }

theorem profile4_node12 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,144] 6 225 profile4_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,144] 6 225 profile4_node12_cert).mp (by decide +kernel))

def profile4_node13_cert : CutBound 8 := { lost := (rows 0 1 32 32 0 0 0 0), upper := (rows 99 162 213 217 209 32 64 128), lower := (rows 99 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile4_node13 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,160] 6 209 profile4_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98,160] 6 209 profile4_node13_cert).mp (by decide +kernel))

def profile4_node6_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile4_node6_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile4_node6 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [98] 6 (by decide) (choices 2) [17,33,48,96,129,144,160] profile4_node6_route profile4_node6_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node7
  · exact profile4_node8
  · exact profile4_node9
  · exact profile4_node10
  · exact profile4_node11
  · exact profile4_node12
  · exact profile4_node13

def profile4_node15_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 113 35 199 203 211 32 64 128), lower := (rows 113 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 209 223 196 200 208 192 192 192) }] }

theorem profile4_node15 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,33] 6 195 profile4_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,33] 6 195 profile4_node15_cert).mp (by decide +kernel))

def profile4_node16_cert : CutBound 8 := { lost := (rows 128 129 0 0 0 0 0 0), upper := (rows 113 98 135 139 147 32 64 128), lower := (rows 113 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 242 226 230 234 242 226 226 226) },{ target := 7, region := (rows 17 255 4 8 16 255 255 0), good := (rows 115 98 102 106 115 98 98 98) }] }

theorem profile4_node16 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,96] 6 131 profile4_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,96] 6 131 profile4_node16_cert).mp (by decide +kernel))

def profile4_node17_cert : CutBound 8 := { lost := (rows 0 96 0 0 0 0 0 0), upper := (rows 113 131 231 235 243 32 64 128), lower := (rows 113 131 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 179 163 164 168 176 160 160 160) }] }

theorem profile4_node17 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,129] 6 227 profile4_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,129] 6 227 profile4_node17_cert).mp (by decide +kernel))

def profile4_node18_cert : CutBound 8 := { lost := (rows 0 65 0 0 0 0 0 0), upper := (rows 113 162 199 203 211 32 64 128), lower := (rows 113 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 242 226 230 234 242 226 226 226) },{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 179 162 166 170 178 162 162 162) }] }

theorem profile4_node18 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,160] 6 195 profile4_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112,160] 6 195 profile4_node18_cert).mp (by decide +kernel))

def profile4_node14_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile4_node14_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile4_node14 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [112] 6 (by decide) (choices 2) [33,96,129,160] profile4_node14_route profile4_node14_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node15
  · exact profile4_node16
  · exact profile4_node17
  · exact profile4_node18

def profile4_node21_cert : CutBound 8 := { lost := (rows 0 0 32 1 0 0 0 0), upper := (rows 225 19 7 232 240 32 64 128), lower := (rows 225 19 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 248 250 254 248 248 248 248 248) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 215 199 200 208 192 192 192) }] }

theorem profile4_node21 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,3] 6 224 profile4_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,3] 6 224 profile4_node21_cert).mp (by decide +kernel))

def profile4_node22_cert : CutBound 8 := { lost := (rows 0 32 0 33 0 0 0 0), upper := (rows 225 19 37 202 210 32 64 128), lower := (rows 225 19 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 255 255 255), good := (rows 224 250 228 232 240 224 224 224) },{ target := 5, region := (rows 1 7 4 15 23 0 255 255), good := (rows 219 219 223 200 208 192 192 192) }] }

theorem profile4_node22 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,33] 6 194 profile4_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,33] 6 194 profile4_node22_cert).mp (by decide +kernel))

def profile4_node23_cert : CutBound 8 := { lost := (rows 0 32 1 32 0 0 0 0), upper := (rows 225 19 38 201 209 32 64 128), lower := (rows 225 19 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 246 230 232 240 224 224 224) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 222 200 208 192 192 192) }] }

theorem profile4_node23 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,34] 6 193 profile4_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,34] 6 193 profile4_node23_cert).mp (by decide +kernel))

def profile4_node24_cert : CutBound 8 := { lost := (rows 0 32 1 32 0 0 0 0), upper := (rows 225 19 100 139 147 32 64 128), lower := (rows 225 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 246 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) }] }

theorem profile4_node24 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,96] 6 131 profile4_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17,96] 6 131 profile4_node24_cert).mp (by decide +kernel))

def profile4_node20_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile4_node20_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile4_node20 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,17] 6 (by decide) (choices 2) [3,33,34,96] profile4_node20_route profile4_node20_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node21
  · exact profile4_node22
  · exact profile4_node23
  · exact profile4_node24

def profile4_node25_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 225 35 215 219 211 32 64 128), lower := (rows 225 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) }] }

theorem profile4_node25 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,33] 6 211 profile4_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,33] 6 211 profile4_node25_cert).mp (by decide +kernel))

def profile4_node26_cert : CutBound 8 := { lost := (rows 0 65 0 0 0 0 0 0), upper := (rows 225 50 199 203 211 32 64 128), lower := (rows 225 50 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 255 255 255), good := (rows 224 242 228 232 242 224 224 224) },{ target := 6, region := (rows 1 18 4 8 16 255 0 255), good := (rows 161 178 164 168 178 160 160 160) }] }

theorem profile4_node26 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,48] 6 195 profile4_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,48] 6 195 profile4_node26_cert).mp (by decide +kernel))

def profile4_node27_cert : CutBound 8 := { lost := (rows 0 129 0 0 0 0 0 0), upper := (rows 225 98 151 155 147 32 64 128), lower := (rows 225 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 7, region := (rows 1 255 4 8 16 255 255 0), good := (rows 99 98 102 106 114 98 98 98) }] }

theorem profile4_node27 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,96] 6 147 profile4_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224,96] 6 147 profile4_node27_cert).mp (by decide +kernel))

def profile4_node19_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile4_node19_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile4_node19 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [224] 6 (by decide) (choices 2) [17,33,48,96] profile4_node19_route profile4_node19_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node20
  · exact profile4_node25
  · exact profile4_node26
  · exact profile4_node27

def profile4_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 134 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 138 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile4_node0_route : Route 8 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 162 => (98,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 194 => (98,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile4_node0 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [] 6 (by decide) (choices 3) [50,98,112,224] profile4_node0_route profile4_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node1
  · exact profile4_node6
  · exact profile4_node14
  · exact profile4_node19

theorem profile4 : Upper (D (n:=8) [50,33,32,32,17,2,2,2]) (R (n:=8) [50,33,32,32,17,2,2,2]) [] 6 := profile4_node0


#print axioms profile4
end Delivery.SmallBudgetTenFinite8
