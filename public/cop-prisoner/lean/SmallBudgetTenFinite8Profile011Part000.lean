import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile11_node2_cert : CutBound 8 := { lost := (rows 64 64 32 32 32 0 0 0), upper := (rows 35 35 197 201 209 32 64 128), lower := (rows 35 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 223 223 196 200 208 192 192 192) },{ target := 6, region := (rows 255 255 4 8 16 255 0 255), good := (rows 163 163 167 171 179 163 163 163) }] }

theorem profile11_node2 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,33] 6 193 profile11_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,33] 6 193 profile11_node2_cert).mp (by decide +kernel))

def profile11_node3_cert : CutBound 8 := { lost := (rows 192 160 0 0 0 0 0 0), upper := (rows 35 67 229 233 241 32 64 128), lower := (rows 35 67 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile11_node3 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,65] 6 225 profile11_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,65] 6 225 profile11_node3_cert).mp (by decide +kernel))

def profile11_node4_cert : CutBound 8 := { lost := (rows 0 1 32 32 32 0 0 0), upper := (rows 35 98 197 201 209 32 64 128), lower := (rows 35 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile11_node4 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,96] 6 193 profile11_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,96] 6 193 profile11_node4_cert).mp (by decide +kernel))

def profile11_node5_cert : CutBound 8 := { lost := (rows 192 33 0 0 0 0 0 0), upper := (rows 35 194 229 233 241 32 64 128), lower := (rows 35 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 255 4 8 16 0 255 255), good := (rows 195 194 198 202 210 194 194 194) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 3 2 4 8 16 255 255 0), good := (rows 99 99 100 104 112 96 96 96) }] }

theorem profile11_node5 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,192] 6 225 profile11_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34,192] 6 225 profile11_node5_cert).mp (by decide +kernel))

def profile11_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile11_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile11_node1 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [34] 6 (by decide) (choices 2) [33,65,96,192] profile11_node1_route profile11_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node2
  · exact profile11_node3
  · exact profile11_node4
  · exact profile11_node5

def profile11_node7_cert : CutBound 8 := { lost := (rows 0 64 32 32 32 0 0 0), upper := (rows 97 35 199 203 211 32 64 128), lower := (rows 97 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) }] }

theorem profile11_node7 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,33] 6 195 profile11_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,33] 6 195 profile11_node7_cert).mp (by decide +kernel))

def profile11_node9_cert : CutBound 8 := { lost := (rows 0 1 0 96 96 0 0 0), upper := (rows 97 98 7 137 145 32 64 128), lower := (rows 97 98 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 4 13 21 0 255 255), good := (rows 217 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 13 21 255 0 255), good := (rows 185 162 191 168 176 160 160 160) }] }

theorem profile11_node9 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,3] 6 129 profile11_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,3] 6 129 profile11_node9_cert).mp (by decide +kernel))

def profile11_node10_cert : CutBound 8 := { lost := (rows 128 129 96 0 0 0 0 0), upper := (rows 97 98 133 139 147 32 64 128), lower := (rows 97 98 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 255 0 255), good := (rows 165 162 165 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile11_node10 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,129] 6 131 profile11_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,129] 6 131 profile11_node10_cert).mp (by decide +kernel))

def profile11_node11_cert : CutBound 8 := { lost := (rows 0 1 33 32 32 0 0 0), upper := (rows 97 98 134 137 145 32 64 128), lower := (rows 97 98 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 9 17 0 255 255), good := (rows 217 198 198 200 208 192 192 192) }] }

theorem profile11_node11 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,130] 6 129 profile11_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96,130] 6 129 profile11_node11_cert).mp (by decide +kernel))

def profile11_node8_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 3 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile11_node8_route : Route 8 := (fun mask => (mask,id))

theorem profile11_node8 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,96] 6 (by decide) (choices 2) [3,129,130] profile11_node8_route profile11_node8_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile11_node9
  · exact profile11_node10
  · exact profile11_node11

def profile11_node13_cert : CutBound 8 := { lost := (rows 0 96 96 0 0 0 0 0), upper := (rows 97 131 7 233 241 32 64 128), lower := (rows 97 131 7 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile11_node13 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,3] 6 225 profile11_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,3] 6 225 profile11_node13_cert).mp (by decide +kernel))

def profile11_node14_cert : CutBound 8 := { lost := (rows 0 96 64 32 32 0 0 0), upper := (rows 97 131 37 203 211 32 64 128), lower := (rows 97 131 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 7 4 15 23 0 255 255), good := (rows 219 219 223 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile11_node14 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,33] 6 195 profile11_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,33] 6 195 profile11_node14_cert).mp (by decide +kernel))

def profile11_node15_cert : CutBound 8 := { lost := (rows 0 32 1 32 32 0 0 0), upper := (rows 97 131 38 201 209 32 64 128), lower := (rows 97 131 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 222 200 208 192 192 192) }] }

theorem profile11_node15 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,34] 6 193 profile11_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,34] 6 193 profile11_node15_cert).mp (by decide +kernel))

def profile11_node16_cert : CutBound 8 := { lost := (rows 0 32 1 32 32 0 0 0), upper := (rows 97 131 100 139 147 32 64 128), lower := (rows 97 131 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) }] }

theorem profile11_node16 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,96] 6 131 profile11_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,96] 6 131 profile11_node16_cert).mp (by decide +kernel))

def profile11_node17_cert : CutBound 8 := { lost := (rows 0 96 96 0 0 0 0 0), upper := (rows 97 131 133 107 115 32 64 128), lower := (rows 97 131 133 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile11_node17 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,129] 6 99 profile11_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,129] 6 99 profile11_node17_cert).mp (by decide +kernel))

def profile11_node18_cert : CutBound 8 := { lost := (rows 0 96 97 0 0 0 0 0), upper := (rows 97 131 134 105 113 32 64 128), lower := (rows 97 131 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 199 199 198 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) }] }

theorem profile11_node18 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,130] 6 97 profile11_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,130] 6 97 profile11_node18_cert).mp (by decide +kernel))

def profile11_node19_cert : CutBound 8 := { lost := (rows 0 32 1 32 32 0 0 0), upper := (rows 97 131 164 75 83 32 64 128), lower := (rows 97 131 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) }] }

theorem profile11_node19 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,160] 6 67 profile11_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129,160] 6 67 profile11_node19_cert).mp (by decide +kernel))

def profile11_node12_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile11_node12_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node12 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,129] 6 (by decide) (choices 2) [3,33,34,96,129,130,160] profile11_node12_route profile11_node12_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node13
  · exact profile11_node14
  · exact profile11_node15
  · exact profile11_node16
  · exact profile11_node17
  · exact profile11_node18
  · exact profile11_node19

def profile11_node21_cert : CutBound 8 := { lost := (rows 0 65 64 32 32 0 0 0), upper := (rows 97 162 7 201 209 32 64 128), lower := (rows 97 162 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 4 13 21 0 255 255), good := (rows 217 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) }] }

theorem profile11_node21 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,3] 6 193 profile11_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,3] 6 193 profile11_node21_cert).mp (by decide +kernel))

def profile11_node22_cert : CutBound 8 := { lost := (rows 0 65 32 64 64 0 0 0), upper := (rows 97 162 69 139 147 32 64 128), lower := (rows 97 162 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 4 13 21 255 0 255), good := (rows 187 162 191 170 178 162 162 162) }] }

theorem profile11_node22 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,65] 6 131 profile11_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,65] 6 131 profile11_node22_cert).mp (by decide +kernel))

def profile11_node23_cert : CutBound 8 := { lost := (rows 0 1 33 32 32 0 0 0), upper := (rows 97 162 70 137 145 32 64 128), lower := (rows 97 162 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 9 17 0 255 255), good := (rows 217 198 198 200 208 192 192 192) }] }

theorem profile11_node23 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,66] 6 129 profile11_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,66] 6 129 profile11_node23_cert).mp (by decide +kernel))

def profile11_node24_cert : CutBound 8 := { lost := (rows 0 65 96 0 0 0 0 0), upper := (rows 97 162 133 75 83 32 64 128), lower := (rows 97 162 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) }] }

theorem profile11_node24 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,129] 6 67 profile11_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,129] 6 67 profile11_node24_cert).mp (by decide +kernel))

def profile11_node25_cert : CutBound 8 := { lost := (rows 0 1 33 32 32 0 0 0), upper := (rows 97 162 134 73 81 32 64 128), lower := (rows 97 162 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 6 9 17 0 255 255), good := (rows 217 198 198 200 208 192 192 192) }] }

theorem profile11_node25 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,130] 6 65 profile11_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,130] 6 65 profile11_node25_cert).mp (by decide +kernel))

def profile11_node26_cert : CutBound 8 := { lost := (rows 0 65 33 64 64 0 0 0), upper := (rows 97 162 196 11 19 32 64 128), lower := (rows 97 162 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 197 198 196 204 212 196 196 196) },{ target := 6, region := (rows 1 255 4 9 17 255 0 255), good := (rows 187 162 166 170 178 162 162 162) }] }

theorem profile11_node26 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,192] 6 3 profile11_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160,192] 6 3 profile11_node26_cert).mp (by decide +kernel))

def profile11_node20_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile11_node20_route : Route 8 := (fun mask => (mask,id))

theorem profile11_node20 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96,160] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile11_node20_route profile11_node20_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile11_node21
  · exact profile11_node22
  · exact profile11_node23
  · exact profile11_node24
  · exact profile11_node25
  · exact profile11_node26

def profile11_node6_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile11_node6_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node6 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [96] 6 (by decide) (choices 2) [33,96,129,160] profile11_node6_route profile11_node6_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile11_node7
  · exact profile11_node8
  · exact profile11_node12
  · exact profile11_node20

def profile11_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 2 | 10 => 3 | 18 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile11_node0_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile11_node0 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [] 6 (by decide) (choices 2) [34,96] profile11_node0_route profile11_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile11_node1
  · exact profile11_node6

theorem profile11 : Upper (D (n:=8) [35,33,32,32,32,2,2,2]) (R (n:=8) [35,33,32,32,32,2,2,2]) [] 6 := profile11_node0


#print axioms profile11
end Delivery.SmallBudgetTenFinite8
