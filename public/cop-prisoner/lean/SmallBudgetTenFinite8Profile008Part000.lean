import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile8_node2_cert : CutBound 8 := { lost := (rows 0 32 16 16 0 0 0 0), upper := (rows 51 19 228 232 240 32 64 128), lower := (rows 51 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 239 239 236 236 236 236 236 236) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) }] }

theorem profile8_node2 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,17] 6 224 profile8_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,17] 6 224 profile8_node2_cert).mp (by decide +kernel))

def profile8_node3_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 51 35 212 216 208 32 64 128), lower := (rows 51 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 223 223 220 220 220 220 220 220) }] }

theorem profile8_node3 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,33] 6 208 profile8_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,33] 6 208 profile8_node3_cert).mp (by decide +kernel))

def profile8_node4_cert : CutBound 8 := { lost := (rows 0 0 48 48 0 0 0 0), upper := (rows 51 50 197 201 209 32 64 128), lower := (rows 51 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 255 255 255), good := (rows 239 226 228 232 224 224 224 224) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 210 196 200 208 192 192 192) }] }

theorem profile8_node4 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,48] 6 193 profile8_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,48] 6 193 profile8_node4_cert).mp (by decide +kernel))

def profile8_node5_cert : CutBound 8 := { lost := (rows 128 176 0 0 0 0 0 0), upper := (rows 51 67 244 248 240 32 64 128), lower := (rows 51 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) },{ target := 7, region := (rows 17 19 4 8 16 255 255 0), good := (rows 115 99 100 104 115 96 96 96) }] }

theorem profile8_node5 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,65] 6 240 profile8_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,65] 6 240 profile8_node5_cert).mp (by decide +kernel))

def profile8_node6_cert : CutBound 8 := { lost := (rows 0 32 16 16 0 0 0 0), upper := (rows 51 82 229 233 241 32 64 128), lower := (rows 51 82 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 255 255 255), good := (rows 239 226 228 232 224 224 224 224) },{ target := 5, region := (rows 1 19 4 8 16 0 255 255), good := (rows 211 210 196 200 210 192 192 192) }] }

theorem profile8_node6 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,80] 6 225 profile8_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,80] 6 225 profile8_node6_cert).mp (by decide +kernel))

def profile8_node7_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 51 98 213 217 209 32 64 128), lower := (rows 51 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 234 226 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile8_node7 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,96] 6 209 profile8_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,96] 6 209 profile8_node7_cert).mp (by decide +kernel))

def profile8_node9_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 51 194 21 232 240 32 64 128), lower := (rows 51 194 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 239 234 234 234 234 234) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 215 202 210 194 194 194) }] }

theorem profile8_node9 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,17] 6 224 profile8_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,17] 6 224 profile8_node9_cert).mp (by decide +kernel))

def profile8_node10_cert : CutBound 8 := { lost := (rows 0 48 16 32 0 0 0 0), upper := (rows 51 194 37 216 208 32 64 128), lower := (rows 51 194 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 255 255 255), good := (rows 231 226 231 234 226 226 226 226) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 223 218 218 218 218 218) }] }

theorem profile8_node10 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,33] 6 208 profile8_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,33] 6 208 profile8_node10_cert).mp (by decide +kernel))

def profile8_node11_cert : CutBound 8 := { lost := (rows 0 48 0 48 0 0 0 0), upper := (rows 51 194 52 201 209 32 64 128), lower := (rows 51 194 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 255 255 255), good := (rows 235 226 230 234 226 226 226 226) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 214 202 210 194 194 194) }] }

theorem profile8_node11 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,48] 6 193 profile8_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,48] 6 193 profile8_node11_cert).mp (by decide +kernel))

def profile8_node12_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 51 194 69 184 176 32 64 128), lower := (rows 51 194 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 5 8 0 255 255 255), good := (rows 231 226 231 234 226 226 226 226) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 215 194 199 202 210 194 194 194) }] }

theorem profile8_node12 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,65] 6 176 profile8_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,65] 6 176 profile8_node12_cert).mp (by decide +kernel))

def profile8_node13_cert : CutBound 8 := { lost := (rows 0 48 32 16 0 0 0 0), upper := (rows 51 194 84 169 177 32 64 128), lower := (rows 51 194 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 9 0 255 255 255), good := (rows 235 226 230 234 226 226 226 226) },{ target := 5, region := (rows 1 255 21 8 16 0 255 255), good := (rows 215 194 214 202 214 194 194 194) }] }

theorem profile8_node13 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,80] 6 161 profile8_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,80] 6 161 profile8_node13_cert).mp (by decide +kernel))

def profile8_node14_cert : CutBound 8 := { lost := (rows 0 48 16 32 0 0 0 0), upper := (rows 51 194 100 153 145 32 64 128), lower := (rows 51 194 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 255 255 255), good := (rows 231 230 230 238 230 230 230 230) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 198 202 210 194 194 194) }] }

theorem profile8_node14 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,96] 6 145 profile8_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,96] 6 145 profile8_node14_cert).mp (by decide +kernel))

def profile8_node15_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 51 194 196 57 49 32 64 128), lower := (rows 51 194 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 255 8 0 255 255 255), good := (rows 231 230 230 238 230 230 230 230) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 215 198 198 206 214 198 198 198) }] }

theorem profile8_node15 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,192] 6 49 profile8_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192,192] 6 49 profile8_node15_cert).mp (by decide +kernel))

def profile8_node8_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile8_node8_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile8_node8 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50,192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile8_node8_route profile8_node8_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node9
  · exact profile8_node10
  · exact profile8_node11
  · exact profile8_node12
  · exact profile8_node13
  · exact profile8_node14
  · exact profile8_node15

def profile8_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile8_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile8_node1 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [50] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile8_node1_route profile8_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node2
  · exact profile8_node3
  · exact profile8_node4
  · exact profile8_node5
  · exact profile8_node6
  · exact profile8_node7
  · exact profile8_node8

def profile8_node17_cert : CutBound 8 := { lost := (rows 144 128 0 0 0 0 0 0), upper := (rows 99 19 244 248 240 32 64 128), lower := (rows 99 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 7, region := (rows 19 18 4 8 16 255 255 0), good := (rows 99 115 100 104 115 96 96 96) }] }

theorem profile8_node17 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,17] 6 240 profile8_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,17] 6 240 profile8_node17_cert).mp (by decide +kernel))

def profile8_node18_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 99 35 212 216 208 32 64 128), lower := (rows 99 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 223 223 220 220 220 220 220 220) }] }

theorem profile8_node18 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,33] 6 208 profile8_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,33] 6 208 profile8_node18_cert).mp (by decide +kernel))

def profile8_node19_cert : CutBound 8 := { lost := (rows 16 0 32 32 0 0 0 0), upper := (rows 99 50 213 217 209 32 64 128), lower := (rows 99 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 210 196 200 208 192 192 192) }] }

theorem profile8_node19 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,48] 6 209 profile8_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,48] 6 209 profile8_node19_cert).mp (by decide +kernel))

def profile8_node20_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 99 98 149 153 145 32 64 128), lower := (rows 99 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile8_node20 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,96] 6 145 profile8_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,96] 6 145 profile8_node20_cert).mp (by decide +kernel))

def profile8_node21_cert : CutBound 8 := { lost := (rows 16 48 0 0 0 0 0 0), upper := (rows 99 131 244 248 240 32 64 128), lower := (rows 99 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) }] }

theorem profile8_node21 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,129] 6 240 profile8_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,129] 6 240 profile8_node21_cert).mp (by decide +kernel))

def profile8_node22_cert : CutBound 8 := { lost := (rows 16 96 0 0 0 0 0 0), upper := (rows 99 146 245 249 241 32 64 128), lower := (rows 99 146 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 3 2 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 18 4 8 16 0 255 255), good := (rows 195 210 196 200 210 192 192 192) },{ target := 6, region := (rows 1 18 4 8 16 255 0 255), good := (rows 163 178 164 168 178 160 160 160) }] }

theorem profile8_node22 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,144] 6 241 profile8_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,144] 6 241 profile8_node22_cert).mp (by decide +kernel))

def profile8_node23_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 99 162 213 217 209 32 64 128), lower := (rows 99 162 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) }] }

theorem profile8_node23 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,160] 6 209 profile8_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98,160] 6 209 profile8_node23_cert).mp (by decide +kernel))

def profile8_node16_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile8_node16_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile8_node16 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [98] 6 (by decide) (choices 2) [17,33,48,96,129,144,160] profile8_node16_route profile8_node16_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node17
  · exact profile8_node18
  · exact profile8_node19
  · exact profile8_node20
  · exact profile8_node21
  · exact profile8_node22
  · exact profile8_node23

def profile8_node25_cert : CutBound 8 := { lost := (rows 0 32 16 16 0 0 0 0), upper := (rows 113 19 230 234 242 32 64 128), lower := (rows 113 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 255 255 255), good := (rows 225 239 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 211 196 200 208 192 192 192) }] }

theorem profile8_node25 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,17] 6 226 profile8_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,17] 6 226 profile8_node25_cert).mp (by decide +kernel))

def profile8_node26_cert : CutBound 8 := { lost := (rows 0 16 32 32 0 0 0 0), upper := (rows 113 35 214 218 210 32 64 128), lower := (rows 113 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 209 223 196 200 208 192 192 192) }] }

theorem profile8_node26 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,33] 6 210 profile8_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,33] 6 210 profile8_node26_cert).mp (by decide +kernel))

def profile8_node27_cert : CutBound 8 := { lost := (rows 128 192 0 0 0 0 0 0), upper := (rows 113 50 199 203 211 32 64 128), lower := (rows 113 50 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 19 4 8 16 255 0 255), good := (rows 179 178 164 168 178 160 160 160) },{ target := 7, region := (rows 19 19 4 8 16 255 255 0), good := (rows 115 115 100 104 115 96 96 96) }] }

theorem profile8_node27 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,48] 6 195 profile8_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,48] 6 195 profile8_node27_cert).mp (by decide +kernel))

def profile8_node28_cert : CutBound 8 := { lost := (rows 128 144 0 0 0 0 0 0), upper := (rows 113 98 151 155 147 32 64 128), lower := (rows 113 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 234 226 226 226 226) },{ target := 7, region := (rows 17 255 4 8 16 255 255 0), good := (rows 115 98 102 106 115 98 98 98) }] }

theorem profile8_node28 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,96] 6 147 profile8_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,96] 6 147 profile8_node28_cert).mp (by decide +kernel))

def profile8_node29_cert : CutBound 8 := { lost := (rows 0 112 0 0 0 0 0 0), upper := (rows 113 131 246 250 242 32 64 128), lower := (rows 113 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 255 255 255), good := (rows 227 227 228 232 224 224 224 224) },{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 211 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 179 163 164 168 176 160 160 160) }] }

theorem profile8_node29 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,129] 6 242 profile8_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,129] 6 242 profile8_node29_cert).mp (by decide +kernel))

def profile8_node30_cert : CutBound 8 := { lost := (rows 128 96 0 0 0 0 0 0), upper := (rows 113 146 231 235 243 32 64 128), lower := (rows 113 146 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 19 4 8 16 0 255 255), good := (rows 211 210 196 200 210 192 192 192) },{ target := 6, region := (rows 1 19 4 8 16 255 0 255), good := (rows 179 178 164 168 178 160 160 160) },{ target := 7, region := (rows 19 2 4 8 16 255 255 0), good := (rows 113 115 100 104 113 96 96 96) }] }

theorem profile8_node30 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,144] 6 227 profile8_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,144] 6 227 profile8_node30_cert).mp (by decide +kernel))

def profile8_node31_cert : CutBound 8 := { lost := (rows 128 80 0 0 0 0 0 0), upper := (rows 113 162 215 219 211 32 64 128), lower := (rows 113 162 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 8 0 255 255 255), good := (rows 227 226 230 234 226 226 226 226) },{ target := 6, region := (rows 1 255 4 8 16 255 0 255), good := (rows 179 162 166 170 178 162 162 162) },{ target := 7, region := (rows 17 2 4 8 16 255 255 0), good := (rows 113 98 100 104 113 96 96 96) }] }

theorem profile8_node31 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,160] 6 211 profile8_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112,160] 6 211 profile8_node31_cert).mp (by decide +kernel))

def profile8_node24_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile8_node24_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile8_node24 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [112] 6 (by decide) (choices 2) [17,33,48,96,129,144,160] profile8_node24_route profile8_node24_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node25
  · exact profile8_node26
  · exact profile8_node27
  · exact profile8_node28
  · exact profile8_node29
  · exact profile8_node30
  · exact profile8_node31

def profile8_node34_cert : CutBound 8 := { lost := (rows 16 0 32 16 0 0 0 0), upper := (rows 225 19 22 232 240 32 64 128), lower := (rows 225 19 22 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 239 233 233 233 233 233) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 215 214 200 208 192 192 192) }] }

theorem profile8_node34 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,18] 6 224 profile8_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,18] 6 224 profile8_node34_cert).mp (by decide +kernel))

def profile8_node35_cert : CutBound 8 := { lost := (rows 16 32 16 32 0 0 0 0), upper := (rows 225 19 38 216 208 32 64 128), lower := (rows 225 19 38 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 6 8 0 255 255 255), good := (rows 225 231 231 233 225 225 225 225) },{ target := 5, region := (rows 1 3 4 255 255 0 255 255), good := (rows 219 219 222 216 216 216 216 216) }] }

theorem profile8_node35 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,34] 6 208 profile8_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,34] 6 208 profile8_node35_cert).mp (by decide +kernel))

def profile8_node36_cert : CutBound 8 := { lost := (rows 16 32 0 48 0 0 0 0), upper := (rows 225 19 52 202 210 32 64 128), lower := (rows 225 19 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 10 0 255 255 255), good := (rows 225 235 229 233 225 225 225 225) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 212 200 208 192 192 192) }] }

theorem profile8_node36 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,48] 6 194 profile8_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,48] 6 194 profile8_node36_cert).mp (by decide +kernel))

def profile8_node37_cert : CutBound 8 := { lost := (rows 16 32 16 32 0 0 0 0), upper := (rows 225 19 100 154 146 32 64 128), lower := (rows 225 19 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 255 255 255), good := (rows 229 231 229 237 229 229 229 229) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) }] }

theorem profile8_node37 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,96] 6 146 profile8_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17,96] 6 146 profile8_node37_cert).mp (by decide +kernel))

def profile8_node33_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile8_node33_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile8_node33 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,17] 6 (by decide) (choices 2) [18,34,48,96] profile8_node33_route profile8_node33_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node34
  · exact profile8_node35
  · exact profile8_node36
  · exact profile8_node37

def profile8_node38_cert : CutBound 8 := { lost := (rows 16 16 32 32 0 0 0 0), upper := (rows 225 35 214 218 210 32 64 128), lower := (rows 225 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) }] }

theorem profile8_node38 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,33] 6 210 profile8_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,33] 6 210 profile8_node38_cert).mp (by decide +kernel))

def profile8_node39_cert : CutBound 8 := { lost := (rows 16 192 0 0 0 0 0 0), upper := (rows 225 50 215 219 211 32 64 128), lower := (rows 225 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 8 0 255 255 255), good := (rows 225 227 229 233 225 225 225 225) },{ target := 6, region := (rows 1 18 4 8 16 255 0 255), good := (rows 161 178 164 168 178 160 160 160) },{ target := 7, region := (rows 1 18 4 8 16 255 255 0), good := (rows 97 114 100 104 114 96 96 96) }] }

theorem profile8_node39 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,48] 6 211 profile8_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,48] 6 211 profile8_node39_cert).mp (by decide +kernel))

def profile8_node40_cert : CutBound 8 := { lost := (rows 16 144 0 0 0 0 0 0), upper := (rows 225 98 151 155 147 32 64 128), lower := (rows 225 98 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 255 255 255), good := (rows 227 227 231 235 227 227 227 227) },{ target := 7, region := (rows 1 255 4 8 16 255 255 0), good := (rows 99 98 102 106 114 98 98 98) }] }

theorem profile8_node40 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,96] 6 147 profile8_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224,96] 6 147 profile8_node40_cert).mp (by decide +kernel))

def profile8_node32_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile8_node32_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile8_node32 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [224] 6 (by decide) (choices 2) [17,33,48,96] profile8_node32_route profile8_node32_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node33
  · exact profile8_node38
  · exact profile8_node39
  · exact profile8_node40

def profile8_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 134 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 138 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile8_node0_route : Route 8 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 162 => (98,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 194 => (98,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile8_node0 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [] 6 (by decide) (choices 3) [50,98,112,224] profile8_node0_route profile8_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node1
  · exact profile8_node16
  · exact profile8_node24
  · exact profile8_node32

theorem profile8 : Upper (D (n:=8) [49,33,32,32,18,2,2,2]) (R (n:=8) [49,33,32,32,18,2,2,2]) [] 6 := profile8_node0


#print axioms profile8
end Delivery.SmallBudgetTenFinite8
