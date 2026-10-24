import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile18_node2_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 49 19 197 201 209 225 64 128), lower := (rows 49 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 255 255), good := (rows 237 239 196 200 192 224 192 192) }] }

theorem profile18_node2 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,17] 6 193 profile18_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,17] 6 193 profile18_node2_cert).mp (by decide +kernel))

def profile18_node3_cert : CutBound 8 := { lost := (rows 0 144 0 0 0 0 0 0), upper := (rows 49 67 213 217 209 241 64 128), lower := (rows 49 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 227 195 196 200 192 224 192 192) },{ target := 7, region := (rows 1 3 4 8 16 32 255 0), good := (rows 115 67 68 72 80 96 64 64) }] }

theorem profile18_node3 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,65] 6 209 profile18_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,65] 6 209 profile18_node3_cert).mp (by decide +kernel))

def profile18_node4_cert : CutBound 8 := { lost := (rows 0 1 16 16 0 0 0 0), upper := (rows 49 82 197 201 209 225 64 128), lower := (rows 49 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 242 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 194 196 200 192 224 192 192) }] }

theorem profile18_node4 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,80] 6 193 profile18_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,80] 6 193 profile18_node4_cert).mp (by decide +kernel))

def profile18_node5_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 49 194 213 217 209 241 64 128), lower := (rows 49 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 242 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 227 194 198 202 194 226 194 194) }] }

theorem profile18_node5 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,192] 6 209 profile18_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48,192] 6 209 profile18_node5_cert).mp (by decide +kernel))

def profile18_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile18_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile18_node1 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [48] 6 (by decide) (choices 2) [17,65,80,192] profile18_node1_route profile18_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile18_node2
  · exact profile18_node3
  · exact profile18_node4
  · exact profile18_node5

def profile18_node7_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 81 19 229 233 241 225 64 128), lower := (rows 81 19 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 11 0 35 255 255), good := (rows 237 239 196 200 192 224 192 192) }] }

theorem profile18_node7 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,17] 6 225 profile18_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,17] 6 225 profile18_node7_cert).mp (by decide +kernel))

def profile18_node9_cert : CutBound 8 := { lost := (rows 0 16 0 16 0 0 0 0), upper := (rows 81 35 21 201 209 225 64 128), lower := (rows 81 35 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 7 4 15 0 39 255 255), good := (rows 235 235 239 200 192 224 192 192) }] }

theorem profile18_node9 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,17] 6 193 profile18_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,17] 6 193 profile18_node9_cert).mp (by decide +kernel))

def profile18_node10_cert : CutBound 8 := { lost := (rows 0 64 16 64 0 0 0 0), upper := (rows 81 35 69 153 145 177 64 128), lower := (rows 81 35 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) },{ target := 6, region := (rows 1 7 4 15 23 39 0 255), good := (rows 187 187 191 136 144 160 128 128) }] }

theorem profile18_node10 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,65] 6 145 profile18_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,65] 6 145 profile18_node10_cert).mp (by decide +kernel))

def profile18_node11_cert : CutBound 8 := { lost := (rows 0 16 1 16 0 0 0 0), upper := (rows 81 35 84 137 145 161 64 128), lower := (rows 81 35 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile18_node11 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,80] 6 129 profile18_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,80] 6 129 profile18_node11_cert).mp (by decide +kernel))

def profile18_node12_cert : CutBound 8 := { lost := (rows 0 0 80 0 0 0 0 0), upper := (rows 81 35 133 217 209 241 64 128), lower := (rows 81 35 133 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 7 8 0 32 255 255), good := (rows 197 231 197 200 192 224 192 192) },{ target := 6, region := (rows 1 2 7 8 16 32 0 255), good := (rows 149 167 133 136 144 160 128 128) }] }

theorem profile18_node12 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,129] 6 209 profile18_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,129] 6 209 profile18_node12_cert).mp (by decide +kernel))

def profile18_node13_cert : CutBound 8 := { lost := (rows 0 16 1 16 0 0 0 0), upper := (rows 81 35 148 201 209 225 64 128), lower := (rows 81 35 148 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 21 8 16 32 255 255), good := (rows 212 230 212 200 212 224 192 192) },{ target := 4, region := (rows 1 3 4 11 0 35 255 255), good := (rows 235 235 196 200 192 224 192 192) }] }

theorem profile18_node13 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,144] 6 193 profile18_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,144] 6 193 profile18_node13_cert).mp (by decide +kernel))

def profile18_node14_cert : CutBound 8 := { lost := (rows 0 0 17 0 0 0 0 0), upper := (rows 81 35 196 153 145 177 64 128), lower := (rows 81 35 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 212 230 196 204 212 228 196 196) },{ target := 4, region := (rows 1 2 255 8 0 32 255 255), good := (rows 197 231 196 204 196 228 196 196) }] }

theorem profile18_node14 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,192] 6 145 profile18_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33,192] 6 145 profile18_node14_cert).mp (by decide +kernel))

def profile18_node8_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile18_node8_route : Route 8 := (fun mask => (mask,id))

theorem profile18_node8 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,33] 6 (by decide) (choices 2) [17,65,80,129,144,192] profile18_node8_route profile18_node8_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node9
  · exact profile18_node10
  · exact profile18_node11
  · exact profile18_node12
  · exact profile18_node13
  · exact profile18_node14

def profile18_node15_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 81 50 197 201 209 225 64 128), lower := (rows 81 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 226 196 200 192 224 192 192) }] }

theorem profile18_node15 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,48] 6 193 profile18_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,48] 6 193 profile18_node15_cert).mp (by decide +kernel))

def profile18_node16_cert : CutBound 8 := { lost := (rows 0 16 64 64 0 0 0 0), upper := (rows 81 67 181 185 177 177 64 128), lower := (rows 81 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 2 7 11 19 35 0 255), good := (rows 189 191 132 136 144 160 128 128) }] }

theorem profile18_node16 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,65] 6 177 profile18_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,65] 6 177 profile18_node16_cert).mp (by decide +kernel))

def profile18_node17_cert : CutBound 8 := { lost := (rows 0 1 16 16 0 0 0 0), upper := (rows 81 82 165 169 177 161 64 128), lower := (rows 81 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 194 196 200 192 224 192 192) }] }

theorem profile18_node17 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,80] 6 161 profile18_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,80] 6 161 profile18_node17_cert).mp (by decide +kernel))

def profile18_node18_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 81 98 149 153 145 177 64 128), lower := (rows 81 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) }] }

theorem profile18_node18 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,96] 6 145 profile18_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,96] 6 145 profile18_node18_cert).mp (by decide +kernel))

def profile18_node19_cert : CutBound 8 := { lost := (rows 0 80 0 0 0 0 0 0), upper := (rows 81 131 245 249 241 241 64 128), lower := (rows 81 131 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 8 0 32 255 255), good := (rows 195 195 196 200 192 224 192 192) },{ target := 6, region := (rows 1 3 4 8 16 32 0 255), good := (rows 147 131 132 136 144 160 128 128) }] }

theorem profile18_node19 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,129] 6 241 profile18_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,129] 6 241 profile18_node19_cert).mp (by decide +kernel))

def profile18_node20_cert : CutBound 8 := { lost := (rows 0 1 16 16 0 0 0 0), upper := (rows 81 146 229 233 241 225 64 128), lower := (rows 81 146 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 19 4 8 16 32 255 255), good := (rows 210 210 196 200 210 224 192 192) },{ target := 4, region := (rows 1 2 5 9 0 33 255 255), good := (rows 237 194 196 200 192 224 192 192) }] }

theorem profile18_node20 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,144] 6 225 profile18_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,144] 6 225 profile18_node20_cert).mp (by decide +kernel))

def profile18_node21_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 81 162 213 217 209 241 64 128), lower := (rows 81 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 208 226 196 200 208 226 192 192) },{ target := 4, region := (rows 1 34 4 8 0 32 255 255), good := (rows 193 226 196 200 192 226 192 192) }] }

theorem profile18_node21 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,160] 6 209 profile18_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,160] 6 209 profile18_node21_cert).mp (by decide +kernel))

def profile18_node22_cert : CutBound 8 := { lost := (rows 0 17 0 0 0 0 0 0), upper := (rows 81 194 181 185 177 177 64 128), lower := (rows 81 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 210 194 198 202 210 226 194 194) },{ target := 4, region := (rows 1 255 4 8 0 32 255 255), good := (rows 195 194 198 202 194 226 194 194) }] }

theorem profile18_node22 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,192] 6 177 profile18_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80,192] 6 177 profile18_node22_cert).mp (by decide +kernel))

def profile18_node6_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile18_node6_route : Route 8 := (fun mask => (mask,id))

theorem profile18_node6 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [80] 6 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] profile18_node6_route profile18_node6_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node7
  · exact profile18_node8
  · exact profile18_node15
  · exact profile18_node16
  · exact profile18_node17
  · exact profile18_node18
  · exact profile18_node19
  · exact profile18_node20
  · exact profile18_node21
  · exact profile18_node22

def profile18_node23_cert : CutBound 8 := { lost := (rows 144 0 0 0 0 0 0 0), upper := (rows 97 211 213 217 209 241 64 128), lower := (rows 97 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 255 255), good := (rows 225 194 196 200 192 225 192 192) },{ target := 7, region := (rows 33 2 4 8 16 32 255 0), good := (rows 97 66 68 72 80 97 64 64) }] }

theorem profile18_node23 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [96] 6 209 profile18_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [96] 6 209 profile18_node23_cert).mp (by decide +kernel))

def profile18_node26_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 19 21 233 241 225 64 128), lower := (rows 193 19 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile18_node26 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,17] 6 225 profile18_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,17] 6 225 profile18_node26_cert).mp (by decide +kernel))

def profile18_node27_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 19 37 217 209 241 64 128), lower := (rows 193 19 37 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) }] }

theorem profile18_node27 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,33] 6 209 profile18_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,33] 6 209 profile18_node27_cert).mp (by decide +kernel))

def profile18_node28_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 19 52 201 209 225 64 128), lower := (rows 193 19 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile18_node28 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,48] 6 193 profile18_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,48] 6 193 profile18_node28_cert).mp (by decide +kernel))

def profile18_node29_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 19 69 185 177 177 64 128), lower := (rows 193 19 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile18_node29 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,65] 6 177 profile18_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,65] 6 177 profile18_node29_cert).mp (by decide +kernel))

def profile18_node30_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 19 84 169 177 161 64 128), lower := (rows 193 19 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 214 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile18_node30 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,80] 6 161 profile18_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,80] 6 161 profile18_node30_cert).mp (by decide +kernel))

def profile18_node31_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 100 153 145 177 64 128), lower := (rows 193 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 255 255), good := (rows 192 210 228 200 208 228 192 192) },{ target := 4, region := (rows 255 2 36 8 0 32 255 255), good := (rows 193 195 229 201 193 229 193 193) }] }

theorem profile18_node31 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,96] 6 145 profile18_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,96] 6 145 profile18_node31_cert).mp (by decide +kernel))

def profile18_node32_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 19 196 57 49 49 64 128), lower := (rows 193 19 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 214 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 199 197 205 197 229 197 197) }] }

theorem profile18_node32 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,192] 6 49 profile18_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17,192] 6 49 profile18_node32_cert).mp (by decide +kernel))

def profile18_node25_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile18_node25_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile18_node25 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,17] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile18_node25_route profile18_node25_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node26
  · exact profile18_node27
  · exact profile18_node28
  · exact profile18_node29
  · exact profile18_node30
  · exact profile18_node31
  · exact profile18_node32

def profile18_node33_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 35 213 217 209 241 64 128), lower := (rows 193 35 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile18_node33 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,33] 6 209 profile18_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,33] 6 209 profile18_node33_cert).mp (by decide +kernel))

def profile18_node35_cert : CutBound 8 := { lost := (rows 16 0 0 16 0 0 0 0), upper := (rows 193 50 21 201 209 225 64 128), lower := (rows 193 50 21 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile18_node35 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,17] 6 193 profile18_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,17] 6 193 profile18_node35_cert).mp (by decide +kernel))

def profile18_node36_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 193 50 69 153 145 177 64 128), lower := (rows 193 50 69 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) }] }

theorem profile18_node36 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,65] 6 145 profile18_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,65] 6 145 profile18_node36_cert).mp (by decide +kernel))

def profile18_node37_cert : CutBound 8 := { lost := (rows 16 0 1 16 0 0 0 0), upper := (rows 193 50 84 137 145 161 64 128), lower := (rows 193 50 84 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 22 8 16 32 255 255), good := (rows 192 246 212 200 212 224 192 192) },{ target := 4, region := (rows 255 2 4 255 0 255 255 255), good := (rows 233 235 237 233 233 233 233 233) }] }

theorem profile18_node37 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,80] 6 129 profile18_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,80] 6 129 profile18_node37_cert).mp (by decide +kernel))

def profile18_node38_cert : CutBound 8 := { lost := (rows 16 0 17 0 0 0 0 0), upper := (rows 193 50 196 25 17 49 64 128), lower := (rows 193 50 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 32 255 255), good := (rows 196 246 196 204 212 228 196 196) },{ target := 4, region := (rows 255 2 255 8 0 32 255 255), good := (rows 197 231 197 205 197 229 197 197) }] }

theorem profile18_node38 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,192] 6 17 profile18_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48,192] 6 17 profile18_node38_cert).mp (by decide +kernel))

def profile18_node34_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile18_node34_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile18_node34 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,48] 6 (by decide) (choices 2) [17,65,80,192] profile18_node34_route profile18_node34_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile18_node35
  · exact profile18_node36
  · exact profile18_node37
  · exact profile18_node38

def profile18_node39_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 193 67 181 185 177 177 64 128), lower := (rows 193 67 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile18_node39 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,65] 6 177 profile18_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,65] 6 177 profile18_node39_cert).mp (by decide +kernel))

def profile18_node40_cert : CutBound 8 := { lost := (rows 16 1 0 0 0 0 0 0), upper := (rows 193 82 181 185 177 177 64 128), lower := (rows 193 82 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 32 255 255), good := (rows 192 210 196 200 210 224 192 192) },{ target := 4, region := (rows 255 2 4 8 0 32 255 255), good := (rows 193 195 197 201 193 225 193 193) }] }

theorem profile18_node40 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,80] 6 177 profile18_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,80] 6 177 profile18_node40_cert).mp (by decide +kernel))

def profile18_node41_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 193 98 149 153 145 177 64 128), lower := (rows 193 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 34 4 8 16 32 255 255), good := (rows 192 226 196 200 208 226 192 192) },{ target := 4, region := (rows 255 34 4 8 0 32 255 255), good := (rows 193 227 197 201 193 227 193 193) }] }

theorem profile18_node41 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,96] 6 145 profile18_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,96] 6 145 profile18_node41_cert).mp (by decide +kernel))

def profile18_node42_cert : CutBound 8 := { lost := (rows 16 17 0 0 0 0 0 0), upper := (rows 193 194 53 57 49 49 64 128), lower := (rows 193 194 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 32 255 255), good := (rows 194 194 198 202 210 226 194 194) },{ target := 4, region := (rows 255 255 4 8 0 32 255 255), good := (rows 195 195 199 203 195 227 195 195) }] }

theorem profile18_node42 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,192] 6 49 profile18_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192,192] 6 49 profile18_node42_cert).mp (by decide +kernel))

def profile18_node24_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile18_node24_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile18_node24 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [192] 6 (by decide) (choices 2) [17,33,48,65,80,96,192] profile18_node24_route profile18_node24_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile18_node25
  · exact profile18_node33
  · exact profile18_node34
  · exact profile18_node39
  · exact profile18_node40
  · exact profile18_node41
  · exact profile18_node42

def profile18_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile18_node0_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile18_node0 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [] 6 (by decide) (choices 2) [48,80,96,192] profile18_node0_route profile18_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile18_node1
  · exact profile18_node6
  · exact profile18_node23
  · exact profile18_node24

theorem profile18 : Upper (D (n:=8) [35,32,32,32,18,17,2,2]) (R (n:=8) [35,32,32,32,18,17,2,2]) [] 6 := profile18_node0


#print axioms profile18
end Delivery.SmallBudgetTenFinite8
