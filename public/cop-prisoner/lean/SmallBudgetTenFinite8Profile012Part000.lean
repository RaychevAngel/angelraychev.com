import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile12_node2_cert : CutBound 8 := { lost := (rows 192 192 32 32 32 0 0 0), upper := (rows 35 35 199 203 211 32 64 128), lower := (rows 35 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 223 223 196 200 208 192 192 192) },{ target := 6, region := (rows 255 255 4 8 16 255 0 255), good := (rows 163 163 167 171 179 163 163 163) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile12_node2 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,33] 6 195 profile12_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,33] 6 195 profile12_node2_cert).mp (by decide +kernel))

def profile12_node4_cert : CutBound 8 := { lost := (rows 64 32 96 3 3 0 0 0), upper := (rows 35 67 7 232 240 32 64 128), lower := (rows 35 67 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 255 255 255 255 255), good := (rows 250 250 254 248 248 248 248 248) },{ target := 1, region := (rows 1 0 4 255 255 255 255 255), good := (rows 249 249 253 248 248 248 248 248) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 7 2 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile12_node4 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,3] 6 224 profile12_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,3] 6 224 profile12_node4_cert).mp (by decide +kernel))

def profile12_node5_cert : CutBound 8 := { lost := (rows 64 32 66 33 33 0 0 0), upper := (rows 35 67 37 202 210 32 64 128), lower := (rows 35 67 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 11 19 255 255 255), good := (rows 250 250 252 232 240 224 224 224) },{ target := 1, region := (rows 1 0 7 8 16 255 255 255), good := (rows 229 229 229 232 240 224 224 224) },{ target := 5, region := (rows 1 7 4 15 23 0 255 255), good := (rows 219 219 223 200 208 192 192 192) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile12_node5 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,33] 6 194 profile12_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,33] 6 194 profile12_node5_cert).mp (by decide +kernel))

def profile12_node6_cert : CutBound 8 := { lost := (rows 64 32 65 34 34 0 0 0), upper := (rows 35 67 38 201 209 32 64 128), lower := (rows 35 67 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 7 8 16 255 255 255), good := (rows 230 230 230 232 240 224 224 224) },{ target := 1, region := (rows 1 0 4 11 19 255 255 255), good := (rows 249 249 252 232 240 224 224 224) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 222 200 208 192 192 192) },{ target := 6, region := (rows 7 2 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile12_node6 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,34] 6 193 profile12_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,34] 6 193 profile12_node6_cert).mp (by decide +kernel))

def profile12_node7_cert : CutBound 8 := { lost := (rows 64 32 34 65 65 0 0 0), upper := (rows 35 67 69 170 178 32 64 128), lower := (rows 35 67 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 11 19 255 255 255), good := (rows 250 250 252 232 240 224 224 224) },{ target := 1, region := (rows 1 0 7 8 16 255 255 255), good := (rows 229 229 229 232 240 224 224 224) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 11 19 255 0 255), good := (rows 187 187 189 168 176 160 160 160) }] }

theorem profile12_node7 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,65] 6 162 profile12_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,65] 6 162 profile12_node7_cert).mp (by decide +kernel))

def profile12_node8_cert : CutBound 8 := { lost := (rows 64 32 33 66 66 0 0 0), upper := (rows 35 67 70 169 177 32 64 128), lower := (rows 35 67 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 7 8 16 255 255 255), good := (rows 230 230 230 232 240 224 224 224) },{ target := 1, region := (rows 1 0 4 11 19 255 255 255), good := (rows 249 249 252 232 240 224 224 224) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 199 199 198 200 208 192 192 192) },{ target := 6, region := (rows 7 2 4 15 23 255 0 255), good := (rows 187 187 191 168 176 160 160 160) }] }

theorem profile12_node8 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,66] 6 161 profile12_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,66] 6 161 profile12_node8_cert).mp (by decide +kernel))

def profile12_node9_cert : CutBound 8 := { lost := (rows 64 32 3 96 96 0 0 0), upper := (rows 35 67 100 139 147 32 64 128), lower := (rows 35 67 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 1, region := (rows 1 0 255 8 16 255 255 255), good := (rows 229 229 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 11 19 255 0 255), good := (rows 187 187 164 168 176 160 160 160) }] }

theorem profile12_node9 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,96] 6 131 profile12_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,96] 6 131 profile12_node9_cert).mp (by decide +kernel))

def profile12_node10_cert : CutBound 8 := { lost := (rows 64 32 98 1 1 0 0 0), upper := (rows 35 67 133 234 242 32 64 128), lower := (rows 35 67 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 11 19 255 255 255), good := (rows 250 250 252 232 240 224 224 224) },{ target := 1, region := (rows 1 0 7 8 16 255 255 255), good := (rows 229 229 229 232 240 224 224 224) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile12_node10 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,129] 6 226 profile12_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,129] 6 226 profile12_node10_cert).mp (by decide +kernel))

def profile12_node11_cert : CutBound 8 := { lost := (rows 64 32 97 2 2 0 0 0), upper := (rows 35 67 134 233 241 32 64 128), lower := (rows 35 67 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 7 8 16 255 255 255), good := (rows 230 230 230 232 240 224 224 224) },{ target := 1, region := (rows 1 0 4 11 19 255 255 255), good := (rows 249 249 252 232 240 224 224 224) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 199 199 198 200 208 192 192 192) },{ target := 6, region := (rows 7 2 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile12_node11 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,130] 6 225 profile12_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,130] 6 225 profile12_node11_cert).mp (by decide +kernel))

def profile12_node12_cert : CutBound 8 := { lost := (rows 64 32 67 32 32 0 0 0), upper := (rows 35 67 164 203 211 32 64 128), lower := (rows 35 67 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 1, region := (rows 1 0 255 8 16 255 255 255), good := (rows 229 229 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) }] }

theorem profile12_node12 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,160] 6 195 profile12_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,160] 6 195 profile12_node12_cert).mp (by decide +kernel))

def profile12_node13_cert : CutBound 8 := { lost := (rows 64 32 35 64 64 0 0 0), upper := (rows 35 67 196 171 179 32 64 128), lower := (rows 35 67 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 230 230 228 236 244 228 228 228) },{ target := 1, region := (rows 1 0 255 8 16 255 255 255), good := (rows 229 229 228 236 244 228 228 228) },{ target := 5, region := (rows 1 3 255 8 16 0 255 255), good := (rows 199 199 196 204 212 196 196 196) },{ target := 6, region := (rows 3 2 4 11 19 255 0 255), good := (rows 187 187 164 168 176 160 160 160) }] }

theorem profile12_node13 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,192] 6 163 profile12_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65,192] 6 163 profile12_node13_cert).mp (by decide +kernel))

def profile12_node3_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile12_node3_route : Route 8 := (fun mask => (mask,id))

theorem profile12_node3 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,65] 6 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] profile12_node3_route profile12_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node4
  · exact profile12_node5
  · exact profile12_node6
  · exact profile12_node7
  · exact profile12_node8
  · exact profile12_node9
  · exact profile12_node10
  · exact profile12_node11
  · exact profile12_node12
  · exact profile12_node13

def profile12_node14_cert : CutBound 8 := { lost := (rows 192 129 32 32 32 0 0 0), upper := (rows 35 98 199 203 211 32 64 128), lower := (rows 35 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 223 194 196 200 208 192 192 192) },{ target := 6, region := (rows 3 2 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile12_node14 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,96] 6 195 profile12_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,96] 6 195 profile12_node14_cert).mp (by decide +kernel))

def profile12_node16_cert : CutBound 8 := { lost := (rows 64 33 96 2 2 0 0 0), upper := (rows 35 194 7 233 241 32 64 128), lower := (rows 35 194 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 1 0 4 13 21 255 255 255), good := (rows 249 224 253 232 240 224 224 224) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 199 194 199 202 210 194 194 194) },{ target := 6, region := (rows 7 2 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile12_node16 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,3] 6 225 profile12_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,3] 6 225 profile12_node16_cert).mp (by decide +kernel))

def profile12_node17_cert : CutBound 8 := { lost := (rows 64 33 66 32 32 0 0 0), upper := (rows 35 194 37 203 211 32 64 128), lower := (rows 35 194 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 1 0 5 8 16 255 255 255), good := (rows 229 224 229 232 240 224 224 224) },{ target := 5, region := (rows 1 255 4 13 21 0 255 255), good := (rows 219 194 223 202 210 194 194 194) },{ target := 6, region := (rows 3 2 7 8 16 255 0 255), good := (rows 167 167 165 168 176 160 160 160) }] }

theorem profile12_node17 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,33] 6 195 profile12_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,33] 6 195 profile12_node17_cert).mp (by decide +kernel))

def profile12_node18_cert : CutBound 8 := { lost := (rows 0 33 1 34 34 0 0 0), upper := (rows 35 194 38 201 209 32 64 128), lower := (rows 35 194 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 1 0 4 9 17 255 255 255), good := (rows 249 224 228 232 240 224 224 224) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 198 202 210 194 194 194) }] }

theorem profile12_node18 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,34] 6 193 profile12_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,34] 6 193 profile12_node18_cert).mp (by decide +kernel))

def profile12_node19_cert : CutBound 8 := { lost := (rows 64 33 34 64 64 0 0 0), upper := (rows 35 194 69 171 179 32 64 128), lower := (rows 35 194 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 1 0 5 8 16 255 255 255), good := (rows 229 224 229 232 240 224 224 224) },{ target := 5, region := (rows 1 255 5 8 16 0 255 255), good := (rows 199 194 199 202 210 194 194 194) },{ target := 6, region := (rows 3 2 4 11 19 255 0 255), good := (rows 187 187 189 168 176 160 160 160) }] }

theorem profile12_node19 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,65] 6 163 profile12_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,65] 6 163 profile12_node19_cert).mp (by decide +kernel))

def profile12_node20_cert : CutBound 8 := { lost := (rows 64 33 33 66 66 0 0 0), upper := (rows 35 194 70 169 177 32 64 128), lower := (rows 35 194 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 1 0 4 9 17 255 255 255), good := (rows 249 224 228 232 240 224 224 224) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 199 198 198 206 214 198 198 198) },{ target := 6, region := (rows 7 2 4 15 23 255 0 255), good := (rows 187 187 191 168 176 160 160 160) }] }

theorem profile12_node20 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,66] 6 161 profile12_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,66] 6 161 profile12_node20_cert).mp (by decide +kernel))

def profile12_node21_cert : CutBound 8 := { lost := (rows 64 33 3 96 96 0 0 0), upper := (rows 35 194 100 139 147 32 64 128), lower := (rows 35 194 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 1 0 255 8 16 255 255 255), good := (rows 229 228 228 236 244 228 228 228) },{ target := 5, region := (rows 1 255 4 9 17 0 255 255), good := (rows 219 194 198 202 210 194 194 194) },{ target := 6, region := (rows 3 2 4 11 19 255 0 255), good := (rows 187 187 164 168 176 160 160 160) }] }

theorem profile12_node21 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,96] 6 131 profile12_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,96] 6 131 profile12_node21_cert).mp (by decide +kernel))

def profile12_node22_cert : CutBound 8 := { lost := (rows 64 33 35 64 64 0 0 0), upper := (rows 35 194 196 43 51 32 64 128), lower := (rows 35 194 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 1 0 255 8 16 255 255 255), good := (rows 229 228 228 236 244 228 228 228) },{ target := 5, region := (rows 1 255 255 8 16 0 255 255), good := (rows 199 198 198 206 214 198 198 198) },{ target := 6, region := (rows 3 2 4 11 19 255 0 255), good := (rows 187 187 164 168 176 160 160 160) }] }

theorem profile12_node22 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,192] 6 35 profile12_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192,192] 6 35 profile12_node22_cert).mp (by decide +kernel))

def profile12_node15_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile12_node15_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile12_node15 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34,192] 6 (by decide) (choices 2) [3,33,34,65,66,96,192] profile12_node15_route profile12_node15_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node16
  · exact profile12_node17
  · exact profile12_node18
  · exact profile12_node19
  · exact profile12_node20
  · exact profile12_node21
  · exact profile12_node22

def profile12_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile12_node1_route : Route 8 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile12_node1 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [34] 6 (by decide) (choices 2) [33,65,96,192] profile12_node1_route profile12_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node2
  · exact profile12_node3
  · exact profile12_node14
  · exact profile12_node15

def profile12_node24_cert : CutBound 8 := { lost := (rows 130 192 32 32 32 0 0 0), upper := (rows 97 35 199 203 211 32 64 128), lower := (rows 97 35 4 8 16 32 64 128), losses := [{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 2 6 10 18 0 255 255), good := (rows 193 223 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile12_node24 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,33] 6 195 profile12_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,33] 6 195 profile12_node24_cert).mp (by decide +kernel))

def profile12_node26_cert : CutBound 8 := { lost := (rows 130 129 128 96 96 0 0 0), upper := (rows 97 98 7 139 147 32 64 128), lower := (rows 97 98 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 2 4 12 20 0 255 255), good := (rows 193 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 2 4 12 20 255 0 255), good := (rows 161 162 191 168 176 160 160 160) },{ target := 7, region := (rows 255 255 255 8 16 255 255 0), good := (rows 103 103 103 111 119 103 103 103) }] }

theorem profile12_node26 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,3] 6 131 profile12_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,3] 6 131 profile12_node26_cert).mp (by decide +kernel))

def profile12_node27_cert : CutBound 8 := { lost := (rows 130 129 98 0 0 0 0 0), upper := (rows 97 98 133 139 147 32 64 128), lower := (rows 97 98 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 2 5 8 16 255 0 255), good := (rows 165 162 165 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile12_node27 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,129] 6 131 profile12_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,129] 6 131 profile12_node27_cert).mp (by decide +kernel))

def profile12_node28_cert : CutBound 8 := { lost := (rows 130 129 97 0 0 0 0 0), upper := (rows 97 98 134 139 147 32 64 128), lower := (rows 97 98 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 2 6 8 16 255 0 255), good := (rows 161 166 166 168 176 160 160 160) },{ target := 7, region := (rows 255 255 4 8 16 255 255 0), good := (rows 99 99 103 107 115 99 99 99) }] }

theorem profile12_node28 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,130] 6 131 profile12_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96,130] 6 131 profile12_node28_cert).mp (by decide +kernel))

def profile12_node25_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 3 | 18 => 4 | 34 => 5 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile12_node25_route : Route 8 := (fun mask => (mask,id))

theorem profile12_node25 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,96] 6 (by decide) (choices 2) [3,129,130] profile12_node25_route profile12_node25_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile12_node26
  · exact profile12_node27
  · exact profile12_node28

def profile12_node30_cert : CutBound 8 := { lost := (rows 2 96 96 1 1 0 0 0), upper := (rows 97 131 7 234 242 32 64 128), lower := (rows 97 131 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 14 22 255 255 255), good := (rows 224 250 254 232 240 224 224 224) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile12_node30 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,3] 6 226 profile12_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,3] 6 226 profile12_node30_cert).mp (by decide +kernel))

def profile12_node31_cert : CutBound 8 := { lost := (rows 2 32 2 33 33 0 0 0), upper := (rows 97 131 37 202 210 32 64 128), lower := (rows 97 131 37 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 255 255 255), good := (rows 224 250 228 232 240 224 224 224) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 7 4 15 23 0 255 255), good := (rows 219 219 223 200 208 192 192 192) }] }

theorem profile12_node31 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,33] 6 194 profile12_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,33] 6 194 profile12_node31_cert).mp (by decide +kernel))

def profile12_node32_cert : CutBound 8 := { lost := (rows 2 96 65 32 32 0 0 0), upper := (rows 97 131 38 203 211 32 64 128), lower := (rows 97 131 38 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 222 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) }] }

theorem profile12_node32 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,34] 6 195 profile12_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,34] 6 195 profile12_node32_cert).mp (by decide +kernel))

def profile12_node33_cert : CutBound 8 := { lost := (rows 2 96 3 96 96 0 0 0), upper := (rows 97 131 100 139 147 32 64 128), lower := (rows 97 131 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 11 19 255 0 255), good := (rows 187 187 164 168 176 160 160 160) }] }

theorem profile12_node33 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,96] 6 131 profile12_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,96] 6 131 profile12_node33_cert).mp (by decide +kernel))

def profile12_node34_cert : CutBound 8 := { lost := (rows 2 96 98 1 1 0 0 0), upper := (rows 97 131 133 106 114 32 64 128), lower := (rows 97 131 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 4 10 18 255 255 255), good := (rows 224 250 228 232 240 224 224 224) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 7 7 8 16 0 255 255), good := (rows 199 199 199 200 208 192 192 192) },{ target := 6, region := (rows 1 7 7 8 16 255 0 255), good := (rows 167 167 167 168 176 160 160 160) }] }

theorem profile12_node34 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,129] 6 98 profile12_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,129] 6 98 profile12_node34_cert).mp (by decide +kernel))

def profile12_node35_cert : CutBound 8 := { lost := (rows 130 96 97 128 128 0 0 0), upper := (rows 97 131 134 107 115 32 64 128), lower := (rows 97 131 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 6 8 16 255 255 255), good := (rows 224 230 230 232 240 224 224 224) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 3 7 8 16 0 255 255), good := (rows 199 199 198 200 208 192 192 192) },{ target := 6, region := (rows 1 3 7 8 16 255 0 255), good := (rows 167 167 166 168 176 160 160 160) },{ target := 7, region := (rows 255 2 4 14 22 255 255 0), good := (rows 97 123 127 105 113 97 97 97) }] }

theorem profile12_node35 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,130] 6 99 profile12_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,130] 6 99 profile12_node35_cert).mp (by decide +kernel))

def profile12_node36_cert : CutBound 8 := { lost := (rows 2 96 67 32 32 0 0 0), upper := (rows 97 131 164 75 83 32 64 128), lower := (rows 97 131 164 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 230 228 236 244 228 228 228) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 3 4 11 19 0 255 255), good := (rows 219 219 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 255 8 16 255 0 255), good := (rows 167 167 164 172 180 164 164 164) }] }

theorem profile12_node36 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,160] 6 67 profile12_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129,160] 6 67 profile12_node36_cert).mp (by decide +kernel))

def profile12_node29_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile12_node29_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node29 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,129] 6 (by decide) (choices 2) [3,33,34,96,129,130,160] profile12_node29_route profile12_node29_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node30
  · exact profile12_node31
  · exact profile12_node32
  · exact profile12_node33
  · exact profile12_node34
  · exact profile12_node35
  · exact profile12_node36

def profile12_node38_cert : CutBound 8 := { lost := (rows 130 65 192 32 32 0 0 0), upper := (rows 97 162 7 203 211 32 64 128), lower := (rows 97 162 7 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 2 4 12 20 0 255 255), good := (rows 193 194 223 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) },{ target := 7, region := (rows 255 2 6 8 16 255 255 0), good := (rows 97 103 103 105 113 97 97 97) }] }

theorem profile12_node38 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,3] 6 195 profile12_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,3] 6 195 profile12_node38_cert).mp (by decide +kernel))

def profile12_node39_cert : CutBound 8 := { lost := (rows 2 65 34 64 64 0 0 0), upper := (rows 97 162 69 139 147 32 64 128), lower := (rows 97 162 69 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 4 13 21 255 0 255), good := (rows 187 162 191 170 178 162 162 162) }] }

theorem profile12_node39 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,65] 6 131 profile12_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,65] 6 131 profile12_node39_cert).mp (by decide +kernel))

def profile12_node40_cert : CutBound 8 := { lost := (rows 2 65 33 64 64 0 0 0), upper := (rows 97 162 70 139 147 32 64 128), lower := (rows 97 162 70 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 255 4 9 17 255 0 255), good := (rows 187 162 166 170 178 162 162 162) }] }

theorem profile12_node40 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,66] 6 131 profile12_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,66] 6 131 profile12_node40_cert).mp (by decide +kernel))

def profile12_node41_cert : CutBound 8 := { lost := (rows 130 65 98 128 128 0 0 0), upper := (rows 97 162 133 75 83 32 64 128), lower := (rows 97 162 133 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 2 5 8 16 0 255 255), good := (rows 197 194 197 200 208 192 192 192) },{ target := 6, region := (rows 1 255 5 8 16 255 0 255), good := (rows 167 162 167 170 178 162 162 162) },{ target := 7, region := (rows 255 2 4 10 18 255 255 0), good := (rows 97 123 101 105 113 97 97 97) }] }

theorem profile12_node41 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,129] 6 67 profile12_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,129] 6 67 profile12_node41_cert).mp (by decide +kernel))

def profile12_node42_cert : CutBound 8 := { lost := (rows 130 65 97 128 128 0 0 0), upper := (rows 97 162 134 75 83 32 64 128), lower := (rows 97 162 134 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 255 0 4 8 16 255 255 255), good := (rows 225 225 229 233 241 225 225 225) },{ target := 5, region := (rows 1 2 6 8 16 0 255 255), good := (rows 193 198 198 200 208 192 192 192) },{ target := 6, region := (rows 1 255 255 8 16 255 0 255), good := (rows 167 166 166 174 182 166 166 166) },{ target := 7, region := (rows 255 2 4 14 22 255 255 0), good := (rows 97 123 127 105 113 97 97 97) }] }

theorem profile12_node42 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,130] 6 67 profile12_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,130] 6 67 profile12_node42_cert).mp (by decide +kernel))

def profile12_node43_cert : CutBound 8 := { lost := (rows 2 65 35 64 64 0 0 0), upper := (rows 97 162 196 11 19 32 64 128), lower := (rows 97 162 196 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 255 8 16 255 255 255), good := (rows 230 230 230 238 246 230 230 230) },{ target := 1, region := (rows 255 0 255 8 16 255 255 255), good := (rows 229 229 229 237 245 229 229 229) },{ target := 5, region := (rows 1 2 255 8 16 0 255 255), good := (rows 197 198 196 204 212 196 196 196) },{ target := 6, region := (rows 1 255 4 9 17 255 0 255), good := (rows 187 162 166 170 178 162 162 162) }] }

theorem profile12_node43 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,192] 6 3 profile12_node43_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160,192] 6 3 profile12_node43_cert).mp (by decide +kernel))

def profile12_node37_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 96 => 5 | 160 => 5 | _ => 0

def profile12_node37_route : Route 8 := (fun mask => (mask,id))

theorem profile12_node37 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96,160] 6 (by decide) (choices 2) [3,65,66,129,130,192] profile12_node37_route profile12_node37_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile12_node38
  · exact profile12_node39
  · exact profile12_node40
  · exact profile12_node41
  · exact profile12_node42
  · exact profile12_node43

def profile12_node23_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile12_node23_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node23 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [96] 6 (by decide) (choices 2) [33,96,129,160] profile12_node23_route profile12_node23_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile12_node24
  · exact profile12_node25
  · exact profile12_node29
  · exact profile12_node37

def profile12_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 2 | 10 => 3 | 18 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile12_node0_route : Route 8 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile12_node0 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [] 6 (by decide) (choices 2) [34,96] profile12_node0_route profile12_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile12_node1
  · exact profile12_node23

theorem profile12 : Upper (D (n:=8) [34,34,32,32,32,2,2,2]) (R (n:=8) [34,34,32,32,32,2,2,2]) [] 6 := profile12_node0


#print axioms profile12
end Delivery.SmallBudgetTenFinite8
