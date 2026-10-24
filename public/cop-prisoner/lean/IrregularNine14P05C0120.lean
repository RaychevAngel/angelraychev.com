import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0060
import IrregularNine14P05C0061

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7200 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 38 76 137 28 291 355 419 291), lower := (rows 19 38 76 137 28 32 64 128 256), losses := [] }

theorem u7200 : Upper (D 5) (R 5) [18,36,72,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7201 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 137 49 302 334 398 270), lower := (rows 19 38 76 137 49 32 64 128 256), losses := [] }

theorem u7201 : Upper (D 5) (R 5) [18,36,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7202 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 137 50 301 333 397 269), lower := (rows 19 38 76 137 50 32 64 128 256), losses := [] }

theorem u7202 : Upper (D 5) (R 5) [18,36,72,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7203 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 137 52 299 331 395 267), lower := (rows 19 38 76 137 52 32 64 128 256), losses := [] }

theorem u7203 : Upper (D 5) (R 5) [18,36,72,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7204 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 137 56 295 327 391 263), lower := (rows 19 38 76 137 56 32 64 128 256), losses := [] }

theorem u7204 : Upper (D 5) (R 5) [18,36,72,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7205 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 137 273 46 110 174 302), lower := (rows 19 38 76 137 273 32 64 128 256), losses := [] }

theorem u7205 : Upper (D 5) (R 5) [18,36,72,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7205
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7206 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 137 274 45 109 173 301), lower := (rows 19 38 76 137 274 32 64 128 256), losses := [] }

theorem u7206 : Upper (D 5) (R 5) [18,36,72,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7206
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7207 : Route 9 := (fun mask => (mask,id))

def c7207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7207 : Upper (D 5) (R 5) [18,36,72,129,260] 13 := by
  apply FastRouting.sound _ _ [18,36,72,129,260] 13 (by decide) (choices 1) [1,2,8] r7207 c7207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3659
  · exact u3660
  · exact u3661

def r7208 : Route 9 := (fun mask => (mask,id))

def c7208 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7208 : Upper (D 5) (R 5) [18,36,72,129,264] 13 := by
  apply FastRouting.sound _ _ [18,36,72,129,264] 13 (by decide) (choices 1) [1,2,4] r7208 c7208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3662
  · exact u3663
  · exact u3664

def b7209 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 137 304 47 79 143 271), lower := (rows 19 38 76 137 304 32 64 128 256), losses := [] }

theorem u7209 : Upper (D 5) (R 5) [18,36,72,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7210 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 138 21 297 361 425 297), lower := (rows 19 38 76 138 21 32 64 128 256), losses := [] }

theorem u7210 : Upper (D 5) (R 5) [18,36,72,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7211 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 38 76 138 25 293 357 421 293), lower := (rows 19 38 76 138 25 32 64 128 256), losses := [] }

theorem u7211 : Upper (D 5) (R 5) [18,36,72,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7211
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7212 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 38 76 138 28 289 353 417 289), lower := (rows 19 38 76 138 28 32 64 128 256), losses := [] }

theorem u7212 : Upper (D 5) (R 5) [18,36,72,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7212
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7213 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 138 49 301 333 397 269), lower := (rows 19 38 76 138 49 32 64 128 256), losses := [] }

theorem u7213 : Upper (D 5) (R 5) [18,36,72,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7214 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 138 52 297 329 393 265), lower := (rows 19 38 76 138 52 32 64 128 256), losses := [] }

theorem u7214 : Upper (D 5) (R 5) [18,36,72,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7215 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 138 56 293 325 389 261), lower := (rows 19 38 76 138 56 32 64 128 256), losses := [] }

theorem u7215 : Upper (D 5) (R 5) [18,36,72,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7216 : Route 9 := (fun mask => (mask,id))

def c7216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7216 : Upper (D 5) (R 5) [18,36,72,130,257] 13 := by
  apply FastRouting.sound _ _ [18,36,72,130,257] 13 (by decide) (choices 1) [1,4,8] r7216 c7216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3665
  · exact u3666
  · exact u3667

def r7217 : Route 9 := (fun mask => (mask,id))

def c7217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7217 : Upper (D 5) (R 5) [18,36,72,130,260] 13 := by
  apply FastRouting.sound _ _ [18,36,72,130,260] 13 (by decide) (choices 1) [1,8] r7217 c7217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3668
  · exact u3669

def r7218 : Route 9 := (fun mask => (mask,id))

def c7218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7218 : Upper (D 5) (R 5) [18,36,72,130,264] 13 := by
  apply FastRouting.sound _ _ [18,36,72,130,264] 13 (by decide) (choices 1) [1,4] r7218 c7218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3670
  · exact u3671

def b7219 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 138 304 45 77 141 269), lower := (rows 19 38 76 138 304 32 64 128 256), losses := [] }

theorem u7219 : Upper (D 5) (R 5) [18,36,72,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7219
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7220 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 140 19 297 361 425 297), lower := (rows 19 38 76 140 19 32 64 128 256), losses := [] }

theorem u7220 : Upper (D 5) (R 5) [18,36,72,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7221 : Route 9 := (fun mask => (mask,id))

def c7221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7221 : Upper (D 5) (R 5) [18,36,72,132,9] 13 := by
  apply FastRouting.sound _ _ [18,36,72,132,9] 13 (by decide) (choices 1) [1,2,256] r7221 c7221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3672
  · exact u3673
  · exact u3674

def b7222 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 38 76 140 26 289 353 417 289), lower := (rows 19 38 76 140 26 32 64 128 256), losses := [] }

theorem u7222 : Upper (D 5) (R 5) [18,36,72,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7222
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7223 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 140 49 299 331 395 267), lower := (rows 19 38 76 140 49 32 64 128 256), losses := [] }

theorem u7223 : Upper (D 5) (R 5) [18,36,72,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7223
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7224 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 140 50 297 329 393 265), lower := (rows 19 38 76 140 50 32 64 128 256), losses := [] }

theorem u7224 : Upper (D 5) (R 5) [18,36,72,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7225 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 140 56 291 323 387 259), lower := (rows 19 38 76 140 56 32 64 128 256), losses := [] }

theorem u7225 : Upper (D 5) (R 5) [18,36,72,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7225
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7226 : Route 9 := (fun mask => (mask,id))

def c7226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7226 : Upper (D 5) (R 5) [18,36,72,132,257] 13 := by
  apply FastRouting.sound _ _ [18,36,72,132,257] 13 (by decide) (choices 1) [1,2,8] r7226 c7226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3675
  · exact u3676
  · exact u3677

def b7227 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 140 274 41 105 169 297), lower := (rows 19 38 76 140 274 32 64 128 256), losses := [] }

theorem u7227 : Upper (D 5) (R 5) [18,36,72,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7228 : Route 9 := (fun mask => (mask,id))

def c7228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7228 : Upper (D 5) (R 5) [18,36,72,132,264] 13 := by
  apply FastRouting.sound _ _ [18,36,72,132,264] 13 (by decide) (choices 1) [1,2] r7228 c7228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3678
  · exact u3679

def b7229 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 140 304 43 75 139 267), lower := (rows 19 38 76 140 304 32 64 128 256), losses := [] }

theorem u7229 : Upper (D 5) (R 5) [18,36,72,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7229
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7230 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 168 19 301 333 397 269), lower := (rows 19 38 76 168 19 32 64 128 256), losses := [] }

theorem u7230 : Upper (D 5) (R 5) [18,36,72,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7231 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 168 21 299 331 395 267), lower := (rows 19 38 76 168 21 32 64 128 256), losses := [] }

theorem u7231 : Upper (D 5) (R 5) [18,36,72,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7232 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 168 22 297 329 393 265), lower := (rows 19 38 76 168 22 32 64 128 256), losses := [] }

theorem u7232 : Upper (D 5) (R 5) [18,36,72,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7232
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7233 : Route 9 := (fun mask => (mask,id))

def c7233 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7233 : Upper (D 5) (R 5) [18,36,72,160,9] 13 := by
  apply FastRouting.sound _ _ [18,36,72,160,9] 13 (by decide) (choices 1) [1,2,4,256] r7233 c7233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3680
  · exact u3681
  · exact u3682
  · exact u3683

def b7234 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 19 38 76 168 26 293 325 389 261), lower := (rows 19 38 76 168 26 32 64 128 256), losses := [] }

theorem u7234 : Upper (D 5) (R 5) [18,36,72,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7234
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7235 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 38 76 168 28 291 323 387 259), lower := (rows 19 38 76 168 28 32 64 128 256), losses := [] }

theorem u7235 : Upper (D 5) (R 5) [18,36,72,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7235
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7236 : Route 9 := (fun mask => (mask,id))

def c7236 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7236 : Upper (D 5) (R 5) [18,36,72,160,257] 13 := by
  apply FastRouting.sound _ _ [18,36,72,160,257] 13 (by decide) (choices 1) [1,2,4,8] r7236 c7236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3684
  · exact u3685
  · exact u3686
  · exact u3687

def b7237 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 168 274 45 77 141 269), lower := (rows 19 38 76 168 274 32 64 128 256), losses := [] }

theorem u7237 : Upper (D 5) (R 5) [18,36,72,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7238 : Route 9 := (fun mask => (mask,id))

def c7238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7238 : Upper (D 5) (R 5) [18,36,72,160,260] 13 := by
  apply FastRouting.sound _ _ [18,36,72,160,260] 13 (by decide) (choices 1) [1,2,8] r7238 c7238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3688
  · exact u3689
  · exact u3690

def r7239 : Route 9 := (fun mask => (mask,id))

def c7239 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7239 : Upper (D 5) (R 5) [18,36,72,160,264] 13 := by
  apply FastRouting.sound _ _ [18,36,72,160,264] 13 (by decide) (choices 1) [1,2,4] r7239 c7239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3691
  · exact u3692
  · exact u3693

def b7240 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 392 19 45 109 173 301), lower := (rows 19 38 76 392 19 32 64 128 256), losses := [] }

theorem u7240 : Upper (D 5) (R 5) [18,36,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7240
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7241 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 392 21 43 107 171 299), lower := (rows 19 38 76 392 21 32 64 128 256), losses := [] }

theorem u7241 : Upper (D 5) (R 5) [18,36,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7241
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7242 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 392 22 41 105 169 297), lower := (rows 19 38 76 392 22 32 64 128 256), losses := [] }

theorem u7242 : Upper (D 5) (R 5) [18,36,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7242
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7243 : Route 9 := (fun mask => (mask,id))

def c7243 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7243 : Upper (D 5) (R 5) [18,36,72,384,9] 13 := by
  apply FastRouting.sound _ _ [18,36,72,384,9] 13 (by decide) (choices 1) [1,2,4] r7243 c7243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3694
  · exact u3695
  · exact u3696

def b7244 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 392 26 37 101 165 293), lower := (rows 19 38 76 392 26 32 64 128 256), losses := [] }

theorem u7244 : Upper (D 5) (R 5) [18,36,72,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7244
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7245 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 38 76 392 28 35 99 163 291), lower := (rows 19 38 76 392 28 32 64 128 256), losses := [] }

theorem u7245 : Upper (D 5) (R 5) [18,36,72,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7246 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 392 49 47 79 143 271), lower := (rows 19 38 76 392 49 32 64 128 256), losses := [] }

theorem u7246 : Upper (D 5) (R 5) [18,36,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7246
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7247 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 392 50 45 77 141 269), lower := (rows 19 38 76 392 50 32 64 128 256), losses := [] }

theorem u7247 : Upper (D 5) (R 5) [18,36,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7248 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 392 52 43 75 139 267), lower := (rows 19 38 76 392 52 32 64 128 256), losses := [] }

theorem u7248 : Upper (D 5) (R 5) [18,36,72,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7249 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 19 38 76 392 56 39 71 135 263), lower := (rows 19 38 76 392 56 32 64 128 256), losses := [] }

theorem u7249 : Upper (D 5) (R 5) [18,36,72,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7249
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7250 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 41 19 300 332 396 268), lower := (rows 19 38 196 41 19 32 64 128 256), losses := [] }

theorem u7250 : Upper (D 5) (R 5) [18,36,192,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7251 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 41 21 298 330 394 266), lower := (rows 19 38 196 41 21 32 64 128 256), losses := [] }

theorem u7251 : Upper (D 5) (R 5) [18,36,192,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7252 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 196 41 22 297 329 393 265), lower := (rows 19 38 196 41 22 32 64 128 256), losses := [] }

theorem u7252 : Upper (D 5) (R 5) [18,36,192,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7252
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7253 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 196 41 25 302 334 398 270), lower := (rows 19 38 196 41 25 32 64 128 256), losses := [] }

theorem u7253 : Upper (D 5) (R 5) [18,36,192,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7253
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7254 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 196 41 26 301 333 397 269), lower := (rows 19 38 196 41 26 32 64 128 256), losses := [] }

theorem u7254 : Upper (D 5) (R 5) [18,36,192,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7254
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7255 : Route 9 := (fun mask => (mask,id))

def c7255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7255 : Upper (D 5) (R 5) [18,36,192,33,12] 13 := by
  apply FastRouting.sound _ _ [18,36,192,33,12] 13 (by decide) (choices 1) [1,2,8,256] r7255 c7255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3697
  · exact u3698
  · exact u3699
  · exact u3700

def b7256 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 41 273 46 78 142 270), lower := (rows 19 38 196 41 273 32 64 128 256), losses := [] }

theorem u7256 : Upper (D 5) (R 5) [18,36,192,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7256
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7257 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 196 41 274 45 77 141 269), lower := (rows 19 38 196 41 274 32 64 128 256), losses := [] }

theorem u7257 : Upper (D 5) (R 5) [18,36,192,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7257
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7258 : Route 9 := (fun mask => (mask,id))

def c7258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7258 : Upper (D 5) (R 5) [18,36,192,33,260] 13 := by
  apply FastRouting.sound _ _ [18,36,192,33,260] 13 (by decide) (choices 1) [1,2,8] r7258 c7258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3701
  · exact u3702
  · exact u3703

def r7259 : Route 9 := (fun mask => (mask,id))

def c7259 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7259 : Upper (D 5) (R 5) [18,36,192,33,264] 13 := by
  apply FastRouting.sound _ _ [18,36,192,33,264] 13 (by decide) (choices 1) [1,2,4,8] r7259 c7259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3704
  · exact u3705
  · exact u3706
  · exact u3707

#print axioms u7259
end Delivery.IrregularNine14.P05
