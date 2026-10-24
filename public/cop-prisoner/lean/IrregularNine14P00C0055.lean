import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0035
import IrregularNine14P00C0036

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3300 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 305 14 52 74 209 225 193 193 449), lower := (rows 305 14 52 74 16 32 64 128 256), losses := [] }

theorem u3300 : Upper (D 0) (R 0) [304,12,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3300
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3301 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 305 14 52 200 211 227 195 195 451), lower := (rows 305 14 52 200 16 32 64 128 256), losses := [] }

theorem u3301 : Upper (D 0) (R 0) [304,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3301
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 69 73 178 178 242 178 434), lower := (rows 305 14 69 73 16 32 64 128 256), losses := [] }

theorem u3302 : Upper (D 0) (R 0) [304,12,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3302
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3303 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 305 14 69 74 177 177 241 177 433), lower := (rows 305 14 69 74 16 32 64 128 256), losses := [] }

theorem u3303 : Upper (D 0) (R 0) [304,12,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3303
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3304 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 69 88 179 163 227 163 419), lower := (rows 305 14 69 88 16 32 64 128 256), losses := [] }

theorem u3304 : Upper (D 0) (R 0) [304,12,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3304
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3305_128 : Upper (D 0) (R 0) [304,12,65,129,128] 13 :=
  permutation_upper _ _ _ [304,12,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2125

def r3305 : Route 9 := (fun mask => (mask,id))

def c3305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3305 : Upper (D 0) (R 0) [304,12,65,129] 13 := by
  apply FastRouting.sound _ _ [304,12,65,129] 13 (by decide) (choices 1) [2,32,64,128] r3305 c3305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2123
  · exact u2124
  · exact u2125
  · exact m3305_128

def r3306 : Route 9 := (fun mask => (mask,id))

def c3306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3306 : Upper (D 0) (R 0) [304,12,65,130] 13 := by
  apply FastRouting.sound _ _ [304,12,65,130] 13 (by decide) (choices 1) [1,32,64,128] r3306 c3306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2126
  · exact u2127
  · exact u2128
  · exact u2129

def r3307 : Route 9 := (fun mask => (mask,id))

def c3307 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3307 : Upper (D 0) (R 0) [304,12,65,144] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144] 13 (by decide) (choices 1) [1,2,32,64,128] r3307 c3307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2130
  · exact u2131
  · exact u2132
  · exact u2133
  · exact u2134

def b3308 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 69 200 179 179 243 179 435), lower := (rows 305 14 69 200 16 32 64 128 256), losses := [] }

theorem u3308 : Upper (D 0) (R 0) [304,12,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3308
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3309 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 305 14 70 88 177 161 225 161 417), lower := (rows 305 14 70 88 16 32 64 128 256), losses := [] }

theorem u3309 : Upper (D 0) (R 0) [304,12,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3309
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3310 : Route 9 := (fun mask => (mask,id))

def c3310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3310 : Upper (D 0) (R 0) [304,12,66,144] 13 := by
  apply FastRouting.sound _ _ [304,12,66,144] 13 (by decide) (choices 1) [1,32,64,128] r3310 c3310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2135
  · exact u2136
  · exact u2137
  · exact u2138

def b3311 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 305 14 70 200 177 177 241 177 433), lower := (rows 305 14 70 200 16 32 64 128 256), losses := [] }

theorem u3311 : Upper (D 0) (R 0) [304,12,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3311
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3312 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 84 104 147 163 195 131 387), lower := (rows 305 14 84 104 16 32 64 128 256), losses := [] }

theorem u3312 : Upper (D 0) (R 0) [304,12,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3312
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3313 : Route 9 := (fun mask => (mask,id))

def c3313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3313 : Upper (D 0) (R 0) [304,12,80,160] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160] 13 (by decide) (choices 1) [1,2,64,128] r3313 c3313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2139
  · exact u2140
  · exact u2141
  · exact u2142

def b3314 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 84 200 179 163 227 163 419), lower := (rows 305 14 84 200 16 32 64 128 256), losses := [] }

theorem u3314 : Upper (D 0) (R 0) [304,12,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3314
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 305 14 196 200 51 51 115 179 307), lower := (rows 305 14 196 200 16 32 64 128 256), losses := [] }

theorem u3315 : Upper (D 0) (R 0) [304,12,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3315
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 19 38 73 220 236 204 204 460), lower := (rows 305 19 38 73 16 32 64 128 256), losses := [] }

theorem u3316 : Upper (D 0) (R 0) [304,17,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3316
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3317 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 19 38 76 217 233 201 201 457), lower := (rows 305 19 38 76 16 32 64 128 256), losses := [] }

theorem u3317 : Upper (D 0) (R 0) [304,17,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3317
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3318 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 19 38 200 221 237 205 205 461), lower := (rows 305 19 38 200 16 32 64 128 256), losses := [] }

theorem u3318 : Upper (D 0) (R 0) [304,17,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3318
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3319 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 44 73 214 230 198 198 454), lower := (rows 305 19 44 73 16 32 64 128 256), losses := [] }

theorem u3319 : Upper (D 0) (R 0) [304,17,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3319
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3320 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 44 74 213 229 197 197 453), lower := (rows 305 19 44 74 16 32 64 128 256), losses := [] }

theorem u3320 : Upper (D 0) (R 0) [304,17,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3320
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3321 : PairBound 9 := { available := 199, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 44 200 215 231 199 199 455), lower := (rows 305 19 44 200 16 32 64 128 256), losses := [] }

theorem u3321 : Upper (D 0) (R 0) [304,17,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3321
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3322 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 69 74 188 172 236 172 428), lower := (rows 305 19 69 74 16 32 64 128 256), losses := [] }

theorem u3322 : Upper (D 0) (R 0) [304,17,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3322
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 69 104 158 174 206 142 398), lower := (rows 305 19 69 104 16 32 64 128 256), losses := [] }

theorem u3323 : Upper (D 0) (R 0) [304,17,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3323
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3324 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 69 138 252 236 236 236 492), lower := (rows 305 19 69 138 16 32 64 128 256), losses := [] }

theorem u3324 : Upper (D 0) (R 0) [304,17,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3324
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3325 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 69 140 250 234 234 234 490), lower := (rows 305 19 69 140 16 32 64 128 256), losses := [] }

theorem u3325 : Upper (D 0) (R 0) [304,17,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3325
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3326 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 69 168 222 238 206 206 462), lower := (rows 305 19 69 168 16 32 64 128 256), losses := [] }

theorem u3326 : Upper (D 0) (R 0) [304,17,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3326
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3327 : PairBound 9 := { available := 174, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 69 200 190 174 238 174 430), lower := (rows 305 19 69 200 16 32 64 128 256), losses := [] }

theorem u3327 : Upper (D 0) (R 0) [304,17,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3327
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3328 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 70 104 157 173 205 141 397), lower := (rows 305 19 70 104 16 32 64 128 256), losses := [] }

theorem u3328 : Upper (D 0) (R 0) [304,17,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3328
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3329 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 70 140 249 233 233 233 489), lower := (rows 305 19 70 140 16 32 64 128 256), losses := [] }

theorem u3329 : Upper (D 0) (R 0) [304,17,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3329
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3330 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 70 168 221 237 205 205 461), lower := (rows 305 19 70 168 16 32 64 128 256), losses := [] }

theorem u3330 : Upper (D 0) (R 0) [304,17,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3330
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 173, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 70 200 189 173 237 173 429), lower := (rows 305 19 70 200 16 32 64 128 256), losses := [] }

theorem u3331 : Upper (D 0) (R 0) [304,17,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3331
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3332 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 76 140 243 227 227 227 483), lower := (rows 305 19 76 140 16 32 64 128 256), losses := [] }

theorem u3332 : Upper (D 0) (R 0) [304,17,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3332
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3333 : PairBound 9 := { available := 199, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 76 168 215 231 199 199 455), lower := (rows 305 19 76 168 16 32 64 128 256), losses := [] }

theorem u3333 : Upper (D 0) (R 0) [304,17,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3333
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3334 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 100 200 159 175 207 143 399), lower := (rows 305 19 100 200 16 32 64 128 256), losses := [] }

theorem u3334 : Upper (D 0) (R 0) [304,17,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3334
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3335 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 22 38 73 217 233 201 201 457), lower := (rows 305 22 38 73 16 32 64 128 256), losses := [] }

theorem u3335 : Upper (D 0) (R 0) [304,20,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3335
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3336 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 22 38 200 217 233 201 201 457), lower := (rows 305 22 38 200 16 32 64 128 256), losses := [] }

theorem u3336 : Upper (D 0) (R 0) [304,20,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3336
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3337 : Route 9 := (fun mask => (mask,id))

def c3337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3337 : Upper (D 0) (R 0) [304,20,40,65] 13 := by
  apply FastRouting.sound _ _ [304,20,40,65] 13 (by decide) (choices 1) [1,2,64,128] r3337 c3337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2143
  · exact u2144
  · exact u2145
  · exact u2146

def r3338 : Route 9 := (fun mask => (mask,id))

def c3338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3338 : Upper (D 0) (R 0) [304,20,40,66] 13 := by
  apply FastRouting.sound _ _ [304,20,40,66] 13 (by decide) (choices 1) [1,64,128] r3338 c3338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2147
  · exact u2148
  · exact u2149

def r3339 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3339 : Upper (D 0) (R 0) [304,20,40,192] 13 := by
  apply FastRouting.sound _ _ [304,20,40,192] 13 (by decide) (choices 1) [1,2,64] r3339 c3339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2150
  · exact u2151
  · exact u2152

def b3340 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 69 73 186 170 234 170 426), lower := (rows 305 22 69 73 16 32 64 128 256), losses := [] }

theorem u3340 : Upper (D 0) (R 0) [304,20,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3340
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 69 74 185 169 233 169 425), lower := (rows 305 22 69 74 16 32 64 128 256), losses := [] }

theorem u3341 : Upper (D 0) (R 0) [304,20,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3341
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3342 : Route 9 := (fun mask => (mask,id))

def c3342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3342 : Upper (D 0) (R 0) [304,20,65,96] 13 := by
  apply FastRouting.sound _ _ [304,20,65,96] 13 (by decide) (choices 1) [1,2,8,128] r3342 c3342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2153
  · exact u2154
  · exact u2155
  · exact u2156

def r3343 : Route 9 := (fun mask => (mask,id))

def c3343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u3343 : Upper (D 0) (R 0) [304,20,65,129] 13 := by
  apply FastRouting.sound _ _ [304,20,65,129] 13 (by decide) (choices 1) [2,8,32,64,128] r3343 c3343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2157
  · exact u2158
  · exact u2159
  · exact u2160
  · exact u2161

def r3344 : Route 9 := (fun mask => (mask,id))

def c3344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3344 : Upper (D 0) (R 0) [304,20,65,130] 13 := by
  apply FastRouting.sound _ _ [304,20,65,130] 13 (by decide) (choices 1) [1,8,32,64,128] r3344 c3344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2162
  · exact u2163
  · exact u2164
  · exact u2165
  · exact u2166

def r3345 : Route 9 := (fun mask => (mask,id))

def c3345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3345 : Upper (D 0) (R 0) [304,20,65,160] 13 := by
  apply FastRouting.sound _ _ [304,20,65,160] 13 (by decide) (choices 1) [1,2,8,64,128] r3345 c3345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2167
  · exact u2168
  · exact u2169
  · exact u2170
  · exact u2171

def r3346 : Route 9 := (fun mask => (mask,id))

def c3346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3346 : Upper (D 0) (R 0) [304,20,65,192] 13 := by
  apply FastRouting.sound _ _ [304,20,65,192] 13 (by decide) (choices 1) [1,2,8,32,128] r3346 c3346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2172
  · exact u2173
  · exact u2174
  · exact u2175
  · exact u2176

def b3347 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 70 73 185 169 233 169 425), lower := (rows 305 22 70 73 16 32 64 128 256), losses := [] }

theorem u3347 : Upper (D 0) (R 0) [304,20,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3347
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3348 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 70 104 153 169 201 137 393), lower := (rows 305 22 70 104 16 32 64 128 256), losses := [] }

theorem u3348 : Upper (D 0) (R 0) [304,20,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3348
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3349 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 70 137 249 233 233 233 489), lower := (rows 305 22 70 137 16 32 64 128 256), losses := [] }

theorem u3349 : Upper (D 0) (R 0) [304,20,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3349
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3350 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 70 168 217 233 201 201 457), lower := (rows 305 22 70 168 16 32 64 128 256), losses := [] }

theorem u3350 : Upper (D 0) (R 0) [304,20,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3350
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3351 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 70 200 185 169 233 169 425), lower := (rows 305 22 70 200 16 32 64 128 256), losses := [] }

theorem u3351 : Upper (D 0) (R 0) [304,20,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3351
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3352 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 76 73 179 163 227 163 419), lower := (rows 305 22 76 73 16 32 64 128 256), losses := [] }

theorem u3352 : Upper (D 0) (R 0) [304,20,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3352
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 76 74 177 161 225 161 417), lower := (rows 305 22 76 74 16 32 64 128 256), losses := [] }

theorem u3353 : Upper (D 0) (R 0) [304,20,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3353
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3354 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 76 104 147 163 195 131 387), lower := (rows 305 22 76 104 16 32 64 128 256), losses := [] }

theorem u3354 : Upper (D 0) (R 0) [304,20,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3354
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3355 : Route 9 := (fun mask => (mask,id))

def c3355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3355 : Upper (D 0) (R 0) [304,20,72,129] 13 := by
  apply FastRouting.sound _ _ [304,20,72,129] 13 (by decide) (choices 1) [1,2,32,64,128] r3355 c3355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2177
  · exact u2178
  · exact u2179
  · exact u2180
  · exact u2181

def r3356 : Route 9 := (fun mask => (mask,id))

def c3356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3356 : Upper (D 0) (R 0) [304,20,72,130] 13 := by
  apply FastRouting.sound _ _ [304,20,72,130] 13 (by decide) (choices 1) [1,32,64,128] r3356 c3356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2182
  · exact u2183
  · exact u2184
  · exact u2185

def r3357 : Route 9 := (fun mask => (mask,id))

def c3357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3357 : Upper (D 0) (R 0) [304,20,72,160] 13 := by
  apply FastRouting.sound _ _ [304,20,72,160] 13 (by decide) (choices 1) [1,2,64,128] r3357 c3357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2186
  · exact u2187
  · exact u2188
  · exact u2189

def b3358 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 76 200 179 163 227 163 419), lower := (rows 305 22 76 200 16 32 64 128 256), losses := [] }

theorem u3358 : Upper (D 0) (R 0) [304,20,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3358
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3359 : Route 9 := (fun mask => (mask,id))

def c3359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3359 : Upper (D 0) (R 0) [304,20,96,65] 13 := by
  apply FastRouting.sound _ _ [304,20,96,65] 13 (by decide) (choices 1) [1,2,8,128] r3359 c3359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2190
  · exact u2191
  · exact u2192
  · exact u2193

#print axioms u3359
end Delivery.IrregularNine14.P00
