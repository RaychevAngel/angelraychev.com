import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0039
import IrregularNine14P01C0040

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6180 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 29 98 37 138 466 498 466 466 466), lower := (rows 29 98 37 138 16 32 64 128 256), losses := [] }

theorem u6180 : Upper (D 1) (R 1) [28,96,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6181 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 29 98 37 200 402 434 466 402 402), lower := (rows 29 98 37 200 16 32 64 128 256), losses := [] }

theorem u6181 : Upper (D 1) (R 1) [28,96,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6182 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 29 98 37 266 210 242 210 210 466), lower := (rows 29 98 37 266 16 32 64 128 256), losses := [] }

theorem u6182 : Upper (D 1) (R 1) [28,96,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6183 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 29 98 37 328 146 178 210 146 402), lower := (rows 29 98 37 328 16 32 64 128 256), losses := [] }

theorem u6183 : Upper (D 1) (R 1) [28,96,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6184 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 29 98 37 392 210 242 210 210 466), lower := (rows 29 98 37 392 16 32 64 128 256), losses := [] }

theorem u6184 : Upper (D 1) (R 1) [28,96,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6185 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 137 466 498 466 466 466), lower := (rows 29 98 38 137 16 32 64 128 256), losses := [] }

theorem u6185 : Upper (D 1) (R 1) [28,96,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6186 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 138 465 497 465 465 465), lower := (rows 29 98 38 138 16 32 64 128 256), losses := [] }

theorem u6186 : Upper (D 1) (R 1) [28,96,34,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6187 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 200 403 435 467 403 403), lower := (rows 29 98 38 200 16 32 64 128 256), losses := [] }

theorem u6187 : Upper (D 1) (R 1) [28,96,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6188 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 265 210 242 210 210 466), lower := (rows 29 98 38 265 16 32 64 128 256), losses := [] }

theorem u6188 : Upper (D 1) (R 1) [28,96,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6188
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6189 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 266 209 241 209 209 465), lower := (rows 29 98 38 266 16 32 64 128 256), losses := [] }

theorem u6189 : Upper (D 1) (R 1) [28,96,34,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6190 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 328 147 179 211 147 403), lower := (rows 29 98 38 328 16 32 64 128 256), losses := [] }

theorem u6190 : Upper (D 1) (R 1) [28,96,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6191 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 38 392 211 243 211 211 467), lower := (rows 29 98 38 392 16 32 64 128 256), losses := [] }

theorem u6191 : Upper (D 1) (R 1) [28,96,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6192 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 137 466 482 450 450 450), lower := (rows 29 98 52 137 16 32 64 128 256), losses := [] }

theorem u6192 : Upper (D 1) (R 1) [28,96,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6193 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 138 467 483 451 451 451), lower := (rows 29 98 52 138 16 32 64 128 256), losses := [] }

theorem u6193 : Upper (D 1) (R 1) [28,96,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6193
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6194 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 200 403 419 451 387 387), lower := (rows 29 98 52 200 16 32 64 128 256), losses := [] }

theorem u6194 : Upper (D 1) (R 1) [28,96,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6194
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6195 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 265 210 226 194 194 450), lower := (rows 29 98 52 265 16 32 64 128 256), losses := [] }

theorem u6195 : Upper (D 1) (R 1) [28,96,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6196 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 266 211 227 195 195 451), lower := (rows 29 98 52 266 16 32 64 128 256), losses := [] }

theorem u6196 : Upper (D 1) (R 1) [28,96,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6196
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6197 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 328 147 163 195 131 387), lower := (rows 29 98 52 328 16 32 64 128 256), losses := [] }

theorem u6197 : Upper (D 1) (R 1) [28,96,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6197
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6198 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 52 392 211 227 195 195 451), lower := (rows 29 98 52 392 16 32 64 128 256), losses := [] }

theorem u6198 : Upper (D 1) (R 1) [28,96,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6198
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6199 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 100 137 402 434 466 402 402), lower := (rows 29 98 100 137 16 32 64 128 256), losses := [] }

theorem u6199 : Upper (D 1) (R 1) [28,96,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6199
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6200 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 100 138 403 435 467 403 403), lower := (rows 29 98 100 138 16 32 64 128 256), losses := [] }

theorem u6200 : Upper (D 1) (R 1) [28,96,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6200
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6201 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 100 265 146 178 210 146 402), lower := (rows 29 98 100 265 16 32 64 128 256), losses := [] }

theorem u6201 : Upper (D 1) (R 1) [28,96,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6201
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6202 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 100 266 147 179 211 147 403), lower := (rows 29 98 100 266 16 32 64 128 256), losses := [] }

theorem u6202 : Upper (D 1) (R 1) [28,96,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6203 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 100 392 147 179 211 147 403), lower := (rows 29 98 100 392 16 32 64 128 256), losses := [] }

theorem u6203 : Upper (D 1) (R 1) [28,96,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6204 : PairBound 9 := { available := 370, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 133 138 370 370 370 498 370), lower := (rows 29 98 133 138 16 32 64 128 256), losses := [] }

theorem u6204 : Upper (D 1) (R 1) [28,96,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6205 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 5, targets := 2 }], pairs := [(0,1)], upper := (rows 29 98 133 152 370 354 354 482 354), lower := (rows 29 98 133 152 16 32 64 128 256), losses := [] }

theorem u6205 : Upper (D 1) (R 1) [28,96,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6206 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 133 168 338 370 338 466 338), lower := (rows 29 98 133 168 16 32 64 128 256), losses := [] }

theorem u6206 : Upper (D 1) (R 1) [28,96,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6207 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6207 : Upper (D 1) (R 1) [28,96,129,258] 13 := by
  apply FastRouting.sound _ _ [28,96,129,258] 13 (by decide) (choices 1) [2,32,128] r6207 c6207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2398
  · exact u2399
  · exact u2400

def b6208 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 133 280 242 226 226 226 482), lower := (rows 29 98 133 280 16 32 64 128 256), losses := [] }

theorem u6208 : Upper (D 1) (R 1) [28,96,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6209 : Route 9 := (fun mask => (mask,id))

def c6209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6209 : Upper (D 1) (R 1) [28,96,129,288] 13 := by
  apply FastRouting.sound _ _ [28,96,129,288] 13 (by decide) (choices 1) [2,64,128] r6209 c6209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2401
  · exact u2402
  · exact u2403

def b6210 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 133 392 114 114 114 242 370), lower := (rows 29 98 133 392 16 32 64 128 256), losses := [] }

theorem u6210 : Upper (D 1) (R 1) [28,96,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6210
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6211 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 98 134 138 369 369 369 497 369), lower := (rows 29 98 134 138 16 32 64 128 256), losses := [] }

theorem u6211 : Upper (D 1) (R 1) [28,96,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6212 : PairBound 9 := { available := 355, camps := [{ cop := 0, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 134 152 371 355 355 483 355), lower := (rows 29 98 134 152 16 32 64 128 256), losses := [] }

theorem u6212 : Upper (D 1) (R 1) [28,96,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6212
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6213 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 168 339 371 339 467 339), lower := (rows 29 98 134 168 16 32 64 128 256), losses := [] }

theorem u6213 : Upper (D 1) (R 1) [28,96,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6213
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6214 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6214 : Upper (D 1) (R 1) [28,96,130,257] 13 := by
  apply FastRouting.sound _ _ [28,96,130,257] 13 (by decide) (choices 1) [2,32,128] r6214 c6214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2404
  · exact u2405
  · exact u2406

def r6215 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6215 : Upper (D 1) (R 1) [28,96,130,258] 13 := by
  apply FastRouting.sound _ _ [28,96,130,258] 13 (by decide) (choices 1) [1,32,128] r6215 c6215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2407
  · exact u2408
  · exact u2409

def b6216 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 134 280 243 227 227 227 483), lower := (rows 29 98 134 280 16 32 64 128 256), losses := [] }

theorem u6216 : Upper (D 1) (R 1) [28,96,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6217 : Route 9 := (fun mask => (mask,id))

def c6217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6217 : Upper (D 1) (R 1) [28,96,130,288] 13 := by
  apply FastRouting.sound _ _ [28,96,130,288] 13 (by decide) (choices 1) [1,2,64,128] r6217 c6217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2410
  · exact u2411
  · exact u2412
  · exact u2413

def b6218 : PairBound 9 := { available := 115, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 392 115 115 115 243 371), lower := (rows 29 98 134 392 16 32 64 128 256), losses := [] }

theorem u6218 : Upper (D 1) (R 1) [28,96,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6218
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6219 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 148 168 339 355 323 451 323), lower := (rows 29 98 148 168 16 32 64 128 256), losses := [] }

theorem u6219 : Upper (D 1) (R 1) [28,96,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6219
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6220 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 148 265 242 226 226 226 482), lower := (rows 29 98 148 265 16 32 64 128 256), losses := [] }

theorem u6220 : Upper (D 1) (R 1) [28,96,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6220
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6221 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 148 266 243 227 227 227 483), lower := (rows 29 98 148 266 16 32 64 128 256), losses := [] }

theorem u6221 : Upper (D 1) (R 1) [28,96,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6222 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 148 296 211 227 195 195 451), lower := (rows 29 98 148 296 16 32 64 128 256), losses := [] }

theorem u6222 : Upper (D 1) (R 1) [28,96,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6222
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6223 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 148 392 115 99 99 227 355), lower := (rows 29 98 148 392 16 32 64 128 256), losses := [] }

theorem u6223 : Upper (D 1) (R 1) [28,96,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6223
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6224 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 164 200 275 307 339 403 275), lower := (rows 29 98 164 200 16 32 64 128 256), losses := [] }

theorem u6224 : Upper (D 1) (R 1) [28,96,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6224
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6225 : Route 9 := (fun mask => (mask,id))

def c6225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6225 : Upper (D 1) (R 1) [28,96,160,257] 13 := by
  apply FastRouting.sound _ _ [28,96,160,257] 13 (by decide) (choices 1) [2,64,128] r6225 c6225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2414
  · exact u2415
  · exact u2416

def r6226 : Route 9 := (fun mask => (mask,id))

def c6226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6226 : Upper (D 1) (R 1) [28,96,160,258] 13 := by
  apply FastRouting.sound _ _ [28,96,160,258] 13 (by decide) (choices 1) [1,2,64,128] r6226 c6226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2417
  · exact u2418
  · exact u2419
  · exact u2420

def b6227 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 164 280 211 227 195 195 451), lower := (rows 29 98 164 280 16 32 64 128 256), losses := [] }

theorem u6227 : Upper (D 1) (R 1) [28,96,160,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6227
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6228 : Route 9 := (fun mask => (mask,id))

def c6228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6228 : Upper (D 1) (R 1) [28,96,160,320] 13 := by
  apply FastRouting.sound _ _ [28,96,160,320] 13 (by decide) (choices 1) [1,2,128] r6228 c6228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2421
  · exact u2422
  · exact u2423

def b6229 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 164 392 83 115 83 211 339), lower := (rows 29 98 164 392 16 32 64 128 256), losses := [] }

theorem u6229 : Upper (D 1) (R 1) [28,96,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6230 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 22 42 240 224 224 224 480), lower := (rows 29 259 22 42 16 32 64 128 256), losses := [] }

theorem u6230 : Upper (D 1) (R 1) [28,257,18,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6230
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6231 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 22 104 242 226 226 226 482), lower := (rows 29 259 22 104 16 32 64 128 256), losses := [] }

theorem u6231 : Upper (D 1) (R 1) [28,257,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6232 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 259 38 42 208 240 208 208 464), lower := (rows 29 259 38 42 16 32 64 128 256), losses := [] }

theorem u6232 : Upper (D 1) (R 1) [28,257,34,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6233 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 38 56 210 226 194 194 450), lower := (rows 29 259 38 56 16 32 64 128 256), losses := [] }

theorem u6233 : Upper (D 1) (R 1) [28,257,34,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6233
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m6234_64 : Upper (D 1) (R 1) [28,257,34,66,64] 13 :=
  permutation_upper _ _ _ [28,257,34,66,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2424

def r6234 : Route 9 := (fun mask => (mask,id))

def c6234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6234 : Upper (D 1) (R 1) [28,257,34,66] 13 := by
  apply FastRouting.sound _ _ [28,257,34,66] 13 (by decide) (choices 1) [32,64,128] r6234 c6234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2424
  · exact m6234_64
  · exact u2425

def b6235 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 38 88 242 226 226 226 482), lower := (rows 29 259 38 88 16 32 64 128 256), losses := [] }

theorem u6235 : Upper (D 1) (R 1) [28,257,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6236 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 259 38 104 210 242 210 210 466), lower := (rows 29 259 38 104 16 32 64 128 256), losses := [] }

theorem u6236 : Upper (D 1) (R 1) [28,257,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6236
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6237 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6237 : Upper (D 1) (R 1) [28,257,34,192] 13 := by
  apply FastRouting.sound _ _ [28,257,34,192] 13 (by decide) (choices 1) [2,32,64] r6237 c6237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2426
  · exact u2427
  · exact u2428

def b6238 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 52 104 210 226 194 194 450), lower := (rows 29 259 52 104 16 32 64 128 256), losses := [] }

theorem u6238 : Upper (D 1) (R 1) [28,257,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6239 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 259 52 200 242 226 226 226 482), lower := (rows 29 259 52 200 16 32 64 128 256), losses := [] }

theorem u6239 : Upper (D 1) (R 1) [28,257,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6239
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6239
end Delivery.IrregularNine14.P01
