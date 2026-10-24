import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0040

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6240 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 29 259 100 104 146 178 210 146 402), lower := (rows 29 259 100 104 16 32 64 128 256), losses := [] }

theorem u6240 : Upper (D 1) (R 1) [28,257,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6241 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 259 100 168 210 242 210 210 466), lower := (rows 29 259 100 168 16 32 64 128 256), losses := [] }

theorem u6241 : Upper (D 1) (R 1) [28,257,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6242 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 29 274 7 42 240 224 224 224 480), lower := (rows 29 274 7 42 16 32 64 128 256), losses := [] }

theorem u6242 : Upper (D 1) (R 1) [28,272,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6243 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 29 274 7 104 242 226 226 226 482), lower := (rows 29 274 7 104 16 32 64 128 256), losses := [] }

theorem u6243 : Upper (D 1) (R 1) [28,272,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6244 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 274 37 42 210 226 194 194 450), lower := (rows 29 274 37 42 16 32 64 128 256), losses := [] }

theorem u6244 : Upper (D 1) (R 1) [28,272,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6245 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 29 274 37 74 242 226 226 226 482), lower := (rows 29 274 37 74 16 32 64 128 256), losses := [] }

theorem u6245 : Upper (D 1) (R 1) [28,272,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6245
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6246 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 274 37 104 210 226 194 194 450), lower := (rows 29 274 37 104 16 32 64 128 256), losses := [] }

theorem u6246 : Upper (D 1) (R 1) [28,272,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6246
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6247 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 29 274 37 200 242 226 226 226 482), lower := (rows 29 274 37 200 16 32 64 128 256), losses := [] }

theorem u6247 : Upper (D 1) (R 1) [28,272,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6248 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 274 38 42 209 225 193 193 449), lower := (rows 29 274 38 42 16 32 64 128 256), losses := [] }

theorem u6248 : Upper (D 1) (R 1) [28,272,34,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6248
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m6249_64 : Upper (D 1) (R 1) [28,272,34,66,64] 13 :=
  permutation_upper _ _ _ [28,272,34,66,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2430

def r6249 : Route 9 := (fun mask => (mask,id))

def c6249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6249 : Upper (D 1) (R 1) [28,272,34,66] 13 := by
  apply FastRouting.sound _ _ [28,272,34,66] 13 (by decide) (choices 1) [1,32,64,128] r6249 c6249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2429
  · exact u2430
  · exact m6249_64
  · exact u2431

def b6250 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 274 38 104 211 227 195 195 451), lower := (rows 29 274 38 104 16 32 64 128 256), losses := [] }

theorem u6250 : Upper (D 1) (R 1) [28,272,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6251 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6251 : Upper (D 1) (R 1) [28,272,34,192] 13 := by
  apply FastRouting.sound _ _ [28,272,34,192] 13 (by decide) (choices 1) [1,2,32,64] r6251 c6251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2432
  · exact u2433
  · exact u2434
  · exact u2435

def b6252 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 29 274 100 104 147 163 195 131 387), lower := (rows 29 274 100 104 16 32 64 128 256), losses := [] }

theorem u6252 : Upper (D 1) (R 1) [28,272,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6253 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 29 274 100 168 211 227 195 195 451), lower := (rows 29 274 100 168 16 32 64 128 256), losses := [] }

theorem u6253 : Upper (D 1) (R 1) [28,272,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6254 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 5, targets := 32 }], pairs := [(0,5)], upper := (rows 29 290 7 26 240 224 224 224 480), lower := (rows 29 290 7 26 16 32 64 128 256), losses := [] }

theorem u6254 : Upper (D 1) (R 1) [28,288,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6255 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 290 7 42 208 240 208 208 464), lower := (rows 29 290 7 42 16 32 64 128 256), losses := [] }

theorem u6255 : Upper (D 1) (R 1) [28,288,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6255
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6256 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 7 56 210 226 194 194 450), lower := (rows 29 290 7 56 16 32 64 128 256), losses := [] }

theorem u6256 : Upper (D 1) (R 1) [28,288,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6256
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6257 : Route 9 := (fun mask => (mask,id))

def c6257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6257 : Upper (D 1) (R 1) [28,288,3,66] 13 := by
  apply FastRouting.sound _ _ [28,288,3,66] 13 (by decide) (choices 1) [32,64,128] r6257 c6257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2436
  · exact u2437
  · exact u2438

def b6258 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 7 88 242 226 226 226 482), lower := (rows 29 290 7 88 16 32 64 128 256), losses := [] }

theorem u6258 : Upper (D 1) (R 1) [28,288,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6258
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6259 : Route 9 := (fun mask => (mask,id))

def c6259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6259 : Upper (D 1) (R 1) [28,288,3,96] 13 := by
  apply FastRouting.sound _ _ [28,288,3,96] 13 (by decide) (choices 1) [2,64,128] r6259 c6259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2439
  · exact u2440
  · exact u2441

def r6260 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6260 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6260 : Upper (D 1) (R 1) [28,288,3,192] 13 := by
  apply FastRouting.sound _ _ [28,288,3,192] 13 (by decide) (choices 1) [2,32,64] r6260 c6260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2442
  · exact u2443
  · exact u2444

def b6261 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 290 21 74 242 226 226 226 482), lower := (rows 29 290 21 74 16 32 64 128 256), losses := [] }

theorem u6261 : Upper (D 1) (R 1) [28,288,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6261
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6262 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 290 21 104 210 226 194 194 450), lower := (rows 29 290 21 104 16 32 64 128 256), losses := [] }

theorem u6262 : Upper (D 1) (R 1) [28,288,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6263 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 29 290 21 200 242 226 226 226 482), lower := (rows 29 290 21 200 16 32 64 128 256), losses := [] }

theorem u6263 : Upper (D 1) (R 1) [28,288,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6264 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 22 73 242 226 226 226 482), lower := (rows 29 290 22 73 16 32 64 128 256), losses := [] }

theorem u6264 : Upper (D 1) (R 1) [28,288,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6265 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 22 74 241 225 225 225 481), lower := (rows 29 290 22 74 16 32 64 128 256), losses := [] }

theorem u6265 : Upper (D 1) (R 1) [28,288,18,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6266 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 22 104 211 227 195 195 451), lower := (rows 29 290 22 104 16 32 64 128 256), losses := [] }

theorem u6266 : Upper (D 1) (R 1) [28,288,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6266
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6267 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 22 200 243 227 227 227 483), lower := (rows 29 290 22 200 16 32 64 128 256), losses := [] }

theorem u6267 : Upper (D 1) (R 1) [28,288,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6267
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6268 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 29 290 37 74 210 242 210 210 466), lower := (rows 29 290 37 74 16 32 64 128 256), losses := [] }

theorem u6268 : Upper (D 1) (R 1) [28,288,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6268
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6269 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 29 290 37 200 210 242 210 210 466), lower := (rows 29 290 37 200 16 32 64 128 256), losses := [] }

theorem u6269 : Upper (D 1) (R 1) [28,288,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6270 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 290 38 73 210 242 210 210 466), lower := (rows 29 290 38 73 16 32 64 128 256), losses := [] }

theorem u6270 : Upper (D 1) (R 1) [28,288,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6270
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6271 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 290 38 74 209 241 209 209 465), lower := (rows 29 290 38 74 16 32 64 128 256), losses := [] }

theorem u6271 : Upper (D 1) (R 1) [28,288,34,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6272 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 29 290 38 200 211 243 211 211 467), lower := (rows 29 290 38 200 16 32 64 128 256), losses := [] }

theorem u6272 : Upper (D 1) (R 1) [28,288,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6273 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 52 73 210 226 194 194 450), lower := (rows 29 290 52 73 16 32 64 128 256), losses := [] }

theorem u6273 : Upper (D 1) (R 1) [28,288,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6273
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6274 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 52 74 211 227 195 195 451), lower := (rows 29 290 52 74 16 32 64 128 256), losses := [] }

theorem u6274 : Upper (D 1) (R 1) [28,288,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6275 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 52 200 211 227 195 195 451), lower := (rows 29 290 52 200 16 32 64 128 256), losses := [] }

theorem u6275 : Upper (D 1) (R 1) [28,288,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6276 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 69 74 178 178 242 178 434), lower := (rows 29 290 69 74 16 32 64 128 256), losses := [] }

theorem u6276 : Upper (D 1) (R 1) [28,288,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6277 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 5, targets := 2 }], pairs := [(0,1)], upper := (rows 29 290 69 88 178 162 226 162 418), lower := (rows 29 290 69 88 16 32 64 128 256), losses := [] }

theorem u6277 : Upper (D 1) (R 1) [28,288,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6278 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 69 104 146 178 210 146 402), lower := (rows 29 290 69 104 16 32 64 128 256), losses := [] }

theorem u6278 : Upper (D 1) (R 1) [28,288,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6279 : Route 9 := (fun mask => (mask,id))

def c6279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6279 : Upper (D 1) (R 1) [28,288,65,130] 13 := by
  apply FastRouting.sound _ _ [28,288,65,130] 13 (by decide) (choices 1) [2,32,64,128] r6279 c6279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2445
  · exact u2446
  · exact u2447
  · exact u2448

def b6280 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 69 152 242 226 226 226 482), lower := (rows 29 290 69 152 16 32 64 128 256), losses := [] }

theorem u6280 : Upper (D 1) (R 1) [28,288,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6281 : Route 9 := (fun mask => (mask,id))

def c6281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6281 : Upper (D 1) (R 1) [28,288,65,160] 13 := by
  apply FastRouting.sound _ _ [28,288,65,160] 13 (by decide) (choices 1) [2,64,128] r6281 c6281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2449
  · exact u2450
  · exact u2451

def b6282 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 69 200 178 178 242 178 434), lower := (rows 29 290 69 200 16 32 64 128 256), losses := [] }

theorem u6282 : Upper (D 1) (R 1) [28,288,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6283 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 29 290 70 74 177 177 241 177 433), lower := (rows 29 290 70 74 16 32 64 128 256), losses := [] }

theorem u6283 : Upper (D 1) (R 1) [28,288,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6284 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 70 88 179 163 227 163 419), lower := (rows 29 290 70 88 16 32 64 128 256), losses := [] }

theorem u6284 : Upper (D 1) (R 1) [28,288,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6285 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 70 104 147 179 211 147 403), lower := (rows 29 290 70 104 16 32 64 128 256), losses := [] }

theorem u6285 : Upper (D 1) (R 1) [28,288,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6285
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m6286_128 : Upper (D 1) (R 1) [28,288,66,130,128] 13 :=
  permutation_upper _ _ _ [28,288,66,130,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2454

def r6286 : Route 9 := (fun mask => (mask,id))

def c6286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6286 : Upper (D 1) (R 1) [28,288,66,130] 13 := by
  apply FastRouting.sound _ _ [28,288,66,130] 13 (by decide) (choices 1) [1,32,64,128] r6286 c6286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2452
  · exact u2453
  · exact u2454
  · exact m6286_128

def b6287 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 70 152 243 227 227 227 483), lower := (rows 29 290 70 152 16 32 64 128 256), losses := [] }

theorem u6287 : Upper (D 1) (R 1) [28,288,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6287
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6288 : Route 9 := (fun mask => (mask,id))

def c6288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6288 : Upper (D 1) (R 1) [28,288,66,160] 13 := by
  apply FastRouting.sound _ _ [28,288,66,160] 13 (by decide) (choices 1) [1,2,64,128] r6288 c6288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2455
  · exact u2456
  · exact u2457
  · exact u2458

def b6289 : PairBound 9 := { available := 179, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 70 200 179 179 243 179 435), lower := (rows 29 290 70 200 16 32 64 128 256), losses := [] }

theorem u6289 : Upper (D 1) (R 1) [28,288,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6289
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6290 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 84 104 147 163 195 131 387), lower := (rows 29 290 84 104 16 32 64 128 256), losses := [] }

theorem u6290 : Upper (D 1) (R 1) [28,288,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6290
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6291 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 84 168 211 227 195 195 451), lower := (rows 29 290 84 168 16 32 64 128 256), losses := [] }

theorem u6291 : Upper (D 1) (R 1) [28,288,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6292 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 84 200 179 163 227 163 419), lower := (rows 29 290 84 200 16 32 64 128 256), losses := [] }

theorem u6292 : Upper (D 1) (R 1) [28,288,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6293 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 100 200 147 179 211 147 403), lower := (rows 29 290 100 200 16 32 64 128 256), losses := [] }

theorem u6293 : Upper (D 1) (R 1) [28,288,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6294 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 29 290 196 200 51 51 115 179 307), lower := (rows 29 290 196 200 16 32 64 128 256), losses := [] }

theorem u6294 : Upper (D 1) (R 1) [28,288,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6294
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6295 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 76 26 496 480 480 480 480), lower := (rows 51 7 76 26 16 32 64 128 256), losses := [] }

theorem u6295 : Upper (D 1) (R 1) [50,5,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6296 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 76 56 466 482 450 450 450), lower := (rows 51 7 76 56 16 32 64 128 256), losses := [] }

theorem u6296 : Upper (D 1) (R 1) [50,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6296
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6297 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 7 76 74 432 432 496 432 432), lower := (rows 51 7 76 74 16 32 64 128 256), losses := [] }

theorem u6297 : Upper (D 1) (R 1) [50,5,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6297
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6298 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 88 434 418 482 418 418), lower := (rows 51 7 76 88 16 32 64 128 256), losses := [] }

theorem u6298 : Upper (D 1) (R 1) [50,5,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6298
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6299 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 138 496 496 496 496 496), lower := (rows 51 7 76 138 16 32 64 128 256), losses := [] }

theorem u6299 : Upper (D 1) (R 1) [50,5,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6299
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6299
end Delivery.IrregularNine14.P01
