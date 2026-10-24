import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0072
import IrregularNine14P08C0073

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13320 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 328 176 51 115 179 307), lower := (rows 97 7 140 328 176 32 64 128 256), losses := [] }

theorem u13320 : Upper (D 8) (R 8) [96,5,136,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13321 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 392 50 113 113 241 369), lower := (rows 97 7 140 392 50 32 64 128 256), losses := [] }

theorem u13321 : Upper (D 8) (R 8) [96,5,136,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13322 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 392 82 49 113 177 305), lower := (rows 97 7 140 392 82 32 64 128 256), losses := [] }

theorem u13322 : Upper (D 8) (R 8) [96,5,136,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13323 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 164 25 176 362 330 458 330), lower := (rows 97 7 164 25 176 32 64 128 256), losses := [] }

theorem u13323 : Upper (D 8) (R 8) [96,5,160,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13324 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 25 208 298 362 426 298), lower := (rows 97 7 164 25 208 32 64 128 256), losses := [] }

theorem u13324 : Upper (D 8) (R 8) [96,5,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13325 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 164 25 274 232 232 232 488), lower := (rows 97 7 164 25 274 32 64 128 256), losses := [] }

theorem u13325 : Upper (D 8) (R 8) [96,5,160,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13326 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 164 25 280 226 226 226 482), lower := (rows 97 7 164 25 280 32 64 128 256), losses := [] }

theorem u13326 : Upper (D 8) (R 8) [96,5,160,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13327 : Route 9 := (fun mask => (mask,id))

def c13327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13327 : Upper (D 8) (R 8) [96,5,160,17,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,288] 13 (by decide) (choices 1) [2,8,64,128] r13327 c13327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4321
  · exact u4322
  · exact u4323
  · exact u4324

def b13328 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 25 336 170 234 170 426), lower := (rows 97 7 164 25 336 32 64 128 256), losses := [] }

theorem u13328 : Upper (D 8) (R 8) [96,5,160,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13329 : Route 9 := (fun mask => (mask,id))

def c13329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13329 : Upper (D 8) (R 8) [96,5,160,17,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,384] 13 (by decide) (choices 1) [2,8,64] r13329 c13329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4325
  · exact u4326
  · exact u4327

def b13330 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 164 26 49 488 456 456 456), lower := (rows 97 7 164 26 49 32 64 128 256), losses := [] }

theorem u13330 : Upper (D 8) (R 8) [96,5,160,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13331 : Route 9 := (fun mask => (mask,id))

def c13331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u13331 : Upper (D 8) (R 8) [96,5,160,18,40] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,40] 13 (by decide) (choices 1) [1,64,128,256] r13331 c13331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4328
  · exact u4329
  · exact u4330
  · exact u4331

def b13332 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 26 81 424 488 424 424), lower := (rows 97 7 164 26 81 32 64 128 256), losses := [] }

theorem u13332 : Upper (D 8) (R 8) [96,5,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13333 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 26 88 417 481 417 417), lower := (rows 97 7 164 26 88 32 64 128 256), losses := [] }

theorem u13333 : Upper (D 8) (R 8) [96,5,160,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13334 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 164 26 112 425 457 393 393), lower := (rows 97 7 164 26 112 32 64 128 256), losses := [] }

theorem u13334 : Upper (D 8) (R 8) [96,5,160,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13335 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 164 26 145 360 360 488 360), lower := (rows 97 7 164 26 145 32 64 128 256), losses := [] }

theorem u13335 : Upper (D 8) (R 8) [96,5,160,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13336 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 152 353 353 481 353), lower := (rows 97 7 164 26 152 32 64 128 256), losses := [] }

theorem u13336 : Upper (D 8) (R 8) [96,5,160,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13337 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 164 26 176 361 329 457 329), lower := (rows 97 7 164 26 176 32 64 128 256), losses := [] }

theorem u13337 : Upper (D 8) (R 8) [96,5,160,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13338 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 208 297 361 425 297), lower := (rows 97 7 164 26 208 32 64 128 256), losses := [] }

theorem u13338 : Upper (D 8) (R 8) [96,5,160,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13339 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 164 26 273 232 232 232 488), lower := (rows 97 7 164 26 273 32 64 128 256), losses := [] }

theorem u13339 : Upper (D 8) (R 8) [96,5,160,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13340 : Route 9 := (fun mask => (mask,id))

def c13340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13340 : Upper (D 8) (R 8) [96,5,160,18,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,264] 13 (by decide) (choices 1) [1,64,128] r13340 c13340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4332
  · exact u4333
  · exact u4334

def r13341 : Route 9 := (fun mask => (mask,id))

def c13341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13341 : Upper (D 8) (R 8) [96,5,160,18,288] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,288] 13 (by decide) (choices 1) [1,8,64,128] r13341 c13341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4335
  · exact u4336
  · exact u4337
  · exact u4338

def r13342 : Route 9 := (fun mask => (mask,id))

def c13342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13342 : Upper (D 8) (R 8) [96,5,160,18,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18,320] 13 (by decide) (choices 1) [1,8,128] r13342 c13342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4339
  · exact u4340
  · exact u4341

def b13343 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 400 105 105 233 361), lower := (rows 97 7 164 26 400 32 64 128 256), losses := [] }

theorem u13343 : Upper (D 8) (R 8) [96,5,160,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13344 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 82 440 472 408 408), lower := (rows 97 7 164 41 82 32 64 128 256), losses := [] }

theorem u13344 : Upper (D 8) (R 8) [96,5,160,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13345 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 8, targets := 128 }], pairs := [(3,7)], upper := (rows 97 7 164 41 88 434 466 402 402), lower := (rows 97 7 164 41 88 32 64 128 256), losses := [] }

theorem u13345 : Upper (D 8) (R 8) [96,5,160,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13346 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 152 370 338 466 338), lower := (rows 97 7 164 41 152 32 64 128 256), losses := [] }

theorem u13346 : Upper (D 8) (R 8) [96,5,160,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13347 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 208 314 346 410 282), lower := (rows 97 7 164 41 208 32 64 128 256), losses := [] }

theorem u13347 : Upper (D 8) (R 8) [96,5,160,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13348 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 274 248 216 216 472), lower := (rows 97 7 164 41 274 32 64 128 256), losses := [] }

theorem u13348 : Upper (D 8) (R 8) [96,5,160,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13349 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 280 242 210 210 466), lower := (rows 97 7 164 41 280 32 64 128 256), losses := [] }

theorem u13349 : Upper (D 8) (R 8) [96,5,160,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13350 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 336 186 218 154 410), lower := (rows 97 7 164 41 336 32 64 128 256), losses := [] }

theorem u13350 : Upper (D 8) (R 8) [96,5,160,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13351 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 41 400 122 90 218 346), lower := (rows 97 7 164 41 400 32 64 128 256), losses := [] }

theorem u13351 : Upper (D 8) (R 8) [96,5,160,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13352 : PairBound 9 := { available := 408, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 42 81 440 472 408 408), lower := (rows 97 7 164 42 81 32 64 128 256), losses := [] }

theorem u13352 : Upper (D 8) (R 8) [96,5,160,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13353 : Route 9 := (fun mask => (mask,id))

def c13353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u13353 : Upper (D 8) (R 8) [96,5,160,34,72] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34,72] 13 (by decide) (choices 1) [1,16,128,256] r13353 c13353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4342
  · exact u4343
  · exact u4344
  · exact u4345

def r13354 : Route 9 := (fun mask => (mask,id))

def c13354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u13354 : Upper (D 8) (R 8) [96,5,160,34,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34,129] 13 (by decide) (choices 1) [8,16,64,256] r13354 c13354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4346
  · exact u4347
  · exact u4348
  · exact u4349

def b13355 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 42 152 369 337 465 337), lower := (rows 97 7 164 42 152 32 64 128 256), losses := [] }

theorem u13355 : Upper (D 8) (R 8) [96,5,160,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13356 : Route 9 := (fun mask => (mask,id))

def c13356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u13356 : Upper (D 8) (R 8) [96,5,160,34,192] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34,192] 13 (by decide) (choices 1) [1,8,16,256] r13356 c13356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4350
  · exact u4351
  · exact u4352
  · exact u4353

def r13357 : Route 9 := (fun mask => (mask,id))

def c13357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u13357 : Upper (D 8) (R 8) [96,5,160,34,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34,257] 13 (by decide) (choices 1) [8,16,64,128] r13357 c13357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4354
  · exact u4355
  · exact u4356
  · exact u4357

def r13358 : Route 9 := (fun mask => (mask,id))

def c13358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u13358 : Upper (D 8) (R 8) [96,5,160,34,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34,264] 13 (by decide) (choices 1) [1,16,64,128] r13358 c13358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4358
  · exact u4359
  · exact u4360
  · exact u4361

def r13359 : Route 9 := (fun mask => (mask,id))

def c13359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13359 : Upper (D 8) (R 8) [96,5,160,34,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34,320] 13 (by decide) (choices 1) [1,8,16,128] r13359 c13359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4362
  · exact u4363
  · exact u4364
  · exact u4365

def r13360 : Route 9 := (fun mask => (mask,id))

def c13360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13360 : Upper (D 8) (R 8) [96,5,160,34,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,34,384] 13 (by decide) (choices 1) [1,8,16,64] r13360 c13360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4366
  · exact u4367
  · exact u4368
  · exact u4369

def b13361 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 56 81 426 458 394 394), lower := (rows 97 7 164 56 81 32 64 128 256), losses := [] }

theorem u13361 : Upper (D 8) (R 8) [96,5,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13362 : Route 9 := (fun mask => (mask,id))

def c13362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u13362 : Upper (D 8) (R 8) [96,5,160,48,66] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,66] 13 (by decide) (choices 1) [1,8,128,256] r13362 c13362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4370
  · exact u4371
  · exact u4372
  · exact u4373

def b13363 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 56 88 419 451 387 387), lower := (rows 97 7 164 56 88 32 64 128 256), losses := [] }

theorem u13363 : Upper (D 8) (R 8) [96,5,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13364 : Route 9 := (fun mask => (mask,id))

def c13364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13364 : Upper (D 8) (R 8) [96,5,160,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,129] 13 (by decide) (choices 1) [2,8,64,256] r13364 c13364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4374
  · exact u4375
  · exact u4376
  · exact u4377

def b13365 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 146 361 329 457 329), lower := (rows 97 7 164 56 146 32 64 128 256), losses := [] }

theorem u13365 : Upper (D 8) (R 8) [96,5,160,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13366 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 164 56 152 355 323 451 323), lower := (rows 97 7 164 56 152 32 64 128 256), losses := [] }

theorem u13366 : Upper (D 8) (R 8) [96,5,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13367 : Route 9 := (fun mask => (mask,id))

def c13367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u13367 : Upper (D 8) (R 8) [96,5,160,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,192] 13 (by decide) (choices 1) [1,2,8,256] r13367 c13367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4378
  · exact u4379
  · exact u4380
  · exact u4381

def r13368 : Route 9 := (fun mask => (mask,id))

def c13368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13368 : Upper (D 8) (R 8) [96,5,160,48,257] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,257] 13 (by decide) (choices 1) [2,8,64,128] r13368 c13368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4382
  · exact u4383
  · exact u4384
  · exact u4385

def r13369 : Route 9 := (fun mask => (mask,id))

def c13369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13369 : Upper (D 8) (R 8) [96,5,160,48,258] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,258] 13 (by decide) (choices 1) [1,8,64,128] r13369 c13369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4386
  · exact u4387
  · exact u4388
  · exact u4389

def r13370 : Route 9 := (fun mask => (mask,id))

def c13370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13370 : Upper (D 8) (R 8) [96,5,160,48,264] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,264] 13 (by decide) (choices 1) [1,2,64,128] r13370 c13370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4390
  · exact u4391
  · exact u4392
  · exact u4393

def r13371 : Route 9 := (fun mask => (mask,id))

def c13371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13371 : Upper (D 8) (R 8) [96,5,160,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,320] 13 (by decide) (choices 1) [1,2,8,128] r13371 c13371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4394
  · exact u4395
  · exact u4396
  · exact u4397

def r13372 : Route 9 := (fun mask => (mask,id))

def c13372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13372 : Upper (D 8) (R 8) [96,5,160,48,384] 13 := by
  apply FastRouting.sound _ _ [96,5,160,48,384] 13 (by decide) (choices 1) [1,2,8,64] r13372 c13372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4398
  · exact u4399
  · exact u4400
  · exact u4401

def b13373 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 73 152 306 370 434 306), lower := (rows 97 7 164 73 152 32 64 128 256), losses := [] }

theorem u13373 : Upper (D 8) (R 8) [96,5,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13374 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 73 274 184 248 184 440), lower := (rows 97 7 164 73 274 32 64 128 256), losses := [] }

theorem u13374 : Upper (D 8) (R 8) [96,5,160,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13375 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 73 280 178 242 178 434), lower := (rows 97 7 164 73 280 32 64 128 256), losses := [] }

theorem u13375 : Upper (D 8) (R 8) [96,5,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13376 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 73 304 186 218 154 410), lower := (rows 97 7 164 73 304 32 64 128 256), losses := [] }

theorem u13376 : Upper (D 8) (R 8) [96,5,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13377 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 73 400 58 122 186 314), lower := (rows 97 7 164 73 400 32 64 128 256), losses := [] }

theorem u13377 : Upper (D 8) (R 8) [96,5,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13378 : Route 9 := (fun mask => (mask,id))

def c13378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u13378 : Upper (D 8) (R 8) [96,5,160,66,129] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,129] 13 (by decide) (choices 1) [8,16,256] r13378 c13378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4402
  · exact u4403
  · exact u4404

def b13379 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 74 152 305 369 433 305), lower := (rows 97 7 164 74 152 32 64 128 256), losses := [] }

theorem u13379 : Upper (D 8) (R 8) [96,5,160,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13379
end Delivery.IrregularNine14.P08
