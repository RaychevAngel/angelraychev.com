import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0105
import IrregularNine14P09C0106

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8580 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 138 280 372 340 468 340), lower := (rows 97 35 133 138 280 32 64 128 256), losses := [] }

theorem u8580 : Upper (D 9) (R 9) [96,33,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8580 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8581 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 138 336 316 348 412 284), lower := (rows 97 35 133 138 336 32 64 128 256), losses := [] }

theorem u8581 : Upper (D 9) (R 9) [96,33,129,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8581 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8582 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 152 274 364 332 460 332), lower := (rows 97 35 133 152 274 32 64 128 256), losses := [] }

theorem u8582 : Upper (D 9) (R 9) [96,33,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8582 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8583 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 152 276 362 330 458 330), lower := (rows 97 35 133 152 276 32 64 128 256), losses := [] }

theorem u8583 : Upper (D 9) (R 9) [96,33,129,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8583 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8584 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 152 280 358 326 454 326), lower := (rows 97 35 133 152 280 32 64 128 256), losses := [] }

theorem u8584 : Upper (D 9) (R 9) [96,33,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8584 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8585 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 152 336 302 334 398 270), lower := (rows 97 35 133 152 336 32 64 128 256), losses := [] }

theorem u8585 : Upper (D 9) (R 9) [96,33,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8585 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8586 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 200 274 316 348 412 284), lower := (rows 97 35 133 200 274 32 64 128 256), losses := [] }

theorem u8586 : Upper (D 9) (R 9) [96,33,129,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8586 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8587 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 200 276 314 346 410 282), lower := (rows 97 35 133 200 276 32 64 128 256), losses := [] }

theorem u8587 : Upper (D 9) (R 9) [96,33,129,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8587 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8588 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 200 280 310 342 406 278), lower := (rows 97 35 133 200 280 32 64 128 256), losses := [] }

theorem u8588 : Upper (D 9) (R 9) [96,33,129,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8588 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8589 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 266 276 248 216 216 472), lower := (rows 97 35 133 266 276 32 64 128 256), losses := [] }

theorem u8589 : Upper (D 9) (R 9) [96,33,129,258,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8589 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8590 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 266 336 188 220 156 412), lower := (rows 97 35 133 266 336 32 64 128 256), losses := [] }

theorem u8590 : Upper (D 9) (R 9) [96,33,129,258,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8590 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8591 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 266 400 124 92 220 348), lower := (rows 97 35 133 266 400 32 64 128 256), losses := [] }

theorem u8591 : Upper (D 9) (R 9) [96,33,129,258,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8591 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8592 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 268 336 186 218 154 410), lower := (rows 97 35 133 268 336 32 64 128 256), losses := [] }

theorem u8592 : Upper (D 9) (R 9) [96,33,129,260,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8592 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8593 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 268 400 122 90 218 346), lower := (rows 97 35 133 268 400 32 64 128 256), losses := [] }

theorem u8593 : Upper (D 9) (R 9) [96,33,129,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8593 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8594 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 328 400 62 94 158 286), lower := (rows 97 35 133 328 400 32 64 128 256), losses := [] }

theorem u8594 : Upper (D 9) (R 9) [96,33,129,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8594 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8595 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 152 276 361 329 457 329), lower := (rows 97 35 134 152 276 32 64 128 256), losses := [] }

theorem u8595 : Upper (D 9) (R 9) [96,33,130,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8595 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8596 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 152 280 357 325 453 325), lower := (rows 97 35 134 152 280 32 64 128 256), losses := [] }

theorem u8596 : Upper (D 9) (R 9) [96,33,130,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8596 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8597 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 152 336 301 333 397 269), lower := (rows 97 35 134 152 336 32 64 128 256), losses := [] }

theorem u8597 : Upper (D 9) (R 9) [96,33,130,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8597 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8598 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 200 276 313 345 409 281), lower := (rows 97 35 134 200 276 32 64 128 256), losses := [] }

theorem u8598 : Upper (D 9) (R 9) [96,33,130,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8598 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8599 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 200 280 309 341 405 277), lower := (rows 97 35 134 200 280 32 64 128 256), losses := [] }

theorem u8599 : Upper (D 9) (R 9) [96,33,130,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8599 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8600 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 268 336 185 217 153 409), lower := (rows 97 35 134 268 336 32 64 128 256), losses := [] }

theorem u8600 : Upper (D 9) (R 9) [96,33,130,260,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8600 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8601 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 268 400 121 89 217 345), lower := (rows 97 35 134 268 400 32 64 128 256), losses := [] }

theorem u8601 : Upper (D 9) (R 9) [96,33,130,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8601 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8602 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 328 400 61 93 157 285), lower := (rows 97 35 134 328 400 32 64 128 256), losses := [] }

theorem u8602 : Upper (D 9) (R 9) [96,33,130,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8602 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8603 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 140 268 208 307 339 403 275), lower := (rows 97 35 140 268 208 32 64 128 256), losses := [] }

theorem u8603 : Upper (D 9) (R 9) [96,33,136,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8603 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8604 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 140 280 208 295 327 391 263), lower := (rows 97 35 140 280 208 32 64 128 256), losses := [] }

theorem u8604 : Upper (D 9) (R 9) [96,33,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8604 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8605 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 140 328 400 55 87 151 279), lower := (rows 97 35 140 328 400 32 64 128 256), losses := [] }

theorem u8605 : Upper (D 9) (R 9) [96,33,136,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8605 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8606 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0),(1,7),(1,8),(2,7),(2,8)], upper := (rows 97 38 70 137 273 440 472 408 408), lower := (rows 97 38 70 137 273 32 64 128 256), losses := [] }

theorem u8606 : Upper (D 9) (R 9) [96,36,66,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8606 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8607 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0),(1,7),(1,8),(2,7),(2,8)], upper := (rows 97 38 70 137 280 433 465 401 401), lower := (rows 97 38 70 137 280 32 64 128 256), losses := [] }

theorem u8607 : Upper (D 9) (R 9) [96,36,66,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8607 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8608 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0),(1,7),(1,8),(2,7),(2,8)], upper := (rows 97 38 70 137 400 313 345 409 281), lower := (rows 97 38 70 137 400 32 64 128 256), losses := [] }

theorem u8608 : Upper (D 9) (R 9) [96,36,66,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8608 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8609 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0),(1,7),(1,8),(2,7),(2,8)], upper := (rows 97 38 70 152 280 417 449 385 385), lower := (rows 97 38 70 152 280 32 64 128 256), losses := [] }

theorem u8609 : Upper (D 9) (R 9) [96,36,66,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8609 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8610 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 16, targets := 352 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,8)], upper := (rows 97 38 76 137 145 306 338 402 274), lower := (rows 97 38 76 137 145 32 64 128 256), losses := [] }

theorem u8610 : Upper (D 9) (R 9) [96,36,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8610 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8611 : Route 9 := (fun mask => (mask,id))

def c8611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8611 : Upper (D 9) (R 9) [96,36,72,129,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,130] 13 (by decide) (choices 1) [1,16,256] r8611 c8611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6311
  · exact u6312
  · exact u6313

def r8612 : Route 9 := (fun mask => (mask,id))

def c8612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8612 : Upper (D 9) (R 9) [96,36,72,129,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,257] 13 (by decide) (choices 1) [2,16,128,256] r8612 c8612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6314
  · exact u6315
  · exact u6316
  · exact u6317

def r8613 : Route 9 := (fun mask => (mask,id))

def c8613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8613 : Upper (D 9) (R 9) [96,36,72,129,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,258] 13 (by decide) (choices 1) [1,16,128,256] r8613 c8613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6318
  · exact u6319
  · exact u6320
  · exact u6321

def r8614 : Route 9 := (fun mask => (mask,id))

def c8614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8614 : Upper (D 9) (R 9) [96,36,72,129,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129,384] 13 (by decide) (choices 1) [1,2,16,256] r8614 c8614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6322
  · exact u6323
  · exact u6324
  · exact u6325

def r8615 : Route 9 := (fun mask => (mask,id))

def c8615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8615 : Upper (D 9) (R 9) [96,36,72,130,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130,129] 13 (by decide) (choices 1) [1,16,256] r8615 c8615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6326
  · exact u6327
  · exact u6328

def r8616 : Route 9 := (fun mask => (mask,id))

def c8616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8616 : Upper (D 9) (R 9) [96,36,72,130,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130,257] 13 (by decide) (choices 1) [1,16,128,256] r8616 c8616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6329
  · exact u6330
  · exact u6331
  · exact u6332

def r8617 : Route 9 := (fun mask => (mask,id))

def c8617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8617 : Upper (D 9) (R 9) [96,36,72,130,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130,384] 13 (by decide) (choices 1) [1,16,256] r8617 c8617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6333
  · exact u6334
  · exact u6335

def b8618 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 38 76 152 145 291 323 387 259), lower := (rows 97 38 76 152 145 32 64 128 256), losses := [] }

theorem u8618 : Upper (D 9) (R 9) [96,36,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8618 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8619 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 38 76 152 146 289 321 385 257), lower := (rows 97 38 76 152 146 32 64 128 256), losses := [] }

theorem u8619 : Upper (D 9) (R 9) [96,36,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8619 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8620 : Route 9 := (fun mask => (mask,id))

def c8620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8620 : Upper (D 9) (R 9) [96,36,72,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,257] 13 (by decide) (choices 1) [1,2,128,256] r8620 c8620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6336
  · exact u6337
  · exact u6338
  · exact u6339

def r8621 : Route 9 := (fun mask => (mask,id))

def c8621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8621 : Upper (D 9) (R 9) [96,36,72,144,258] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144,258] 13 (by decide) (choices 1) [1,128,256] r8621 c8621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6340
  · exact u6341
  · exact u6342

def b8622 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 38 76 152 400 291 323 387 259), lower := (rows 97 38 76 152 400 32 64 128 256), losses := [] }

theorem u8622 : Upper (D 9) (R 9) [96,36,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8622 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8623 : Route 9 := (fun mask => (mask,id))

def c8623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8623 : Upper (D 9) (R 9) [96,36,72,384,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,129] 13 (by decide) (choices 1) [1,2,16,256] r8623 c8623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6343
  · exact u6344
  · exact u6345
  · exact u6346

def r8624 : Route 9 := (fun mask => (mask,id))

def c8624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8624 : Upper (D 9) (R 9) [96,36,72,384,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,130] 13 (by decide) (choices 1) [1,16,256] r8624 c8624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6347
  · exact u6348
  · exact u6349

def b8625 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 97 38 76 392 400 51 83 147 275), lower := (rows 97 38 76 392 400 32 64 128 256), losses := [] }

theorem u8625 : Upper (D 9) (R 9) [96,36,72,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8625 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8626 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 16, targets := 352 },{ cop := 4, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6),(4,8)], upper := (rows 97 38 133 88 145 298 330 394 266), lower := (rows 97 38 133 88 145 32 64 128 256), losses := [] }

theorem u8626 : Upper (D 9) (R 9) [96,36,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8626 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8627 : Route 9 := (fun mask => (mask,id))

def c8627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8627 : Upper (D 9) (R 9) [96,36,129,80,130] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,130] 13 (by decide) (choices 1) [1,8,256] r8627 c8627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6350
  · exact u6351
  · exact u6352

def r8628 : Route 9 := (fun mask => (mask,id))

def c8628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8628 : Upper (D 9) (R 9) [96,36,129,80,136] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,136] 13 (by decide) (choices 1) [1,2,256] r8628 c8628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6353
  · exact u6354
  · exact u6355

def r8629 : Route 9 := (fun mask => (mask,id))

def c8629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8629 : Upper (D 9) (R 9) [96,36,129,80,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,257] 13 (by decide) (choices 1) [2,8,128,256] r8629 c8629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6356
  · exact u6357
  · exact u6358
  · exact u6359

def r8630 : Route 9 := (fun mask => (mask,id))

def c8630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8630 : Upper (D 9) (R 9) [96,36,129,80,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,258] 13 (by decide) (choices 1) [1,8,128,256] r8630 c8630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6360
  · exact u6361
  · exact u6362
  · exact u6363

def r8631 : Route 9 := (fun mask => (mask,id))

def c8631 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8631 : Upper (D 9) (R 9) [96,36,129,80,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,264] 13 (by decide) (choices 1) [1,2,128,256] r8631 c8631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6364
  · exact u6365
  · exact u6366
  · exact u6367

def r8632 : Route 9 := (fun mask => (mask,id))

def c8632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8632 : Upper (D 9) (R 9) [96,36,129,80,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,384] 13 (by decide) (choices 1) [1,2,8,256] r8632 c8632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6368
  · exact u6369
  · exact u6370
  · exact u6371

def b8633 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 97 38 133 137 274 376 344 472 344), lower := (rows 97 38 133 137 274 32 64 128 256), losses := [] }

theorem u8633 : Upper (D 9) (R 9) [96,36,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8633 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8634 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 97 38 133 137 280 370 338 466 338), lower := (rows 97 38 133 137 280 32 64 128 256), losses := [] }

theorem u8634 : Upper (D 9) (R 9) [96,36,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8634 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8635 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 97 38 133 137 336 314 346 410 282), lower := (rows 97 38 133 137 336 32 64 128 256), losses := [] }

theorem u8635 : Upper (D 9) (R 9) [96,36,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8635 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8636 : Route 9 := (fun mask => (mask,id))

def c8636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u8636 : Upper (D 9) (R 9) [96,36,129,130,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,130,257] 13 (by decide) (choices 1) [8,16,64,256] r8636 c8636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6372
  · exact u6373
  · exact u6374
  · exact u6375

def r8637 : Route 9 := (fun mask => (mask,id))

def c8637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8637 : Upper (D 9) (R 9) [96,36,129,130,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,130,264] 13 (by decide) (choices 1) [1,16,64,256] r8637 c8637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6376
  · exact u6377
  · exact u6378
  · exact u6379

def r8638 : Route 9 := (fun mask => (mask,id))

def c8638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8638 : Upper (D 9) (R 9) [96,36,129,130,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,130,320] 13 (by decide) (choices 1) [1,8,16,256] r8638 c8638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6380
  · exact u6381
  · exact u6382
  · exact u6383

def r8639 : Route 9 := (fun mask => (mask,id))

def c8639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8639 : Upper (D 9) (R 9) [96,36,129,144,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,144,257] 13 (by decide) (choices 1) [2,8,64,256] r8639 c8639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6384
  · exact u6385
  · exact u6386
  · exact u6387

#print axioms u8639
end Delivery.IrregularNine14.P09
