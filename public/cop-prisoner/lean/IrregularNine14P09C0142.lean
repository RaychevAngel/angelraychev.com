import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0104
import IrregularNine14P09C0105

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8520 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 14 148 168 81 291 323 387 259), lower := (rows 97 14 148 168 81 32 64 128 256), losses := [] }

theorem u8520 : Upper (D 9) (R 9) [96,12,144,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8521 : Route 9 := (fun mask => (mask,id))

def c8521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8521 : Upper (D 9) (R 9) [96,12,144,160,66] 13 := by
  apply FastRouting.sound _ _ [96,12,144,160,66] 13 (by decide) (choices 1) [1,256] r8521 c8521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6247
  · exact u6248

def r8522 : Route 9 := (fun mask => (mask,id))

def c8522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8522 : Upper (D 9) (R 9) [96,12,144,160,257] 13 := by
  apply FastRouting.sound _ _ [96,12,144,160,257] 13 (by decide) (choices 1) [1,2,64,256] r8522 c8522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6249
  · exact u6250
  · exact u6251
  · exact u6252

def r8523 : Route 9 := (fun mask => (mask,id))

def c8523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8523 : Upper (D 9) (R 9) [96,12,144,160,258] 13 := by
  apply FastRouting.sound _ _ [96,12,144,160,258] 13 (by decide) (choices 1) [1,64,256] r8523 c8523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6253
  · exact u6254
  · exact u6255

def r8524 : Route 9 := (fun mask => (mask,id))

def c8524 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8524 : Upper (D 9) (R 9) [96,12,144,160,320] 13 := by
  apply FastRouting.sound _ _ [96,12,144,160,320] 13 (by decide) (choices 1) [1,2,256] r8524 c8524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6256
  · exact u6257
  · exact u6258

def b8525 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 14 148 296 81 419 451 387 387), lower := (rows 97 14 148 296 81 32 64 128 256), losses := [] }

theorem u8525 : Upper (D 9) (R 9) [96,12,144,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8526 : Route 9 := (fun mask => (mask,id))

def c8526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8526 : Upper (D 9) (R 9) [96,12,144,288,66] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,66] 13 (by decide) (choices 1) [1,128,256] r8526 c8526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6259
  · exact u6260
  · exact u6261

def b8527 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 4, targets := 353 },{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 14 148 296 145 355 323 451 323), lower := (rows 97 14 148 296 145 32 64 128 256), losses := [] }

theorem u8527 : Upper (D 9) (R 9) [96,12,144,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8527 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8528 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 4, targets := 353 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 14 148 296 146 353 321 449 321), lower := (rows 97 14 148 296 146 32 64 128 256), losses := [] }

theorem u8528 : Upper (D 9) (R 9) [96,12,144,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8528 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8529 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 4, targets := 353 },{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 14 148 296 208 291 323 387 259), lower := (rows 97 14 148 296 208 32 64 128 256), losses := [] }

theorem u8529 : Upper (D 9) (R 9) [96,12,144,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8529 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8530 : Route 9 := (fun mask => (mask,id))

def c8530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8530 : Upper (D 9) (R 9) [96,12,144,288,257] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,257] 13 (by decide) (choices 1) [1,2,64,128] r8530 c8530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6262
  · exact u6263
  · exact u6264
  · exact u6265

def r8531 : Route 9 := (fun mask => (mask,id))

def c8531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8531 : Upper (D 9) (R 9) [96,12,144,288,258] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,258] 13 (by decide) (choices 1) [1,64,128] r8531 c8531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6266
  · exact u6267
  · exact u6268

def r8532 : Route 9 := (fun mask => (mask,id))

def c8532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8532 : Upper (D 9) (R 9) [96,12,144,288,320] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,320] 13 (by decide) (choices 1) [1,2,128] r8532 c8532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6269
  · exact u6270
  · exact u6271

def b8533 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 353 },{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 14 148 296 400 99 67 195 323), lower := (rows 97 14 148 296 400 32 64 128 256), losses := [] }

theorem u8533 : Upper (D 9) (R 9) [96,12,144,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8533 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8534 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 14 148 392 49 355 323 451 323), lower := (rows 97 14 148 392 49 32 64 128 256), losses := [] }

theorem u8534 : Upper (D 9) (R 9) [96,12,144,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8534 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8535 : Route 9 := (fun mask => (mask,id))

def c8535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8535 : Upper (D 9) (R 9) [96,12,144,384,34] 13 := by
  apply FastRouting.sound _ _ [96,12,144,384,34] 13 (by decide) (choices 1) [1,64,256] r8535 c8535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6272
  · exact u6273
  · exact u6274

def b8536 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 14 148 392 112 291 323 387 259), lower := (rows 97 14 148 392 112 32 64 128 256), losses := [] }

theorem u8536 : Upper (D 9) (R 9) [96,12,144,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8536 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8537 : Route 9 := (fun mask => (mask,id))

def c8537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8537 : Upper (D 9) (R 9) [96,12,144,384,257] 13 := by
  apply FastRouting.sound _ _ [96,12,144,384,257] 13 (by decide) (choices 1) [1,2,64] r8537 c8537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6275
  · exact u6276
  · exact u6277

def b8538 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 22, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(2,0),(2,5)], upper := (rows 97 14 148 392 274 97 97 225 353), lower := (rows 97 14 148 392 274 32 64 128 256), losses := [] }

theorem u8538 : Upper (D 9) (R 9) [96,12,144,384,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8538 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8539 : Route 9 := (fun mask => (mask,id))

def c8539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8539 : Upper (D 9) (R 9) [96,12,144,384,288] 13 := by
  apply FastRouting.sound _ _ [96,12,144,384,288] 13 (by decide) (choices 1) [1,2,64] r8539 c8539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6278
  · exact u6279
  · exact u6280

def r8540 : Route 9 := (fun mask => (mask,id))

def c8540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8540 : Upper (D 9) (R 9) [96,12,160,192,257] 13 := by
  apply FastRouting.sound _ _ [96,12,160,192,257] 13 (by decide) (choices 1) [1,2,16,256] r8540 c8540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6281
  · exact u6282
  · exact u6283
  · exact u6284

def r8541 : Route 9 := (fun mask => (mask,id))

def c8541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8541 : Upper (D 9) (R 9) [96,12,160,192,258] 13 := by
  apply FastRouting.sound _ _ [96,12,160,192,258] 13 (by decide) (choices 1) [1,16,256] r8541 c8541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6285
  · exact u6286
  · exact u6287

def r8542 : Route 9 := (fun mask => (mask,id))

def c8542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8542 : Upper (D 9) (R 9) [96,12,160,320,129] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,129] 13 (by decide) (choices 1) [1,2,16,256] r8542 c8542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6288
  · exact u6289
  · exact u6290
  · exact u6291

def r8543 : Route 9 := (fun mask => (mask,id))

def c8543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8543 : Upper (D 9) (R 9) [96,12,160,320,130] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,130] 13 (by decide) (choices 1) [1,16,256] r8543 c8543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6292
  · exact u6293
  · exact u6294

def r8544 : Route 9 := (fun mask => (mask,id))

def c8544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8544 : Upper (D 9) (R 9) [96,12,160,320,384] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,384] 13 (by decide) (choices 1) [1,2,16] r8544 c8544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6295
  · exact u6296
  · exact u6297

def b8545 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 14 164 392 81 307 339 403 275), lower := (rows 97 14 164 392 81 32 64 128 256), losses := [] }

theorem u8545 : Upper (D 9) (R 9) [96,12,160,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8545 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8546 : Route 9 := (fun mask => (mask,id))

def c8546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8546 : Upper (D 9) (R 9) [96,12,160,384,66] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,66] 13 (by decide) (choices 1) [1,16,256] r8546 c8546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6298
  · exact u6299
  · exact u6300

def r8547 : Route 9 := (fun mask => (mask,id))

def c8547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8547 : Upper (D 9) (R 9) [96,12,160,384,257] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,257] 13 (by decide) (choices 1) [1,2,16,64] r8547 c8547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6301
  · exact u6302
  · exact u6303
  · exact u6304

def r8548 : Route 9 := (fun mask => (mask,id))

def c8548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8548 : Upper (D 9) (R 9) [96,12,160,384,258] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,258] 13 (by decide) (choices 1) [1,16,64] r8548 c8548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6305
  · exact u6306
  · exact u6307

def r8549 : Route 9 := (fun mask => (mask,id))

def c8549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8549 : Upper (D 9) (R 9) [96,12,160,384,320] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,320] 13 (by decide) (choices 1) [1,2,16] r8549 c8549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6308
  · exact u6309
  · exact u6310

def b8550 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 10, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(3,0),(3,5)], upper := (rows 97 14 388 392 50 113 81 209 337), lower := (rows 97 14 388 392 50 32 64 128 256), losses := [] }

theorem u8550 : Upper (D 9) (R 9) [96,12,384,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8550 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8551 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 137 148 312 344 408 280), lower := (rows 97 35 70 137 148 32 64 128 256), losses := [] }

theorem u8551 : Upper (D 9) (R 9) [96,33,66,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8551 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8552 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 137 276 440 472 408 408), lower := (rows 97 35 70 137 276 32 64 128 256), losses := [] }

theorem u8552 : Upper (D 9) (R 9) [96,33,66,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8552 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8553 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 137 280 436 468 404 404), lower := (rows 97 35 70 137 280 32 64 128 256), losses := [] }

theorem u8553 : Upper (D 9) (R 9) [96,33,66,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8553 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8554 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 137 400 316 348 412 284), lower := (rows 97 35 70 137 400 32 64 128 256), losses := [] }

theorem u8554 : Upper (D 9) (R 9) [96,33,66,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8554 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8555 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 140 280 433 465 401 401), lower := (rows 97 35 70 140 280 32 64 128 256), losses := [] }

theorem u8555 : Upper (D 9) (R 9) [96,33,66,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8555 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8556 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 140 400 313 345 409 281), lower := (rows 97 35 70 140 400 32 64 128 256), losses := [] }

theorem u8556 : Upper (D 9) (R 9) [96,33,66,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8556 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8557 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 152 280 421 453 389 389), lower := (rows 97 35 70 152 280 32 64 128 256), losses := [] }

theorem u8557 : Upper (D 9) (R 9) [96,33,66,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8557 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8558 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 137 146 308 340 404 276), lower := (rows 97 35 76 137 146 32 64 128 256), losses := [] }

theorem u8558 : Upper (D 9) (R 9) [96,33,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8558 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8559 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 137 148 306 338 402 274), lower := (rows 97 35 76 137 148 32 64 128 256), losses := [] }

theorem u8559 : Upper (D 9) (R 9) [96,33,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8559 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8560 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 137 274 436 468 404 404), lower := (rows 97 35 76 137 274 32 64 128 256), losses := [] }

theorem u8560 : Upper (D 9) (R 9) [96,33,72,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8560 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8561 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 137 276 434 466 402 402), lower := (rows 97 35 76 137 276 32 64 128 256), losses := [] }

theorem u8561 : Upper (D 9) (R 9) [96,33,72,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8561 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8562 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 137 400 310 342 406 278), lower := (rows 97 35 76 137 400 32 64 128 256), losses := [] }

theorem u8562 : Upper (D 9) (R 9) [96,33,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8562 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8563 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 138 145 308 340 404 276), lower := (rows 97 35 76 138 145 32 64 128 256), losses := [] }

theorem u8563 : Upper (D 9) (R 9) [96,33,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8563 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8564 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 138 148 305 337 401 273), lower := (rows 97 35 76 138 148 32 64 128 256), losses := [] }

theorem u8564 : Upper (D 9) (R 9) [96,33,72,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8564 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8565 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 138 273 436 468 404 404), lower := (rows 97 35 76 138 273 32 64 128 256), losses := [] }

theorem u8565 : Upper (D 9) (R 9) [96,33,72,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8565 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8566 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 138 276 433 465 401 401), lower := (rows 97 35 76 138 276 32 64 128 256), losses := [] }

theorem u8566 : Upper (D 9) (R 9) [96,33,72,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8566 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8567 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 138 400 309 341 405 277), lower := (rows 97 35 76 138 400 32 64 128 256), losses := [] }

theorem u8567 : Upper (D 9) (R 9) [96,33,72,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8567 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8568 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 476, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5),(4,6)], upper := (rows 97 35 76 140 145 306 338 402 274), lower := (rows 97 35 76 140 145 32 64 128 256), losses := [] }

theorem u8568 : Upper (D 9) (R 9) [96,33,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8568 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8569 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 476, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5),(4,6)], upper := (rows 97 35 76 140 146 305 337 401 273), lower := (rows 97 35 76 140 146 32 64 128 256), losses := [] }

theorem u8569 : Upper (D 9) (R 9) [96,33,72,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8569 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8570 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 476, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5),(4,6)], upper := (rows 97 35 76 140 273 434 466 402 402), lower := (rows 97 35 76 140 273 32 64 128 256), losses := [] }

theorem u8570 : Upper (D 9) (R 9) [96,33,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8570 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8571 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 476, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5),(4,6)], upper := (rows 97 35 76 140 274 433 465 401 401), lower := (rows 97 35 76 140 274 32 64 128 256), losses := [] }

theorem u8571 : Upper (D 9) (R 9) [96,33,72,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8571 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8572 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 476, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5),(4,6)], upper := (rows 97 35 76 140 400 307 339 403 275), lower := (rows 97 35 76 140 400 32 64 128 256), losses := [] }

theorem u8572 : Upper (D 9) (R 9) [96,33,72,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8572 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8573 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 152 273 422 454 390 390), lower := (rows 97 35 76 152 273 32 64 128 256), losses := [] }

theorem u8573 : Upper (D 9) (R 9) [96,33,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8573 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8574 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 152 274 421 453 389 389), lower := (rows 97 35 76 152 274 32 64 128 256), losses := [] }

theorem u8574 : Upper (D 9) (R 9) [96,33,72,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8574 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8575 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 476, targets := 32 },{ cop := 0, region := 2, targets := 384 }], pairs := [(1,7),(1,8),(2,5),(3,5),(4,5)], upper := (rows 97 35 76 152 276 419 451 387 387), lower := (rows 97 35 76 152 276 32 64 128 256), losses := [] }

theorem u8575 : Upper (D 9) (R 9) [96,33,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8575 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8576 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 392 145 310 342 406 278), lower := (rows 97 35 76 392 145 32 64 128 256), losses := [] }

theorem u8576 : Upper (D 9) (R 9) [96,33,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8576 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8577 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 392 146 309 341 405 277), lower := (rows 97 35 76 392 146 32 64 128 256), losses := [] }

theorem u8577 : Upper (D 9) (R 9) [96,33,72,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8577 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8578 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 392 148 307 339 403 275), lower := (rows 97 35 76 392 148 32 64 128 256), losses := [] }

theorem u8578 : Upper (D 9) (R 9) [96,33,72,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8578 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8579 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 138 276 376 344 472 344), lower := (rows 97 35 133 138 276 32 64 128 256), losses := [] }

theorem u8579 : Upper (D 9) (R 9) [96,33,129,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8579 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8579
end Delivery.IrregularNine14.P09
