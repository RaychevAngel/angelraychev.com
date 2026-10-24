import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0237
import IrregularNine14P07C0238
import IrregularNine14P07C0239

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31560 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 7 98 164 25 25 482 450 450 450), lower := (rows 7 98 164 25 25 32 64 128 256), losses := [] }

theorem u31560 : Upper (D 7) (R 7) [6,96,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31561 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 164 25 26 481 449 449 449), lower := (rows 7 98 164 25 26 32 64 128 256), losses := [] }

theorem u31561 : Upper (D 7) (R 7) [6,96,160,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31562 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 164 25 81 426 458 394 394), lower := (rows 7 98 164 25 81 32 64 128 256), losses := [] }

theorem u31562 : Upper (D 7) (R 7) [6,96,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31563 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 164 25 82 425 457 393 393), lower := (rows 7 98 164 25 82 32 64 128 256), losses := [] }

theorem u31563 : Upper (D 7) (R 7) [6,96,160,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31564 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 25 88 419 451 387 387), lower := (rows 7 98 164 25 88 32 64 128 256), losses := [] }

theorem u31564 : Upper (D 7) (R 7) [6,96,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31565 : PairBound 9 := { available := 330, camps := [{ cop := 4, region := 8, targets := 98 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 164 25 145 362 330 458 330), lower := (rows 7 98 164 25 145 32 64 128 256), losses := [] }

theorem u31565 : Upper (D 7) (R 7) [6,96,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31566 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 484, targets := 2 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(2,1),(3,5),(4,5)], upper := (rows 7 98 164 25 146 361 329 457 329), lower := (rows 7 98 164 25 146 32 64 128 256), losses := [] }

theorem u31566 : Upper (D 7) (R 7) [6,96,160,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31567 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 25 152 355 323 451 323), lower := (rows 7 98 164 25 152 32 64 128 256), losses := [] }

theorem u31567 : Upper (D 7) (R 7) [6,96,160,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31568 : Route 9 := (fun mask => (mask,id))

def c31568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31568 : Upper (D 7) (R 7) [6,96,160,17,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,192] 13 (by decide) (choices 1) [1,2,8,256] r31568 c31568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14244
  · exact u14245
  · exact u14246
  · exact u14247

def b31569 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 164 25 273 234 202 202 458), lower := (rows 7 98 164 25 273 32 64 128 256), losses := [] }

theorem u31569 : Upper (D 7) (R 7) [6,96,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31570 : Route 9 := (fun mask => (mask,id))

def c31570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31570 : Upper (D 7) (R 7) [6,96,160,17,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,258] 13 (by decide) (choices 1) [1,8,64,128] r31570 c31570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14248
  · exact u14249
  · exact u14250
  · exact u14251

def r31571 : Route 9 := (fun mask => (mask,id))

def c31571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31571 : Upper (D 7) (R 7) [6,96,160,17,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,264] 13 (by decide) (choices 1) [1,2,64,128] r31571 c31571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14252
  · exact u14253
  · exact u14254
  · exact u14255

def r31572 : Route 9 := (fun mask => (mask,id))

def c31572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31572 : Upper (D 7) (R 7) [6,96,160,17,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,320] 13 (by decide) (choices 1) [1,2,8,128] r31572 c31572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14256
  · exact u14257
  · exact u14258
  · exact u14259

def r31573 : Route 9 := (fun mask => (mask,id))

def c31573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31573 : Upper (D 7) (R 7) [6,96,160,17,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,384] 13 (by decide) (choices 1) [1,2,8,64] r31573 c31573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14260
  · exact u14261
  · exact u14262
  · exact u14263

def b31574 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 26 81 425 457 393 393), lower := (rows 7 98 164 26 81 32 64 128 256), losses := [] }

theorem u31574 : Upper (D 7) (R 7) [6,96,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31575 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 7 98 164 26 88 417 449 385 385), lower := (rows 7 98 164 26 88 32 64 128 256), losses := [] }

theorem u31575 : Upper (D 7) (R 7) [6,96,160,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31576 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,5),(3,7),(4,5)], upper := (rows 7 98 164 26 145 361 329 457 329), lower := (rows 7 98 164 26 145 32 64 128 256), losses := [] }

theorem u31576 : Upper (D 7) (R 7) [6,96,160,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31577 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 26 152 353 321 449 321), lower := (rows 7 98 164 26 152 32 64 128 256), losses := [] }

theorem u31577 : Upper (D 7) (R 7) [6,96,160,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31578 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 26 208 297 329 393 265), lower := (rows 7 98 164 26 208 32 64 128 256), losses := [] }

theorem u31578 : Upper (D 7) (R 7) [6,96,160,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31579 : Route 9 := (fun mask => (mask,id))

def c31579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31579 : Upper (D 7) (R 7) [6,96,160,18,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,257] 13 (by decide) (choices 1) [1,8,64,128] r31579 c31579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14264
  · exact u14265
  · exact u14266
  · exact u14267

def r31580 : Route 9 := (fun mask => (mask,id))

def c31580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31580 : Upper (D 7) (R 7) [6,96,160,18,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,264] 13 (by decide) (choices 1) [1,64,128] r31580 c31580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14268
  · exact u14269
  · exact u14270

def b31581 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 26 336 169 201 137 393), lower := (rows 7 98 164 26 336 32 64 128 256), losses := [] }

theorem u31581 : Upper (D 7) (R 7) [6,96,160,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31582 : Route 9 := (fun mask => (mask,id))

def c31582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31582 : Upper (D 7) (R 7) [6,96,160,18,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,384] 13 (by decide) (choices 1) [1,8,64] r31582 c31582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14271
  · exact u14272
  · exact u14273

def b31583 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,5),(3,7),(4,5)], upper := (rows 7 98 164 73 145 314 346 410 282), lower := (rows 7 98 164 73 145 32 64 128 256), losses := [] }

theorem u31583 : Upper (D 7) (R 7) [6,96,160,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31584 : Route 9 := (fun mask => (mask,id))

def c31584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31584 : Upper (D 7) (R 7) [6,96,160,65,130] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,130] 13 (by decide) (choices 1) [1,8,16,256] r31584 c31584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14274
  · exact u14275
  · exact u14276
  · exact u14277

def r31585 : Route 9 := (fun mask => (mask,id))

def c31585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31585 : Upper (D 7) (R 7) [6,96,160,65,136] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,136] 13 (by decide) (choices 1) [1,2,16,256] r31585 c31585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14278
  · exact u14279
  · exact u14280
  · exact u14281

def r31586 : Route 9 := (fun mask => (mask,id))

def c31586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31586 : Upper (D 7) (R 7) [6,96,160,65,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,257] 13 (by decide) (choices 1) [2,8,16,128] r31586 c31586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14282
  · exact u14283
  · exact u14284
  · exact u14285

def r31587 : Route 9 := (fun mask => (mask,id))

def c31587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31587 : Upper (D 7) (R 7) [6,96,160,65,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,258] 13 (by decide) (choices 1) [1,8,16,128] r31587 c31587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14286
  · exact u14287
  · exact u14288
  · exact u14289

def r31588 : Route 9 := (fun mask => (mask,id))

def c31588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31588 : Upper (D 7) (R 7) [6,96,160,65,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,264] 13 (by decide) (choices 1) [1,2,16,128] r31588 c31588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14290
  · exact u14291
  · exact u14292
  · exact u14293

def r31589 : Route 9 := (fun mask => (mask,id))

def c31589 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31589 : Upper (D 7) (R 7) [6,96,160,65,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,384] 13 (by decide) (choices 1) [1,2,8,16] r31589 c31589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14294
  · exact u14295
  · exact u14296
  · exact u14297

def b31590 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 7 98 164 74 152 305 337 401 273), lower := (rows 7 98 164 74 152 32 64 128 256), losses := [] }

theorem u31590 : Upper (D 7) (R 7) [6,96,160,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31591 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 7 98 164 74 273 185 217 153 409), lower := (rows 7 98 164 74 273 32 64 128 256), losses := [] }

theorem u31591 : Upper (D 7) (R 7) [6,96,160,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31592 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 7 98 164 74 280 177 209 145 401), lower := (rows 7 98 164 74 280 32 64 128 256), losses := [] }

theorem u31592 : Upper (D 7) (R 7) [6,96,160,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31593 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 7 98 164 74 400 57 89 153 281), lower := (rows 7 98 164 74 400 32 64 128 256), losses := [] }

theorem u31593 : Upper (D 7) (R 7) [6,96,160,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31594 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,5),(3,7),(4,5)], upper := (rows 7 98 164 88 145 299 331 395 267), lower := (rows 7 98 164 88 145 32 64 128 256), losses := [] }

theorem u31594 : Upper (D 7) (R 7) [6,96,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31595 : Route 9 := (fun mask => (mask,id))

def c31595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31595 : Upper (D 7) (R 7) [6,96,160,80,130] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,130] 13 (by decide) (choices 1) [1,8,256] r31595 c31595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14298
  · exact u14299
  · exact u14300

def b31596 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 88 152 291 323 387 259), lower := (rows 7 98 164 88 152 32 64 128 256), losses := [] }

theorem u31596 : Upper (D 7) (R 7) [6,96,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31597 : Route 9 := (fun mask => (mask,id))

def c31597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31597 : Upper (D 7) (R 7) [6,96,160,80,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,257] 13 (by decide) (choices 1) [1,2,8,128] r31597 c31597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14301
  · exact u14302
  · exact u14303
  · exact u14304

def r31598 : Route 9 := (fun mask => (mask,id))

def c31598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31598 : Upper (D 7) (R 7) [6,96,160,80,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,258] 13 (by decide) (choices 1) [1,8,128] r31598 c31598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14305
  · exact u14306
  · exact u14307

def b31599 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 88 280 163 195 131 387), lower := (rows 7 98 164 88 280 32 64 128 256), losses := [] }

theorem u31599 : Upper (D 7) (R 7) [6,96,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31600 : Route 9 := (fun mask => (mask,id))

def c31600 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31600 : Upper (D 7) (R 7) [6,96,160,80,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384] 13 (by decide) (choices 1) [1,2,8] r31600 c31600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14308
  · exact u14309
  · exact u14310

def b31601 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,7)], upper := (rows 7 98 164 137 273 122 90 218 346), lower := (rows 7 98 164 137 273 32 64 128 256), losses := [] }

theorem u31601 : Upper (D 7) (R 7) [6,96,160,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31602 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,7)], upper := (rows 7 98 164 137 274 121 89 217 345), lower := (rows 7 98 164 137 274 32 64 128 256), losses := [] }

theorem u31602 : Upper (D 7) (R 7) [6,96,160,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31603 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,7)], upper := (rows 7 98 164 137 280 115 83 211 339), lower := (rows 7 98 164 137 280 32 64 128 256), losses := [] }

theorem u31603 : Upper (D 7) (R 7) [6,96,160,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31604 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,7)], upper := (rows 7 98 164 137 336 59 91 155 283), lower := (rows 7 98 164 137 336 32 64 128 256), losses := [] }

theorem u31604 : Upper (D 7) (R 7) [6,96,160,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31605 : Route 9 := (fun mask => (mask,id))

def c31605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31605 : Upper (D 7) (R 7) [6,96,160,130,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,130,257] 13 (by decide) (choices 1) [1,8,16,64] r31605 c31605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14311
  · exact u14312
  · exact u14313
  · exact u14314

def r31606 : Route 9 := (fun mask => (mask,id))

def c31606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31606 : Upper (D 7) (R 7) [6,96,160,130,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,130,264] 13 (by decide) (choices 1) [1,16,64] r31606 c31606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14315
  · exact u14316
  · exact u14317

def r31607 : Route 9 := (fun mask => (mask,id))

def c31607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31607 : Upper (D 7) (R 7) [6,96,160,130,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,130,320] 13 (by decide) (choices 1) [1,8,16] r31607 c31607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14318
  · exact u14319
  · exact u14320

def r31608 : Route 9 := (fun mask => (mask,id))

def c31608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31608 : Upper (D 7) (R 7) [6,96,160,144,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,144,257] 13 (by decide) (choices 1) [1,2,8,64] r31608 c31608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14321
  · exact u14322
  · exact u14323
  · exact u14324

def r31609 : Route 9 := (fun mask => (mask,id))

def c31609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31609 : Upper (D 7) (R 7) [6,96,160,144,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,144,258] 13 (by decide) (choices 1) [1,8,64] r31609 c31609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14325
  · exact u14326
  · exact u14327

def b31610 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 152 280 99 67 195 323), lower := (rows 7 98 164 152 280 32 64 128 256), losses := [] }

theorem u31610 : Upper (D 7) (R 7) [6,96,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31611 : Route 9 := (fun mask => (mask,id))

def c31611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31611 : Upper (D 7) (R 7) [6,96,160,144,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,144,320] 13 (by decide) (choices 1) [1,2,8] r31611 c31611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14328
  · exact u14329
  · exact u14330

def r31612 : Route 9 := (fun mask => (mask,id))

def c31612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31612 : Upper (D 7) (R 7) [6,96,160,192,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257] 13 (by decide) (choices 1) [1,2,8,16] r31612 c31612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14331
  · exact u14332
  · exact u14333
  · exact u14334

def r31613 : Route 9 := (fun mask => (mask,id))

def c31613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31613 : Upper (D 7) (R 7) [6,96,160,192,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,258] 13 (by decide) (choices 1) [1,8,16] r31613 c31613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14335
  · exact u14336
  · exact u14337

def r31614 : Route 9 := (fun mask => (mask,id))

def c31614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31614 : Upper (D 7) (R 7) [6,96,160,192,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264] 13 (by decide) (choices 1) [1,2,16] r31614 c31614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14338
  · exact u14339
  · exact u14340

def b31615 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 261 11 56 240 208 208 464), lower := (rows 7 98 261 11 56 32 64 128 256), losses := [] }

theorem u31615 : Upper (D 7) (R 7) [6,96,257,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31616 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 261 11 152 240 240 240 496), lower := (rows 7 98 261 11 152 32 64 128 256), losses := [] }

theorem u31616 : Upper (D 7) (R 7) [6,96,257,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31617 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 261 11 176 248 216 216 472), lower := (rows 7 98 261 11 176 32 64 128 256), losses := [] }

theorem u31617 : Upper (D 7) (R 7) [6,96,257,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31618 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 261 25 26 224 224 224 480), lower := (rows 7 98 261 25 26 32 64 128 256), losses := [] }

theorem u31618 : Upper (D 7) (R 7) [6,96,257,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31619 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 261 25 50 232 200 200 456), lower := (rows 7 98 261 25 50 32 64 128 256), losses := [] }

theorem u31619 : Upper (D 7) (R 7) [6,96,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31619
end Delivery.IrregularNine14.P07
