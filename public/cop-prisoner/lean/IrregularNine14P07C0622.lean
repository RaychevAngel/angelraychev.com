import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0393
import IrregularNine14P07C0394
import IrregularNine14P07C0395
import IrregularNine14P07C0396

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37320 : Route 9 := (fun mask => (mask,id))

def c37320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u37320 : Upper (D 7) (R 7) [36,96,10,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,130] 13 (by decide) (choices 1) [1,64,128,256] r37320 c37320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23616
  · exact u23617
  · exact u23618
  · exact u23619

def r37321 : Route 9 := (fun mask => (mask,id))

def c37321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37321 : Upper (D 7) (R 7) [36,96,10,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,192] 13 (by decide) (choices 1) [1,2,128,256] r37321 c37321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23620
  · exact u23621
  · exact u23622
  · exact u23623

def b37322 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 14 25 273 226 194 194 450), lower := (rows 37 98 14 25 273 32 64 128 256), losses := [] }

theorem u37322 : Upper (D 7) (R 7) [36,96,10,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37323 : Route 9 := (fun mask => (mask,id))

def c37323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37323 : Upper (D 7) (R 7) [36,96,10,17,258] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,258] 13 (by decide) (choices 1) [1,64,128] r37323 c37323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23624
  · exact u23625
  · exact u23626

def r37324 : Route 9 := (fun mask => (mask,id))

def c37324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37324 : Upper (D 7) (R 7) [36,96,10,17,320] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,320] 13 (by decide) (choices 1) [1,2,128] r37324 c37324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23627
  · exact u23628
  · exact u23629

def r37325 : Route 9 := (fun mask => (mask,id))

def c37325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37325 : Upper (D 7) (R 7) [36,96,10,17,384] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,384] 13 (by decide) (choices 1) [1,2,64,128] r37325 c37325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23630
  · exact u23631
  · exact u23632
  · exact u23633

def b37326 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 88 19 417 449 385 385), lower := (rows 37 98 14 88 19 32 64 128 256), losses := [] }

theorem u37326 : Upper (D 7) (R 7) [36,96,10,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37327 : Route 9 := (fun mask => (mask,id))

def c37327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37327 : Upper (D 7) (R 7) [36,96,10,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,129] 13 (by decide) (choices 1) [1,2,128,256] r37327 c37327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23634
  · exact u23635
  · exact u23636
  · exact u23637

def r37328 : Route 9 := (fun mask => (mask,id))

def c37328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37328 : Upper (D 7) (R 7) [36,96,10,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,130] 13 (by decide) (choices 1) [1,128,256] r37328 c37328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23638
  · exact u23639
  · exact u23640

def r37329 : Route 9 := (fun mask => (mask,id))

def c37329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37329 : Upper (D 7) (R 7) [36,96,10,80,257] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,257] 13 (by decide) (choices 1) [1,2,128] r37329 c37329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23641
  · exact u23642
  · exact u23643

def r37330 : Route 9 := (fun mask => (mask,id))

def c37330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37330 : Upper (D 7) (R 7) [36,96,10,80,258] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,258] 13 (by decide) (choices 1) [1,128] r37330 c37330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23644
  · exact u23645

def r37331 : Route 9 := (fun mask => (mask,id))

def c37331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37331 : Upper (D 7) (R 7) [36,96,10,80,384] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,384] 13 (by decide) (choices 1) [1,2,128] r37331 c37331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23646
  · exact u23647
  · exact u23648

def b37332 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 456, targets := 2 }], pairs := [(1,0),(2,5),(3,1),(3,5)], upper := (rows 37 98 14 137 19 496 464 464 464), lower := (rows 37 98 14 137 19 32 64 128 256), losses := [] }

theorem u37332 : Upper (D 7) (R 7) [36,96,10,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37333 : Route 9 := (fun mask => (mask,id))

def c37333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u37333 : Upper (D 7) (R 7) [36,96,10,129,65] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,65] 13 (by decide) (choices 1) [2,16,128,256] r37333 c37333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23649
  · exact u23650
  · exact u23651
  · exact u23652

def b37334 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 14 137 82 433 465 401 401), lower := (rows 37 98 14 137 82 32 64 128 256), losses := [] }

theorem u37334 : Upper (D 7) (R 7) [36,96,10,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37335 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 98 14 137 145 370 338 466 338), lower := (rows 37 98 14 137 145 32 64 128 256), losses := [] }

theorem u37335 : Upper (D 7) (R 7) [36,96,10,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37336 : Route 9 := (fun mask => (mask,id))

def c37336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37336 : Upper (D 7) (R 7) [36,96,10,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,130] 13 (by decide) (choices 1) [1,16,64,256] r37336 c37336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23653
  · exact u23654
  · exact u23655
  · exact u23656

def r37337 : Route 9 := (fun mask => (mask,id))

def c37337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37337 : Upper (D 7) (R 7) [36,96,10,129,192] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,192] 13 (by decide) (choices 1) [1,2,16,256] r37337 c37337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23657
  · exact u23658
  · exact u23659
  · exact u23660

def r37338 : Route 9 := (fun mask => (mask,id))

def c37338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37338 : Upper (D 7) (R 7) [36,96,10,129,257] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,257] 13 (by decide) (choices 1) [2,16,64,128] r37338 c37338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23661
  · exact u23662
  · exact u23663
  · exact u23664

def r37339 : Route 9 := (fun mask => (mask,id))

def c37339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37339 : Upper (D 7) (R 7) [36,96,10,129,258] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,258] 13 (by decide) (choices 1) [1,16,64,128] r37339 c37339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23665
  · exact u23666
  · exact u23667
  · exact u23668

def r37340 : Route 9 := (fun mask => (mask,id))

def c37340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37340 : Upper (D 7) (R 7) [36,96,10,129,320] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,320] 13 (by decide) (choices 1) [1,2,16,128] r37340 c37340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23669
  · exact u23670
  · exact u23671
  · exact u23672

def r37341 : Route 9 := (fun mask => (mask,id))

def c37341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37341 : Upper (D 7) (R 7) [36,96,10,129,384] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,384] 13 (by decide) (choices 1) [1,2,16,64] r37341 c37341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23673
  · exact u23674
  · exact u23675
  · exact u23676

def b37342 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 2, region := 481, targets := 2 },{ cop := 4, region := 456, targets := 2 }], pairs := [(0,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 14 152 19 481 449 449 449), lower := (rows 37 98 14 152 19 32 64 128 256), losses := [] }

theorem u37342 : Upper (D 7) (R 7) [36,96,10,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37343 : Route 9 := (fun mask => (mask,id))

def c37343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37343 : Upper (D 7) (R 7) [36,96,10,144,65] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144,65] 13 (by decide) (choices 1) [1,2,128,256] r37343 c37343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23677
  · exact u23678
  · exact u23679
  · exact u23680

def b37344 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 14 152 82 417 449 385 385), lower := (rows 37 98 14 152 82 32 64 128 256), losses := [] }

theorem u37344 : Upper (D 7) (R 7) [36,96,10,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37345 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 14 152 145 355 323 451 323), lower := (rows 37 98 14 152 145 32 64 128 256), losses := [] }

theorem u37345 : Upper (D 7) (R 7) [36,96,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37346 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 37 98 14 152 146 353 321 449 321), lower := (rows 37 98 14 152 146 32 64 128 256), losses := [] }

theorem u37346 : Upper (D 7) (R 7) [36,96,10,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37347 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 14 152 208 291 323 387 259), lower := (rows 37 98 14 152 208 32 64 128 256), losses := [] }

theorem u37347 : Upper (D 7) (R 7) [36,96,10,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37348 : Route 9 := (fun mask => (mask,id))

def c37348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37348 : Upper (D 7) (R 7) [36,96,10,144,257] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144,257] 13 (by decide) (choices 1) [1,2,64,128] r37348 c37348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23681
  · exact u23682
  · exact u23683
  · exact u23684

def r37349 : Route 9 := (fun mask => (mask,id))

def c37349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37349 : Upper (D 7) (R 7) [36,96,10,144,258] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144,258] 13 (by decide) (choices 1) [1,64,128] r37349 c37349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23685
  · exact u23686
  · exact u23687

def r37350 : Route 9 := (fun mask => (mask,id))

def c37350 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37350 : Upper (D 7) (R 7) [36,96,10,144,320] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144,320] 13 (by decide) (choices 1) [1,2,128] r37350 c37350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23688
  · exact u23689
  · exact u23690

def b37351 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 14 152 400 99 67 195 323), lower := (rows 37 98 14 152 400 32 64 128 256), losses := [] }

theorem u37351 : Upper (D 7) (R 7) [36,96,10,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37352 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 460, targets := 32 }], pairs := [(0,6),(2,5),(3,5),(4,6)], upper := (rows 37 98 14 200 19 433 465 401 401), lower := (rows 37 98 14 200 19 32 64 128 256), losses := [] }

theorem u37352 : Upper (D 7) (R 7) [36,96,10,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37353 : Route 9 := (fun mask => (mask,id))

def c37353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37353 : Upper (D 7) (R 7) [36,96,10,192,129] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192,129] 13 (by decide) (choices 1) [1,2,16,256] r37353 c37353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23691
  · exact u23692
  · exact u23693
  · exact u23694

def r37354 : Route 9 := (fun mask => (mask,id))

def c37354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37354 : Upper (D 7) (R 7) [36,96,10,192,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192,130] 13 (by decide) (choices 1) [1,16,256] r37354 c37354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23695
  · exact u23696
  · exact u23697

def r37355 : Route 9 := (fun mask => (mask,id))

def c37355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37355 : Upper (D 7) (R 7) [36,96,10,192,257] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192,257] 13 (by decide) (choices 1) [1,2,16,128] r37355 c37355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23698
  · exact u23699
  · exact u23700
  · exact u23701

def r37356 : Route 9 := (fun mask => (mask,id))

def c37356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37356 : Upper (D 7) (R 7) [36,96,10,192,258] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192,258] 13 (by decide) (choices 1) [1,16,128] r37356 c37356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23702
  · exact u23703
  · exact u23704

def r37357 : Route 9 := (fun mask => (mask,id))

def c37357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37357 : Upper (D 7) (R 7) [36,96,10,192,384] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192,384] 13 (by decide) (choices 1) [1,2,16] r37357 c37357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23705
  · exact u23706
  · exact u23707

def b37358 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 226, targets := 1 },{ cop := 4, region := 456, targets := 2 }], pairs := [(1,0),(2,5),(3,1),(3,5)], upper := (rows 37 98 14 265 19 240 208 208 464), lower := (rows 37 98 14 265 19 32 64 128 256), losses := [] }

theorem u37358 : Upper (D 7) (R 7) [36,96,10,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37359 : Route 9 := (fun mask => (mask,id))

def c37359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37359 : Upper (D 7) (R 7) [36,96,10,257,65] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,65] 13 (by decide) (choices 1) [2,16,128] r37359 c37359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23708
  · exact u23709
  · exact u23710

def b37360 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 14 265 82 177 209 145 401), lower := (rows 37 98 14 265 82 32 64 128 256), losses := [] }

theorem u37360 : Upper (D 7) (R 7) [36,96,10,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37361 : Route 9 := (fun mask => (mask,id))

def c37361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37361 : Upper (D 7) (R 7) [36,96,10,257,129] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,129] 13 (by decide) (choices 1) [2,16,64,128] r37361 c37361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23711
  · exact u23712
  · exact u23713
  · exact u23714

def r37362 : Route 9 := (fun mask => (mask,id))

def c37362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37362 : Upper (D 7) (R 7) [36,96,10,257,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,130] 13 (by decide) (choices 1) [1,16,64,128] r37362 c37362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23715
  · exact u23716
  · exact u23717
  · exact u23718

def r37363 : Route 9 := (fun mask => (mask,id))

def c37363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37363 : Upper (D 7) (R 7) [36,96,10,257,192] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257,192] 13 (by decide) (choices 1) [1,2,16,128] r37363 c37363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23719
  · exact u23720
  · exact u23721
  · exact u23722

def b37364 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 2, region := 225, targets := 2 },{ cop := 4, region := 456, targets := 2 }], pairs := [(0,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 14 280 19 225 193 193 449), lower := (rows 37 98 14 280 19 32 64 128 256), losses := [] }

theorem u37364 : Upper (D 7) (R 7) [36,96,10,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37365 : Route 9 := (fun mask => (mask,id))

def c37365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37365 : Upper (D 7) (R 7) [36,96,10,272,65] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,65] 13 (by decide) (choices 1) [1,2,128] r37365 c37365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23723
  · exact u23724
  · exact u23725

def b37366 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 14 280 82 161 193 129 385), lower := (rows 37 98 14 280 82 32 64 128 256), losses := [] }

theorem u37366 : Upper (D 7) (R 7) [36,96,10,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37367 : Route 9 := (fun mask => (mask,id))

def c37367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37367 : Upper (D 7) (R 7) [36,96,10,272,129] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,129] 13 (by decide) (choices 1) [1,2,64,128] r37367 c37367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23726
  · exact u23727
  · exact u23728
  · exact u23729

def r37368 : Route 9 := (fun mask => (mask,id))

def c37368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37368 : Upper (D 7) (R 7) [36,96,10,272,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,130] 13 (by decide) (choices 1) [1,64,128] r37368 c37368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23730
  · exact u23731
  · exact u23732

def r37369 : Route 9 := (fun mask => (mask,id))

def c37369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37369 : Upper (D 7) (R 7) [36,96,10,272,192] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272,192] 13 (by decide) (choices 1) [1,2,128] r37369 c37369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23733
  · exact u23734
  · exact u23735

def b37370 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 460, targets := 32 }], pairs := [(0,6),(2,5),(3,5),(4,6)], upper := (rows 37 98 14 328 19 177 209 145 401), lower := (rows 37 98 14 328 19 32 64 128 256), losses := [] }

theorem u37370 : Upper (D 7) (R 7) [36,96,10,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37371 : Route 9 := (fun mask => (mask,id))

def c37371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37371 : Upper (D 7) (R 7) [36,96,10,320,129] 13 := by
  apply FastRouting.sound _ _ [36,96,10,320,129] 13 (by decide) (choices 1) [1,2,16,128] r37371 c37371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23736
  · exact u23737
  · exact u23738
  · exact u23739

def r37372 : Route 9 := (fun mask => (mask,id))

def c37372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37372 : Upper (D 7) (R 7) [36,96,10,320,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,320,130] 13 (by decide) (choices 1) [1,16,128] r37372 c37372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23740
  · exact u23741
  · exact u23742

def r37373 : Route 9 := (fun mask => (mask,id))

def c37373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37373 : Upper (D 7) (R 7) [36,96,10,384,3] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,3] 13 (by decide) (choices 1) [1,16,64,128] r37373 c37373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23743
  · exact u23744
  · exact u23745
  · exact u23746

def r37374 : Route 9 := (fun mask => (mask,id))

def c37374 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37374 : Upper (D 7) (R 7) [36,96,10,384,65] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,65] 13 (by decide) (choices 1) [1,2,16,128] r37374 c37374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23747
  · exact u23748
  · exact u23749
  · exact u23750

def b37375 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 14 392 82 177 209 145 401), lower := (rows 37 98 14 392 82 32 64 128 256), losses := [] }

theorem u37375 : Upper (D 7) (R 7) [36,96,10,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37376 : Route 9 := (fun mask => (mask,id))

def c37376 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37376 : Upper (D 7) (R 7) [36,96,10,384,129] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,129] 13 (by decide) (choices 1) [1,2,16,64] r37376 c37376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23751
  · exact u23752
  · exact u23753
  · exact u23754

def r37377 : Route 9 := (fun mask => (mask,id))

def c37377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37377 : Upper (D 7) (R 7) [36,96,10,384,130] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,130] 13 (by decide) (choices 1) [1,16,64] r37377 c37377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23755
  · exact u23756
  · exact u23757

def r37378 : Route 9 := (fun mask => (mask,id))

def c37378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37378 : Upper (D 7) (R 7) [36,96,10,384,192] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384,192] 13 (by decide) (choices 1) [1,2,16] r37378 c37378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23758
  · exact u23759
  · exact u23760

def b37379 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 28 11 19 480 448 448 448), lower := (rows 37 98 28 11 19 32 64 128 256), losses := [] }

theorem u37379 : Upper (D 7) (R 7) [36,96,24,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37379
end Delivery.IrregularNine14.P07
