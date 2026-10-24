import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0177
import IrregularNine14P07C0178

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r28380 : Route 9 := (fun mask => (mask,id))

def c28380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28380 : Upper (D 7) (R 7) [96,257,9,18,160,4] 13 := by
  apply FastRouting.sound _ _ [96,257,9,18,160,4] 13 (by decide) (choices 1) [2,128] r28380 c28380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10670
  · exact u10671

def b28381 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 26 176 96 198 134 390), lower := (rows 97 259 13 26 176 96 64 128 256), losses := [] }

theorem u28381 : Upper (D 7) (R 7) [96,257,9,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28382 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 259 13 26 176 160 70 198 326), lower := (rows 97 259 13 26 176 160 64 128 256), losses := [] }

theorem u28382 : Upper (D 7) (R 7) [96,257,9,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28383 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 60, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 13 28 50 34 192 192 448), lower := (rows 97 259 13 28 50 34 64 128 256), losses := [] }

theorem u28383 : Upper (D 7) (R 7) [96,257,9,20,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28384 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 28 50 96 194 130 386), lower := (rows 97 259 13 28 50 96 64 128 256), losses := [] }

theorem u28384 : Upper (D 7) (R 7) [96,257,9,20,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28385 : Route 9 := (fun mask => (mask,id))

def c28385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28385 : Upper (D 7) (R 7) [96,257,9,20,34,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,20,34,128] 13 (by decide) (choices 1) [2,128] r28385 c28385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10672
  · exact u10673

def r28386 : Route 9 := (fun mask => (mask,id))

def c28386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u28386 : Upper (D 7) (R 7) [96,257,9,20,130,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,20,130,2] 13 (by decide) (choices 1) [32,128] r28386 c28386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10674
  · exact u10675

def b28387 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 28 146 96 226 162 418), lower := (rows 97 259 13 28 146 96 64 128 256), losses := [] }

theorem u28387 : Upper (D 7) (R 7) [96,257,9,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28388_2 : Upper (D 7) (R 7) [96,257,9,20,130,128,2] 13 :=
  permutation_upper _ _ _ [96,257,9,20,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10675

theorem m28388_32 : Upper (D 7) (R 7) [96,257,9,20,130,128,32] 13 :=
  permutation_upper _ _ _ [96,257,9,20,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10676

def r28388 : Route 9 := (fun mask => (mask,id))

def c28388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28388 : Upper (D 7) (R 7) [96,257,9,20,130,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,20,130,128] 13 (by decide) (choices 1) [2,32] r28388 c28388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28388_2
  · exact m28388_32

def r28389 : Route 9 := (fun mask => (mask,id))

def c28389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28389 : Upper (D 7) (R 7) [96,257,9,20,160,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,20,160,2] 13 (by decide) (choices 1) [2,128] r28389 c28389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10677
  · exact u10678

def b28390 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 28 176 96 194 130 386), lower := (rows 97 259 13 28 176 96 64 128 256), losses := [] }

theorem u28390 : Upper (D 7) (R 7) [96,257,9,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28391 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 259 13 28 176 160 66 194 322), lower := (rows 97 259 13 28 176 160 64 128 256), losses := [] }

theorem u28391 : Upper (D 7) (R 7) [96,257,9,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28392 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6)], upper := (rows 97 259 13 42 82 36 208 144 400), lower := (rows 97 259 13 42 82 36 64 128 256), losses := [] }

theorem u28392 : Upper (D 7) (R 7) [96,257,9,34,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28392 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28393 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 42 82 48 196 132 388), lower := (rows 97 259 13 42 82 48 64 128 256), losses := [] }

theorem u28393 : Upper (D 7) (R 7) [96,257,9,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28393 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28394 : Route 9 := (fun mask => (mask,id))

def c28394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28394 : Upper (D 7) (R 7) [96,257,9,34,66,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,66,128] 13 (by decide) (choices 1) [4,16,128] r28394 c28394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10679
  · exact u10680
  · exact u10681

def b28395 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 13 42 84 34 208 144 400), lower := (rows 97 259 13 42 84 34 64 128 256), losses := [] }

theorem u28395 : Upper (D 7) (R 7) [96,257,9,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28396 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 42 84 48 194 130 386), lower := (rows 97 259 13 42 84 48 64 128 256), losses := [] }

theorem u28396 : Upper (D 7) (R 7) [96,257,9,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28396 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28397 : Route 9 := (fun mask => (mask,id))

def c28397 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28397 : Upper (D 7) (R 7) [96,257,9,34,68,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,68,128] 13 (by decide) (choices 1) [2,16,128] r28397 c28397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10682
  · exact u10683
  · exact u10684

def b28398 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6)], upper := (rows 97 259 13 42 146 36 208 208 464), lower := (rows 97 259 13 42 146 36 64 128 256), losses := [] }

theorem u28398 : Upper (D 7) (R 7) [96,257,9,34,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28398 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28399 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 259 13 42 146 48 196 196 452), lower := (rows 97 259 13 42 146 48 64 128 256), losses := [] }

theorem u28399 : Upper (D 7) (R 7) [96,257,9,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28399 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28400 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 42 146 96 212 148 404), lower := (rows 97 259 13 42 146 96 64 128 256), losses := [] }

theorem u28400 : Upper (D 7) (R 7) [96,257,9,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28401 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 97 259 13 42 146 160 84 212 340), lower := (rows 97 259 13 42 146 160 64 128 256), losses := [] }

theorem u28401 : Upper (D 7) (R 7) [96,257,9,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28402 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 13 42 148 34 208 208 464), lower := (rows 97 259 13 42 148 34 64 128 256), losses := [] }

theorem u28402 : Upper (D 7) (R 7) [96,257,9,34,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28403 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,0),(4,5)], upper := (rows 97 259 13 42 148 48 194 194 450), lower := (rows 97 259 13 42 148 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 52 74 138 266), good := (rows 96 450 508 490 180 48 64 128 256) }] }

theorem u28403 : Upper (D 7) (R 7) [96,257,9,34,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28403 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28404 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 42 148 96 210 146 402), lower := (rows 97 259 13 42 148 96 64 128 256), losses := [] }

theorem u28404 : Upper (D 7) (R 7) [96,257,9,34,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28405 : Route 9 := (fun mask => (mask,id))

def c28405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28405 : Upper (D 7) (R 7) [96,257,9,34,132,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,132,128] 13 (by decide) (choices 1) [2,16] r28405 c28405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10685
  · exact u10686

def b28406 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 13 42 208 34 212 148 404), lower := (rows 97 259 13 42 208 34 64 128 256), losses := [] }

theorem u28406 : Upper (D 7) (R 7) [96,257,9,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28407 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 44, targets := 192 }], pairs := [(2,6),(2,7),(3,6)], upper := (rows 97 259 13 42 208 36 210 146 402), lower := (rows 97 259 13 42 208 36 64 128 256), losses := [] }

theorem u28407 : Upper (D 7) (R 7) [96,257,9,34,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28407 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28408 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 42 208 48 198 134 390), lower := (rows 97 259 13 42 208 48 64 128 256), losses := [] }

theorem u28408 : Upper (D 7) (R 7) [96,257,9,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28409 : Route 9 := (fun mask => (mask,id))

def c28409 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28409 : Upper (D 7) (R 7) [96,257,9,34,192,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,192,128] 13 (by decide) (choices 1) [2,4,16] r28409 c28409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10687
  · exact u10688
  · exact u10689

def b28410 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 60, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 13 56 22 34 192 192 448), lower := (rows 97 259 13 56 22 34 64 128 256), losses := [] }

theorem u28410 : Upper (D 7) (R 7) [96,257,9,48,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28411 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 56 22 96 194 130 386), lower := (rows 97 259 13 56 22 96 64 128 256), losses := [] }

theorem u28411 : Upper (D 7) (R 7) [96,257,9,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28412 : Route 9 := (fun mask => (mask,id))

def c28412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28412 : Upper (D 7) (R 7) [96,257,9,48,6,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,6,128] 13 (by decide) (choices 1) [2,128] r28412 c28412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10690
  · exact u10691

def b28413 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 97 259 13 56 82 34 196 132 388), lower := (rows 97 259 13 56 82 34 64 128 256), losses := [] }

theorem u28413 : Upper (D 7) (R 7) [96,257,9,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28414 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 56 82 36 194 130 386), lower := (rows 97 259 13 56 82 36 64 128 256), losses := [] }

theorem u28414 : Upper (D 7) (R 7) [96,257,9,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28414 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28415 : Route 9 := (fun mask => (mask,id))

def c28415 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28415 : Upper (D 7) (R 7) [96,257,9,48,66,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,66,128] 13 (by decide) (choices 1) [2,4,128] r28415 c28415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10692
  · exact u10693
  · exact u10694

def b28416 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 97 259 13 56 146 34 196 196 452), lower := (rows 97 259 13 56 146 34 64 128 256), losses := [] }

theorem u28416 : Upper (D 7) (R 7) [96,257,9,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28417 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 1, region := 208, targets := 1 }], pairs := [(1,5),(4,0),(4,5)], upper := (rows 97 259 13 56 146 36 194 194 450), lower := (rows 97 259 13 56 146 36 64 128 256), losses := [] }

theorem u28417 : Upper (D 7) (R 7) [96,257,9,48,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28417 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28418 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 56 146 96 198 134 390), lower := (rows 97 259 13 56 146 96 64 128 256), losses := [] }

theorem u28418 : Upper (D 7) (R 7) [96,257,9,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28419 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 259 13 56 146 160 70 198 326), lower := (rows 97 259 13 56 146 160 64 128 256), losses := [] }

theorem u28419 : Upper (D 7) (R 7) [96,257,9,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28420 : Route 9 := (fun mask => (mask,id))

def c28420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28420 : Upper (D 7) (R 7) [96,257,9,48,132,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,132,2] 13 (by decide) (choices 1) [2,128] r28420 c28420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10695
  · exact u10696

def b28421 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 56 148 96 194 130 386), lower := (rows 97 259 13 56 148 96 64 128 256), losses := [] }

theorem u28421 : Upper (D 7) (R 7) [96,257,9,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28422 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 259 13 56 148 160 66 194 322), lower := (rows 97 259 13 56 148 160 64 128 256), losses := [] }

theorem u28422 : Upper (D 7) (R 7) [96,257,9,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28423 : Route 9 := (fun mask => (mask,id))

def c28423 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28423 : Upper (D 7) (R 7) [96,257,9,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,192,2] 13 (by decide) (choices 1) [2,4,128] r28423 c28423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10697
  · exact u10698
  · exact u10699

def b28424 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 56 208 36 194 130 386), lower := (rows 97 259 13 56 208 36 64 128 256), losses := [] }

theorem u28424 : Upper (D 7) (R 7) [96,257,9,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28424 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28425 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 97 259 13 56 208 160 70 134 262), lower := (rows 97 259 13 56 208 160 64 128 256), losses := [] }

theorem u28425 : Upper (D 7) (R 7) [96,257,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28426 : Route 9 := (fun mask => (mask,id))

def c28426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u28426 : Upper (D 7) (R 7) [96,257,9,130,6,16] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,6,16] 13 (by decide) (choices 1) [32,128] r28426 c28426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10700
  · exact u10701

def b28427 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 138 22 96 240 176 432), lower := (rows 97 259 13 138 22 96 64 128 256), losses := [] }

theorem u28427 : Upper (D 7) (R 7) [96,257,9,130,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28428_16 : Upper (D 7) (R 7) [96,257,9,130,6,128,16] 13 :=
  permutation_upper _ _ _ [96,257,9,130,6,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10701

theorem m28428_32 : Upper (D 7) (R 7) [96,257,9,130,6,128,32] 13 :=
  permutation_upper _ _ _ [96,257,9,130,6,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10702

def r28428 : Route 9 := (fun mask => (mask,id))

def c28428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28428 : Upper (D 7) (R 7) [96,257,9,130,6,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,6,128] 13 (by decide) (choices 1) [16,32] r28428 c28428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28428_16
  · exact m28428_32

def b28429 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 200, targets := 33 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(3,0),(3,5)], upper := (rows 97 259 13 138 50 36 208 208 464), lower := (rows 97 259 13 138 50 36 64 128 256), losses := [] }

theorem u28429 : Upper (D 7) (R 7) [96,257,9,130,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28429 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28430 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 138 50 48 196 196 452), lower := (rows 97 259 13 138 50 48 64 128 256), losses := [] }

theorem u28430 : Upper (D 7) (R 7) [96,257,9,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28430 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28431 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 138 50 96 212 148 404), lower := (rows 97 259 13 138 50 96 64 128 256), losses := [] }

theorem u28431 : Upper (D 7) (R 7) [96,257,9,130,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28432 : Route 9 := (fun mask => (mask,id))

def c28432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28432 : Upper (D 7) (R 7) [96,257,9,130,34,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,34,128] 13 (by decide) (choices 1) [4,16] r28432 c28432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10703
  · exact u10704

def b28433 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 259 13 138 52 34 208 208 464), lower := (rows 97 259 13 138 52 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 84 148 276), good := (rows 96 290 508 170 500 34 64 128 256) },{ target := 6, region := (rows 1 2 4 8 20 42 0 128 256), good := (rows 33 291 61 170 52 34 0 128 256) },{ target := 7, region := (rows 1 2 4 8 20 42 64 0 256), good := (rows 97 291 61 42 52 34 64 0 256) }] }

theorem u28433 : Upper (D 7) (R 7) [96,257,9,130,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28434 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 259 13 138 52 48 194 194 450), lower := (rows 97 259 13 138 52 48 64 128 256), losses := [] }

theorem u28434 : Upper (D 7) (R 7) [96,257,9,130,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28434 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28435 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 138 52 96 210 146 402), lower := (rows 97 259 13 138 52 96 64 128 256), losses := [] }

theorem u28435 : Upper (D 7) (R 7) [96,257,9,130,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28436 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 97 259 13 138 52 160 82 210 338), lower := (rows 97 259 13 138 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 96 258 60 170 52 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 97 257 61 168 52 160 64 160 256) }] }

theorem u28436 : Upper (D 7) (R 7) [96,257,9,130,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28437 : Route 9 := (fun mask => (mask,id))

def c28437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28437 : Upper (D 7) (R 7) [96,257,9,130,132,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,132,2] 13 (by decide) (choices 1) [16,32] r28437 c28437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10705
  · exact u10706

theorem m28438_2 : Upper (D 7) (R 7) [96,257,9,130,132,16,2] 13 :=
  permutation_upper _ _ _ [96,257,9,130,132,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10705

def r28438 : Route 9 := (fun mask => (mask,id))

def c28438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28438 : Upper (D 7) (R 7) [96,257,9,130,132,16] 13 := by
  apply FastRouting.sound _ _ [96,257,9,130,132,16] 13 (by decide) (choices 1) [2,32] r28438 c28438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28438_2
  · exact u10707

def b28439 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 138 148 96 114 178 306), lower := (rows 97 259 13 138 148 96 64 128 256), losses := [] }

theorem u28439 : Upper (D 7) (R 7) [96,257,9,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28439
end Delivery.IrregularNine14.P07
