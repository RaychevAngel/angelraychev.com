import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0427
import IrregularNine14P07C0428
import IrregularNine14P07C0429

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38400 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38400 : Upper (D 7) (R 7) [36,257,10,17,192] 13 := by
  apply FastRouting.sound _ _ [36,257,10,17,192] 13 (by decide) (choices 1) [2,64] r38400 c38400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25658
  · exact u25659

def b38401 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 37 259 14 56 19 224 192 192 448), lower := (rows 37 259 14 56 19 32 64 128 256), losses := [] }

theorem u38401 : Upper (D 7) (R 7) [36,257,10,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38402 : Route 9 := (fun mask => (mask,id))

def c38402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38402 : Upper (D 7) (R 7) [36,257,10,48,65] 13 := by
  apply FastRouting.sound _ _ [36,257,10,48,65] 13 (by decide) (choices 1) [2,64,128] r38402 c38402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25660
  · exact u25661
  · exact u25662

def b38403 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 37 259 14 56 82 225 193 193 449), lower := (rows 37 259 14 56 82 32 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 39 71 135 263), good := (rows 485 481 493 56 504 32 64 128 256) }] }

theorem u38403 : Upper (D 7) (R 7) [36,257,10,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38404 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38404 : Upper (D 7) (R 7) [36,257,10,48,192] 13 := by
  apply FastRouting.sound _ _ [36,257,10,48,192] 13 (by decide) (choices 1) [1,2,64] r38404 c38404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25663
  · exact u25664
  · exact u25665

def r38405 : Route 9 := (fun mask => (mask,id))

def c38405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38405 : Upper (D 7) (R 7) [36,257,10,65,34] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,34] 13 (by decide) (choices 1) [16,64,128] r38405 c38405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25666
  · exact u25667
  · exact u25668

def r38406 : Route 9 := (fun mask => (mask,id))

def c38406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38406 : Upper (D 7) (R 7) [36,257,10,65,66] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,66] 13 (by decide) (choices 1) [16,128] r38406 c38406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25669
  · exact u25670

def r38407 : Route 9 := (fun mask => (mask,id))

def c38407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38407 : Upper (D 7) (R 7) [36,257,10,65,96] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,96] 13 (by decide) (choices 1) [2,16,128] r38407 c38407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25671
  · exact u25672
  · exact u25673

def r38408 : Route 9 := (fun mask => (mask,id))

def c38408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38408 : Upper (D 7) (R 7) [36,257,10,65,130] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,130] 13 (by decide) (choices 1) [16,64,128] r38408 c38408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25674
  · exact u25675
  · exact u25676

def r38409 : Route 9 := (fun mask => (mask,id))

def c38409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38409 : Upper (D 7) (R 7) [36,257,10,65,160] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,160] 13 (by decide) (choices 1) [2,16,64,128] r38409 c38409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25677
  · exact u25678
  · exact u25679
  · exact u25680

def r38410 : Route 9 := (fun mask => (mask,id))

def c38410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38410 : Upper (D 7) (R 7) [36,257,10,65,192] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,192] 13 (by decide) (choices 1) [2,16,128] r38410 c38410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25681
  · exact u25682
  · exact u25683

def b38411 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 37 259 14 88 19 224 224 224 480), lower := (rows 37 259 14 88 19 32 64 128 256), losses := [] }

theorem u38411 : Upper (D 7) (R 7) [36,257,10,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38412 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 259 14 88 49 226 194 194 450), lower := (rows 37 259 14 88 49 32 64 128 256), losses := [] }

theorem u38412 : Upper (D 7) (R 7) [36,257,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38413 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,1)], upper := (rows 37 259 14 88 50 225 193 193 449), lower := (rows 37 259 14 88 50 32 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 39 71 135 263), good := (rows 485 481 493 88 504 32 64 128 256) },{ target := 5, region := (rows 1 3 20 24 16 0 67 131 259), good := (rows 455 451 462 92 478 0 64 128 256) }] }

theorem u38413 : Upper (D 7) (R 7) [36,257,10,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38414 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 259 14 88 81 162 226 162 418), lower := (rows 37 259 14 88 81 32 64 128 256), losses := [] }

theorem u38414 : Upper (D 7) (R 7) [36,257,10,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38415 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 37 259 14 88 82 161 225 161 417), lower := (rows 37 259 14 88 82 32 64 128 256), losses := [] }

theorem u38415 : Upper (D 7) (R 7) [36,257,10,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38416 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 259 14 88 112 163 195 131 387), lower := (rows 37 259 14 88 112 32 64 128 256), losses := [] }

theorem u38416 : Upper (D 7) (R 7) [36,257,10,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38417 : Route 9 := (fun mask => (mask,id))

def c38417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38417 : Upper (D 7) (R 7) [36,257,10,80,129] 13 := by
  apply FastRouting.sound _ _ [36,257,10,80,129] 13 (by decide) (choices 1) [2,64,128] r38417 c38417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25684
  · exact u25685
  · exact u25686

def r38418 : Route 9 := (fun mask => (mask,id))

def c38418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38418 : Upper (D 7) (R 7) [36,257,10,80,130] 13 := by
  apply FastRouting.sound _ _ [36,257,10,80,130] 13 (by decide) (choices 1) [1,64,128] r38418 c38418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25687
  · exact u25688
  · exact u25689

def r38419 : Route 9 := (fun mask => (mask,id))

def c38419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38419 : Upper (D 7) (R 7) [36,257,10,80,160] 13 := by
  apply FastRouting.sound _ _ [36,257,10,80,160] 13 (by decide) (choices 1) [1,2,64,128] r38419 c38419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25690
  · exact u25691
  · exact u25692
  · exact u25693

def b38420 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 259 14 88 208 163 227 163 419), lower := (rows 37 259 14 88 208 32 64 128 256), losses := [] }

theorem u38420 : Upper (D 7) (R 7) [36,257,10,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38421 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 37 259 14 104 19 240 208 208 464), lower := (rows 37 259 14 104 19 32 64 128 256), losses := [] }

theorem u38421 : Upper (D 7) (R 7) [36,257,10,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38422 : Route 9 := (fun mask => (mask,id))

def c38422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38422 : Upper (D 7) (R 7) [36,257,10,96,65] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,65] 13 (by decide) (choices 1) [2,16,128] r38422 c38422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25694
  · exact u25695
  · exact u25696

def r38423 : Route 9 := (fun mask => (mask,id))

def c38423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38423 : Upper (D 7) (R 7) [36,257,10,96,66] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,66] 13 (by decide) (choices 1) [1,16,128] r38423 c38423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25697
  · exact u25698
  · exact u25699

def r38424 : Route 9 := (fun mask => (mask,id))

def c38424 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38424 : Upper (D 7) (R 7) [36,257,10,96,129] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,129] 13 (by decide) (choices 1) [2,16,64,128] r38424 c38424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25700
  · exact u25701
  · exact u25702
  · exact u25703

def r38425 : Route 9 := (fun mask => (mask,id))

def c38425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38425 : Upper (D 7) (R 7) [36,257,10,96,130] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,130] 13 (by decide) (choices 1) [1,16,64,128] r38425 c38425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25704
  · exact u25705
  · exact u25706
  · exact u25707

def r38426 : Route 9 := (fun mask => (mask,id))

def c38426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38426 : Upper (D 7) (R 7) [36,257,10,96,192] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,192] 13 (by decide) (choices 1) [1,2,16,128] r38426 c38426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25708
  · exact u25709
  · exact u25710
  · exact u25711

def b38427 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 37 259 14 200 19 240 240 240 496), lower := (rows 37 259 14 200 19 32 64 128 256), losses := [] }

theorem u38427 : Upper (D 7) (R 7) [36,257,10,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38428 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 259 14 200 49 242 210 210 466), lower := (rows 37 259 14 200 49 32 64 128 256), losses := [] }

theorem u38428 : Upper (D 7) (R 7) [36,257,10,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38429 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38429 : Upper (D 7) (R 7) [36,257,10,192,34] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192,34] 13 (by decide) (choices 1) [1,16,64] r38429 c38429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25712
  · exact u25713
  · exact u25714

def r38430 : Route 9 := (fun mask => (mask,id))

def c38430 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38430 : Upper (D 7) (R 7) [36,257,10,192,65] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192,65] 13 (by decide) (choices 1) [2,16,128] r38430 c38430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25715
  · exact u25716
  · exact u25717

def r38431 : Route 9 := (fun mask => (mask,id))

def c38431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38431 : Upper (D 7) (R 7) [36,257,10,192,66] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192,66] 13 (by decide) (choices 1) [1,16,128] r38431 c38431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25718
  · exact u25719
  · exact u25720

def r38432 : Route 9 := (fun mask => (mask,id))

def c38432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38432 : Upper (D 7) (R 7) [36,257,10,192,96] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192,96] 13 (by decide) (choices 1) [1,2,16,128] r38432 c38432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25721
  · exact u25722
  · exact u25723
  · exact u25724

def b38433 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 259 14 200 208 51 115 179 307), lower := (rows 37 259 14 200 208 32 64 128 256), losses := [] }

theorem u38433 : Upper (D 7) (R 7) [36,257,10,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38434 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 28 11 50 224 192 192 448), lower := (rows 37 259 28 11 50 32 64 128 256), losses := [] }

theorem u38434 : Upper (D 7) (R 7) [36,257,24,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38435 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 28 11 82 224 224 224 480), lower := (rows 37 259 28 11 82 32 64 128 256), losses := [] }

theorem u38435 : Upper (D 7) (R 7) [36,257,24,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38436 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 1, region := 8, targets := 192 }], pairs := [(1,5),(3,5),(3,6),(3,7)], upper := (rows 37 259 28 11 112 226 194 194 450), lower := (rows 37 259 28 11 112 32 64 128 256), losses := [] }

theorem u38436 : Upper (D 7) (R 7) [36,257,24,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38437 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 28 11 208 226 226 226 482), lower := (rows 37 259 28 11 208 32 64 128 256), losses := [] }

theorem u38437 : Upper (D 7) (R 7) [36,257,24,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38438 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 28 41 82 226 194 194 450), lower := (rows 37 259 28 41 82 32 64 128 256), losses := [] }

theorem u38438 : Upper (D 7) (R 7) [36,257,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38439 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 28 41 208 226 194 194 450), lower := (rows 37 259 28 41 208 32 64 128 256), losses := [] }

theorem u38439 : Upper (D 7) (R 7) [36,257,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38440 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 232, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 37 259 28 42 81 226 194 194 450), lower := (rows 37 259 28 42 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 19 12 8 19 0 95 159 287), good := (rows 471 467 478 478 467 0 64 128 256) }] }

theorem u38440 : Upper (D 7) (R 7) [36,257,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38441 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(4,5)], upper := (rows 37 259 28 42 82 225 193 193 449), lower := (rows 37 259 28 42 82 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 12 8 27 0 67 131 259), good := (rows 471 467 28 478 466 0 64 128 256) }] }

theorem u38441 : Upper (D 7) (R 7) [36,257,24,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38442 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38442 : Upper (D 7) (R 7) [36,257,24,34,192] 13 := by
  apply FastRouting.sound _ _ [36,257,24,34,192] 13 (by decide) (choices 1) [1,2,64] r38442 c38442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25725
  · exact u25726
  · exact u25727

def r38443 : Route 9 := (fun mask => (mask,id))

def c38443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38443 : Upper (D 7) (R 7) [36,257,24,65,66] 13 := by
  apply FastRouting.sound _ _ [36,257,24,65,66] 13 (by decide) (choices 1) [2,128] r38443 c38443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25728
  · exact u25729

def b38444 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 28 73 112 162 194 130 386), lower := (rows 37 259 28 73 112 32 64 128 256), losses := [] }

theorem u38444 : Upper (D 7) (R 7) [36,257,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38445 : Route 9 := (fun mask => (mask,id))

def c38445 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38445 : Upper (D 7) (R 7) [36,257,24,65,130] 13 := by
  apply FastRouting.sound _ _ [36,257,24,65,130] 13 (by decide) (choices 1) [2,64,128] r38445 c38445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25730
  · exact u25731
  · exact u25732

def r38446 : Route 9 := (fun mask => (mask,id))

def c38446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38446 : Upper (D 7) (R 7) [36,257,24,65,160] 13 := by
  apply FastRouting.sound _ _ [36,257,24,65,160] 13 (by decide) (choices 1) [2,64,128] r38446 c38446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25733
  · exact u25734
  · exact u25735

def r38447 : Route 9 := (fun mask => (mask,id))

def c38447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38447 : Upper (D 7) (R 7) [36,257,24,65,192] 13 := by
  apply FastRouting.sound _ _ [36,257,24,65,192] 13 (by decide) (choices 1) [2,128] r38447 c38447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25736
  · exact u25737

def b38448 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 37 259 28 74 82 161 225 161 417), lower := (rows 37 259 28 74 82 32 64 128 256), losses := [] }

theorem u38448 : Upper (D 7) (R 7) [36,257,24,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38449 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(3,5)], upper := (rows 37 259 28 74 112 163 195 131 387), lower := (rows 37 259 28 74 112 32 64 128 256), losses := [] }

theorem u38449 : Upper (D 7) (R 7) [36,257,24,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m38450_128 : Upper (D 7) (R 7) [36,257,24,66,130,128] 13 :=
  permutation_upper _ _ _ [36,257,24,66,130,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u25739

def r38450 : Route 9 := (fun mask => (mask,id))

def c38450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38450 : Upper (D 7) (R 7) [36,257,24,66,130] 13 := by
  apply FastRouting.sound _ _ [36,257,24,66,130] 13 (by decide) (choices 1) [1,64,128] r38450 c38450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25738
  · exact u25739
  · exact m38450_128

def r38451 : Route 9 := (fun mask => (mask,id))

def c38451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38451 : Upper (D 7) (R 7) [36,257,24,66,160] 13 := by
  apply FastRouting.sound _ _ [36,257,24,66,160] 13 (by decide) (choices 1) [1,2,64,128] r38451 c38451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25740
  · exact u25741
  · exact u25742
  · exact u25743

def r38452 : Route 9 := (fun mask => (mask,id))

def c38452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38452 : Upper (D 7) (R 7) [36,257,24,66,192] 13 := by
  apply FastRouting.sound _ _ [36,257,24,66,192] 13 (by decide) (choices 1) [1,2,128] r38452 c38452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25744
  · exact u25745
  · exact u25746

def b38453 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 37 259 28 104 208 163 195 131 387), lower := (rows 37 259 28 104 208 32 64 128 256), losses := [] }

theorem u38453 : Upper (D 7) (R 7) [36,257,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38454 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(4,0)], upper := (rows 37 259 28 200 208 35 99 163 291), lower := (rows 37 259 28 200 208 32 64 128 256), losses := [] }

theorem u38454 : Upper (D 7) (R 7) [36,257,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38455 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 37 259 69 26 26 224 224 224 480), lower := (rows 37 259 69 26 26 32 64 128 256), losses := [] }

theorem u38455 : Upper (D 7) (R 7) [36,257,65,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38456 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 26 50 232 200 200 456), lower := (rows 37 259 69 26 50 32 64 128 256), losses := [] }

theorem u38456 : Upper (D 7) (R 7) [36,257,65,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38457 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 248, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 37 259 69 26 56 226 194 194 450), lower := (rows 37 259 69 26 56 32 64 128 256), losses := [] }

theorem u38457 : Upper (D 7) (R 7) [36,257,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38458 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 26 82 168 232 168 424), lower := (rows 37 259 69 26 82 32 64 128 256), losses := [] }

theorem u38458 : Upper (D 7) (R 7) [36,257,65,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38459 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 37 259 69 26 88 162 226 162 418), lower := (rows 37 259 69 26 88 32 64 128 256), losses := [] }

theorem u38459 : Upper (D 7) (R 7) [36,257,65,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38459
end Delivery.IrregularNine14.P07
