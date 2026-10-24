import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0147
import IrregularNine14P06C0148

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27720 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 74 49 484 452 452 452), lower := (rows 7 11 52 74 49 32 64 128 256), losses := [] }

theorem u27720 : Upper (D 6) (R 6) [6,9,48,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27721 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 74 52 481 449 449 449), lower := (rows 7 11 52 74 52 32 64 128 256), losses := [] }

theorem u27721 : Upper (D 6) (R 6) [6,9,48,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27722 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 11 52 74 81 420 484 420 420), lower := (rows 7 11 52 74 81 32 64 128 256), losses := [] }

theorem u27722 : Upper (D 6) (R 6) [6,9,48,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27723 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 11, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 74 84 417 481 417 417), lower := (rows 7 11 52 74 84 32 64 128 256), losses := [] }

theorem u27723 : Upper (D 6) (R 6) [6,9,48,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27724 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 74 112 421 453 389 389), lower := (rows 7 11 52 74 112 32 64 128 256), losses := [] }

theorem u27724 : Upper (D 6) (R 6) [6,9,48,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27725 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 52 74 145 356 356 484 356), lower := (rows 7 11 52 74 145 32 64 128 256), losses := [] }

theorem u27725 : Upper (D 6) (R 6) [6,9,48,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27726 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 52 74 148 353 353 481 353), lower := (rows 7 11 52 74 148 32 64 128 256), losses := [] }

theorem u27726 : Upper (D 6) (R 6) [6,9,48,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27727 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 74 176 357 325 453 325), lower := (rows 7 11 52 74 176 32 64 128 256), losses := [] }

theorem u27727 : Upper (D 6) (R 6) [6,9,48,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27728 : Route 9 := (fun mask => (mask,id))

def c27728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27728 : Upper (D 6) (R 6) [6,9,48,66,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,66,192] 13 (by decide) (choices 1) [1,4,256] r27728 c27728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8844
  · exact u8845
  · exact u8846

def r27729 : Route 9 := (fun mask => (mask,id))

def c27729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27729 : Upper (D 6) (R 6) [6,9,48,66,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,66,384] 13 (by decide) (choices 1) [1,4,64] r27729 c27729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8847
  · exact u8848
  · exact u8849

def b27730 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 104 19 484 452 452 452), lower := (rows 7 11 52 104 19 32 64 128 256), losses := [] }

theorem u27730 : Upper (D 6) (R 6) [6,9,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27731 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 104 21 482 450 450 450), lower := (rows 7 11 52 104 21 32 64 128 256), losses := [] }

theorem u27731 : Upper (D 6) (R 6) [6,9,48,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27732 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 104 22 481 449 449 449), lower := (rows 7 11 52 104 22 32 64 128 256), losses := [] }

theorem u27732 : Upper (D 6) (R 6) [6,9,48,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27733 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 488, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 52 104 81 422 454 390 390), lower := (rows 7 11 52 104 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 60 104 508 32 64 128 256) }] }

theorem u27733 : Upper (D 6) (R 6) [6,9,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27734 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 11 52 104 82 421 453 389 389), lower := (rows 7 11 52 104 82 32 64 128 256), losses := [] }

theorem u27734 : Upper (D 6) (R 6) [6,9,48,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27735 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 104 84 419 451 387 387), lower := (rows 7 11 52 104 84 32 64 128 256), losses := [] }

theorem u27735 : Upper (D 6) (R 6) [6,9,48,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27736 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 360, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 52 104 145 358 326 454 326), lower := (rows 7 11 52 104 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 60 104 508 32 64 128 256) }] }

theorem u27736 : Upper (D 6) (R 6) [6,9,48,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27737 : Route 9 := (fun mask => (mask,id))

def c27737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27737 : Upper (D 6) (R 6) [6,9,48,96,130] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,130] 13 (by decide) (choices 1) [1,4,64,256] r27737 c27737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8850
  · exact u8851
  · exact u8852
  · exact u8853

def b27738 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 11 52 104 148 355 323 451 323), lower := (rows 7 11 52 104 148 32 64 128 256), losses := [] }

theorem u27738 : Upper (D 6) (R 6) [6,9,48,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27739 : Route 9 := (fun mask => (mask,id))

def c27739 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27739 : Upper (D 6) (R 6) [6,9,48,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192] 13 (by decide) (choices 1) [1,2,4,256] r27739 c27739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8854
  · exact u8855
  · exact u8856
  · exact u8857

def r27740 : Route 9 := (fun mask => (mask,id))

def c27740 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27740 : Upper (D 6) (R 6) [6,9,48,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384] 13 (by decide) (choices 1) [1,2,4,64] r27740 c27740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8858
  · exact u8859
  · exact u8860
  · exact u8861

def b27741 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 52 138 21 352 352 480 352), lower := (rows 7 11 52 138 21 32 64 128 256), losses := [] }

theorem u27741 : Upper (D 6) (R 6) [6,9,48,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27742 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 138 49 356 324 452 324), lower := (rows 7 11 52 138 49 32 64 128 256), losses := [] }

theorem u27742 : Upper (D 6) (R 6) [6,9,48,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27743 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 138 52 353 321 449 321), lower := (rows 7 11 52 138 52 32 64 128 256), losses := [] }

theorem u27743 : Upper (D 6) (R 6) [6,9,48,130,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27744 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 488, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 52 138 81 356 356 484 356), lower := (rows 7 11 52 138 81 32 64 128 256), losses := [] }

theorem u27744 : Upper (D 6) (R 6) [6,9,48,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27745 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 52 138 84 353 353 481 353), lower := (rows 7 11 52 138 84 32 64 128 256), losses := [] }

theorem u27745 : Upper (D 6) (R 6) [6,9,48,130,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27746 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 138 112 357 325 453 325), lower := (rows 7 11 52 138 112 32 64 128 256), losses := [] }

theorem u27746 : Upper (D 6) (R 6) [6,9,48,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27747 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 232, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 52 138 273 100 100 228 356), lower := (rows 7 11 52 138 273 32 64 128 256), losses := [] }

theorem u27747 : Upper (D 6) (R 6) [6,9,48,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27748 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 52 138 276 97 97 225 353), lower := (rows 7 11 52 138 276 32 64 128 256), losses := [] }

theorem u27748 : Upper (D 6) (R 6) [6,9,48,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27749 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 138 304 101 69 197 325), lower := (rows 7 11 52 138 304 32 64 128 256), losses := [] }

theorem u27749 : Upper (D 6) (R 6) [6,9,48,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27750 : Route 9 := (fun mask => (mask,id))

def c27750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27750 : Upper (D 6) (R 6) [6,9,48,130,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,130,320] 13 (by decide) (choices 1) [1,4,64] r27750 c27750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8862
  · exact u8863
  · exact u8864

def b27751 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 168 19 356 324 452 324), lower := (rows 7 11 52 168 19 32 64 128 256), losses := [] }

theorem u27751 : Upper (D 6) (R 6) [6,9,48,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27752 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 168 21 354 322 450 322), lower := (rows 7 11 52 168 21 32 64 128 256), losses := [] }

theorem u27752 : Upper (D 6) (R 6) [6,9,48,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27753 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 52 168 22 353 321 449 321), lower := (rows 7 11 52 168 22 32 64 128 256), losses := [] }

theorem u27753 : Upper (D 6) (R 6) [6,9,48,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27754 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 488, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 52 168 81 358 326 454 326), lower := (rows 7 11 52 168 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 60 168 508 32 64 128 256) }] }

theorem u27754 : Upper (D 6) (R 6) [6,9,48,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27755 : Route 9 := (fun mask => (mask,id))

def c27755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27755 : Upper (D 6) (R 6) [6,9,48,160,66] 13 := by
  apply FastRouting.sound _ _ [6,9,48,160,66] 13 (by decide) (choices 1) [1,4,64,256] r27755 c27755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8865
  · exact u8866
  · exact u8867
  · exact u8868

def b27756 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 490, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 11 52 168 84 355 323 451 323), lower := (rows 7 11 52 168 84 32 64 128 256), losses := [] }

theorem u27756 : Upper (D 6) (R 6) [6,9,48,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27757 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 232, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 52 168 273 102 70 198 326), lower := (rows 7 11 52 168 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 60 168 508 32 64 128 256) }] }

theorem u27757 : Upper (D 6) (R 6) [6,9,48,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27758 : Route 9 := (fun mask => (mask,id))

def c27758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27758 : Upper (D 6) (R 6) [6,9,48,160,258] 13 := by
  apply FastRouting.sound _ _ [6,9,48,160,258] 13 (by decide) (choices 1) [1,4,64] r27758 c27758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8869
  · exact u8870
  · exact u8871

def b27759 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 11 52 168 276 99 67 195 323), lower := (rows 7 11 52 168 276 32 64 128 256), losses := [] }

theorem u27759 : Upper (D 6) (R 6) [6,9,48,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27760 : Route 9 := (fun mask => (mask,id))

def c27760 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27760 : Upper (D 6) (R 6) [6,9,48,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,160,320] 13 (by decide) (choices 1) [1,2,4,64] r27760 c27760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8872
  · exact u8873
  · exact u8874
  · exact u8875

def b27761 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 52 200 19 356 356 484 356), lower := (rows 7 11 52 200 19 32 64 128 256), losses := [] }

theorem u27761 : Upper (D 6) (R 6) [6,9,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27762 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 52 200 21 354 354 482 354), lower := (rows 7 11 52 200 21 32 64 128 256), losses := [] }

theorem u27762 : Upper (D 6) (R 6) [6,9,48,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27763 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 490, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 11 52 200 22 353 353 481 353), lower := (rows 7 11 52 200 22 32 64 128 256), losses := [] }

theorem u27763 : Upper (D 6) (R 6) [6,9,48,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27764 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 200 49 358 326 454 326), lower := (rows 7 11 52 200 49 32 64 128 256), losses := [] }

theorem u27764 : Upper (D 6) (R 6) [6,9,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27765 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 200 50 357 325 453 325), lower := (rows 7 11 52 200 50 32 64 128 256), losses := [] }

theorem u27765 : Upper (D 6) (R 6) [6,9,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27766 : PairBound 9 := { available := 323, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 200 52 355 323 451 323), lower := (rows 7 11 52 200 52 32 64 128 256), losses := [] }

theorem u27766 : Upper (D 6) (R 6) [6,9,48,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27767 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 488, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 7 11 52 200 81 294 358 422 294), lower := (rows 7 11 52 200 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 60 200 508 32 64 128 256) },{ target := 6, region := (rows 1 2 20 8 16 33 0 129 257), good := (rows 423 427 52 136 437 32 0 128 256) }] }

theorem u27767 : Upper (D 6) (R 6) [6,9,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27768 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 293, targets := 64 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 11 52 200 82 293 357 421 293), lower := (rows 7 11 52 200 82 32 64 128 256), losses := [] }

theorem u27768 : Upper (D 6) (R 6) [6,9,48,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27769 : Route 9 := (fun mask => (mask,id))

def c27769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27769 : Upper (D 6) (R 6) [6,9,48,192,68] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,68] 13 (by decide) (choices 1) [1,2,256] r27769 c27769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8876
  · exact u8877
  · exact u8878

def b27770 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 200 112 295 327 391 263), lower := (rows 7 11 52 200 112 32 64 128 256), losses := [] }

theorem u27770 : Upper (D 6) (R 6) [6,9,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27771 : Route 9 := (fun mask => (mask,id))

def c27771 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27771 : Upper (D 6) (R 6) [6,9,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257] 13 (by decide) (choices 1) [2,4,64] r27771 c27771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8879
  · exact u8880
  · exact u8881

def r27772 : Route 9 := (fun mask => (mask,id))

def c27772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27772 : Upper (D 6) (R 6) [6,9,48,192,258] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,258] 13 (by decide) (choices 1) [1,4,64] r27772 c27772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8882
  · exact u8883
  · exact u8884

def r27773 : Route 9 := (fun mask => (mask,id))

def c27773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27773 : Upper (D 6) (R 6) [6,9,48,192,260] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,260] 13 (by decide) (choices 1) [1,2,64] r27773 c27773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8885
  · exact u8886
  · exact u8887

def b27774 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 200 304 103 71 199 327), lower := (rows 7 11 52 200 304 32 64 128 256), losses := [] }

theorem u27774 : Upper (D 6) (R 6) [6,9,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27775 : Route 9 := (fun mask => (mask,id))

def c27775 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27775 : Upper (D 6) (R 6) [6,9,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320] 13 (by decide) (choices 1) [1,2,4] r27775 c27775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8888
  · exact u8889
  · exact u8890

def b27776 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 52 392 19 100 100 228 356), lower := (rows 7 11 52 392 19 32 64 128 256), losses := [] }

theorem u27776 : Upper (D 6) (R 6) [6,9,48,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27777 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 52 392 21 98 98 226 354), lower := (rows 7 11 52 392 21 32 64 128 256), losses := [] }

theorem u27777 : Upper (D 6) (R 6) [6,9,48,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27778 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 490, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 11 52 392 22 97 97 225 353), lower := (rows 7 11 52 392 22 32 64 128 256), losses := [] }

theorem u27778 : Upper (D 6) (R 6) [6,9,48,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27779 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 392 49 102 70 198 326), lower := (rows 7 11 52 392 49 32 64 128 256), losses := [] }

theorem u27779 : Upper (D 6) (R 6) [6,9,48,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27779
end Delivery.IrregularNine14.P06
