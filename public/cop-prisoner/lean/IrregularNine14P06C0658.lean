import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0430
import IrregularNine14P06C0431
import IrregularNine14P06C0432

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39480 : Route 9 := (fun mask => (mask,id))

def c39480 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39480 : Upper (D 6) (R 6) [40,96,129,20,257] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20,257] 13 (by decide) (choices 1) [2,4,64] r39480 c39480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25853
  · exact u25854
  · exact u25855

def r39481 : Route 9 := (fun mask => (mask,id))

def c39481 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39481 : Upper (D 6) (R 6) [40,96,129,20,258] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20,258] 13 (by decide) (choices 1) [1,2,4,64] r39481 c39481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25856
  · exact u25857
  · exact u25858
  · exact u25859

def b39482 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 98 133 28 276 99 67 195 323), lower := (rows 41 98 133 28 276 32 64 128 256), losses := [] }

theorem u39482 : Upper (D 6) (R 6) [40,96,129,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39483 : Route 9 := (fun mask => (mask,id))

def c39483 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39483 : Upper (D 6) (R 6) [40,96,129,20,320] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20,320] 13 (by decide) (choices 1) [1,2,4] r39483 c39483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25860
  · exact u25861
  · exact u25862

def b39484 : PairBound 9 := { available := 278, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 98 133 76 19 310 342 406 278), lower := (rows 41 98 133 76 19 32 64 128 256), losses := [] }

theorem u39484 : Upper (D 6) (R 6) [40,96,129,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39485 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 76 21 306 338 402 274), lower := (rows 41 98 133 76 21 32 64 128 256), losses := [] }

theorem u39485 : Upper (D 6) (R 6) [40,96,129,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39486 : Route 9 := (fun mask => (mask,id))

def c39486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39486 : Upper (D 6) (R 6) [40,96,129,68,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,6] 13 (by decide) (choices 1) [1,2,16,256] r39486 c39486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25863
  · exact u25864
  · exact u25865
  · exact u25866

def r39487 : Route 9 := (fun mask => (mask,id))

def c39487 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39487 : Upper (D 6) (R 6) [40,96,129,68,257] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,257] 13 (by decide) (choices 1) [2,4,16] r39487 c39487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25867
  · exact u25868
  · exact u25869

def r39488 : Route 9 := (fun mask => (mask,id))

def c39488 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39488 : Upper (D 6) (R 6) [40,96,129,68,258] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,258] 13 (by decide) (choices 1) [1,2,4,16] r39488 c39488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25870
  · exact u25871
  · exact u25872
  · exact u25873

def r39489 : Route 9 := (fun mask => (mask,id))

def c39489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39489 : Upper (D 6) (R 6) [40,96,129,68,260] 13 := by
  apply FastRouting.sound _ _ [40,96,129,68,260] 13 (by decide) (choices 1) [1,2,16] r39489 c39489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25874
  · exact u25875
  · exact u25876

def b39490 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 88 19 294 326 390 262), lower := (rows 41 98 133 88 19 32 64 128 256), losses := [] }

theorem u39490 : Upper (D 6) (R 6) [40,96,129,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39491 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 88 21 294 326 390 262), lower := (rows 41 98 133 88 21 32 64 128 256), losses := [] }

theorem u39491 : Upper (D 6) (R 6) [40,96,129,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39492 : Route 9 := (fun mask => (mask,id))

def c39492 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39492 : Upper (D 6) (R 6) [40,96,129,80,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,6] 13 (by decide) (choices 1) [1,2,4,256] r39492 c39492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25877
  · exact u25878
  · exact u25879
  · exact u25880

def r39493 : Route 9 := (fun mask => (mask,id))

def c39493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39493 : Upper (D 6) (R 6) [40,96,129,80,257] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,257] 13 (by decide) (choices 1) [2,4] r39493 c39493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25881
  · exact u25882

def r39494 : Route 9 := (fun mask => (mask,id))

def c39494 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39494 : Upper (D 6) (R 6) [40,96,129,80,258] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,258] 13 (by decide) (choices 1) [1,2,4] r39494 c39494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25883
  · exact u25884
  · exact u25885

def r39495 : Route 9 := (fun mask => (mask,id))

def c39495 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39495 : Upper (D 6) (R 6) [40,96,129,80,260] 13 := by
  apply FastRouting.sound _ _ [40,96,129,80,260] 13 (by decide) (choices 1) [1,2,4] r39495 c39495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25886
  · exact u25887
  · exact u25888

def r39496 : Route 9 := (fun mask => (mask,id))

def c39496 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39496 : Upper (D 6) (R 6) [40,96,129,257,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,257,6] 13 (by decide) (choices 1) [2,4,16,64] r39496 c39496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25889
  · exact u25890
  · exact u25891
  · exact u25892

def b39497 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 133 265 82 54 86 150 278), lower := (rows 41 98 133 265 82 32 64 128 256), losses := [] }

theorem u39497 : Upper (D 6) (R 6) [40,96,129,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39498 : Route 9 := (fun mask => (mask,id))

def c39498 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39498 : Upper (D 6) (R 6) [40,96,129,257,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,257,68] 13 (by decide) (choices 1) [2,4,16] r39498 c39498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25893
  · exact u25894
  · exact u25895

def b39499 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(3,5)], upper := (rows 41 98 133 266 19 116 84 212 340), lower := (rows 41 98 133 266 19 32 64 128 256), losses := [] }

theorem u39499 : Upper (D 6) (R 6) [40,96,129,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39500 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 266 21 118 86 214 342), lower := (rows 41 98 133 266 21 32 64 128 256), losses := [] }

theorem u39500 : Upper (D 6) (R 6) [40,96,129,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39501 : Route 9 := (fun mask => (mask,id))

def c39501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39501 : Upper (D 6) (R 6) [40,96,129,258,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,258,6] 13 (by decide) (choices 1) [1,4,16,64] r39501 c39501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25896
  · exact u25897
  · exact u25898
  · exact u25899

def r39502 : Route 9 := (fun mask => (mask,id))

def c39502 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39502 : Upper (D 6) (R 6) [40,96,129,258,65] 13 := by
  apply FastRouting.sound _ _ [40,96,129,258,65] 13 (by decide) (choices 1) [2,4,16] r39502 c39502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25900
  · exact u25901
  · exact u25902

def b39503 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 133 266 82 53 85 149 277), lower := (rows 41 98 133 266 82 32 64 128 256), losses := [] }

theorem u39503 : Upper (D 6) (R 6) [40,96,129,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39504 : Route 9 := (fun mask => (mask,id))

def c39504 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39504 : Upper (D 6) (R 6) [40,96,129,258,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,258,68] 13 (by decide) (choices 1) [1,2,4,16] r39504 c39504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25903
  · exact u25904
  · exact u25905
  · exact u25906

def r39505 : Route 9 := (fun mask => (mask,id))

def c39505 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39505 : Upper (D 6) (R 6) [40,96,129,260,3] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,3] 13 (by decide) (choices 1) [2,4,16,64] r39505 c39505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25907
  · exact u25908
  · exact u25909
  · exact u25910

def b39506 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 268 21 114 82 210 338), lower := (rows 41 98 133 268 21 32 64 128 256), losses := [] }

theorem u39506 : Upper (D 6) (R 6) [40,96,129,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39507 : Route 9 := (fun mask => (mask,id))

def c39507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39507 : Upper (D 6) (R 6) [40,96,129,260,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,6] 13 (by decide) (choices 1) [1,2,16,64] r39507 c39507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25911
  · exact u25912
  · exact u25913
  · exact u25914

def r39508 : Route 9 := (fun mask => (mask,id))

def c39508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39508 : Upper (D 6) (R 6) [40,96,129,260,65] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,65] 13 (by decide) (choices 1) [2,4,16] r39508 c39508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25915
  · exact u25916
  · exact u25917

def b39509 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 133 268 82 55 87 151 279), lower := (rows 41 98 133 268 82 32 64 128 256), losses := [] }

theorem u39509 : Upper (D 6) (R 6) [40,96,129,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39510 : Route 9 := (fun mask => (mask,id))

def c39510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39510 : Upper (D 6) (R 6) [40,96,129,260,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,260,68] 13 (by decide) (choices 1) [1,2,16] r39510 c39510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25918
  · exact u25919
  · exact u25920

def b39511 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 41 98 133 280 19 102 70 198 326), lower := (rows 41 98 133 280 19 32 64 128 256), losses := [] }

theorem u39511 : Upper (D 6) (R 6) [40,96,129,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39512 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 280 21 102 70 198 326), lower := (rows 41 98 133 280 21 32 64 128 256), losses := [] }

theorem u39512 : Upper (D 6) (R 6) [40,96,129,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39513 : Route 9 := (fun mask => (mask,id))

def c39513 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39513 : Upper (D 6) (R 6) [40,96,129,272,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,272,6] 13 (by decide) (choices 1) [1,2,4,64] r39513 c39513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25921
  · exact u25922
  · exact u25923
  · exact u25924

def r39514 : Route 9 := (fun mask => (mask,id))

def c39514 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39514 : Upper (D 6) (R 6) [40,96,129,272,65] 13 := by
  apply FastRouting.sound _ _ [40,96,129,272,65] 13 (by decide) (choices 1) [2,4] r39514 c39514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25925
  · exact u25926

def b39515 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 133 280 82 39 71 135 263), lower := (rows 41 98 133 280 82 32 64 128 256), losses := [] }

theorem u39515 : Upper (D 6) (R 6) [40,96,129,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39516 : Route 9 := (fun mask => (mask,id))

def c39516 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39516 : Upper (D 6) (R 6) [40,96,129,272,68] 13 := by
  apply FastRouting.sound _ _ [40,96,129,272,68] 13 (by decide) (choices 1) [1,2,4] r39516 c39516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25927
  · exact u25928
  · exact u25929

def b39517 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 98 133 328 19 54 86 150 278), lower := (rows 41 98 133 328 19 32 64 128 256), losses := [] }

theorem u39517 : Upper (D 6) (R 6) [40,96,129,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39518 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 133 328 21 54 86 150 278), lower := (rows 41 98 133 328 21 32 64 128 256), losses := [] }

theorem u39518 : Upper (D 6) (R 6) [40,96,129,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39519 : Route 9 := (fun mask => (mask,id))

def c39519 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39519 : Upper (D 6) (R 6) [40,96,129,320,6] 13 := by
  apply FastRouting.sound _ _ [40,96,129,320,6] 13 (by decide) (choices 1) [1,2,4,16] r39519 c39519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25930
  · exact u25931
  · exact u25932
  · exact u25933

def b39520 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 98 134 13 19 372 340 468 340), lower := (rows 41 98 134 13 19 32 64 128 256), losses := [] }

theorem u39520 : Upper (D 6) (R 6) [40,96,130,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39521 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 134 13 21 370 338 466 338), lower := (rows 41 98 134 13 21 32 64 128 256), losses := [] }

theorem u39521 : Upper (D 6) (R 6) [40,96,130,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39522 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 13 22 369 337 465 337), lower := (rows 41 98 134 13 22 32 64 128 256), losses := [] }

theorem u39522 : Upper (D 6) (R 6) [40,96,130,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39523 : Route 9 := (fun mask => (mask,id))

def c39523 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39523 : Upper (D 6) (R 6) [40,96,130,5,65] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,65] 13 (by decide) (choices 1) [2,4,16,256] r39523 c39523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25934
  · exact u25935
  · exact u25936
  · exact u25937

def b39524 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 134 13 82 309 341 405 277), lower := (rows 41 98 134 13 82 32 64 128 256), losses := [] }

theorem u39524 : Upper (D 6) (R 6) [40,96,130,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39525 : Route 9 := (fun mask => (mask,id))

def c39525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39525 : Upper (D 6) (R 6) [40,96,130,5,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,68] 13 (by decide) (choices 1) [1,2,16,256] r39525 c39525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25938
  · exact u25939
  · exact u25940
  · exact u25941

def r39526 : Route 9 := (fun mask => (mask,id))

def c39526 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39526 : Upper (D 6) (R 6) [40,96,130,5,257] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,257] 13 (by decide) (choices 1) [2,4,16,64] r39526 c39526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25942
  · exact u25943
  · exact u25944
  · exact u25945

def r39527 : Route 9 := (fun mask => (mask,id))

def c39527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39527 : Upper (D 6) (R 6) [40,96,130,5,258] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,258] 13 (by decide) (choices 1) [1,4,16,64] r39527 c39527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25946
  · exact u25947
  · exact u25948
  · exact u25949

def r39528 : Route 9 := (fun mask => (mask,id))

def c39528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39528 : Upper (D 6) (R 6) [40,96,130,5,260] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,260] 13 (by decide) (choices 1) [1,2,16,64] r39528 c39528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25950
  · exact u25951
  · exact u25952
  · exact u25953

def r39529 : Route 9 := (fun mask => (mask,id))

def c39529 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39529 : Upper (D 6) (R 6) [40,96,130,5,320] 13 := by
  apply FastRouting.sound _ _ [40,96,130,5,320] 13 (by decide) (choices 1) [1,2,4,16] r39529 c39529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25954
  · exact u25955
  · exact u25956
  · exact u25957

def b39530 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 134 25 19 356 324 452 324), lower := (rows 41 98 134 25 19 32 64 128 256), losses := [] }

theorem u39530 : Upper (D 6) (R 6) [40,96,130,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39531 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 134 25 21 358 326 454 326), lower := (rows 41 98 134 25 21 32 64 128 256), losses := [] }

theorem u39531 : Upper (D 6) (R 6) [40,96,130,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39532 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 134 25 22 357 325 453 325), lower := (rows 41 98 134 25 22 32 64 128 256), losses := [] }

theorem u39532 : Upper (D 6) (R 6) [40,96,130,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39533 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 134 25 81 294 326 390 262), lower := (rows 41 98 134 25 81 32 64 128 256), losses := [] }

theorem u39533 : Upper (D 6) (R 6) [40,96,130,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39534 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 134 25 82 293 325 389 261), lower := (rows 41 98 134 25 82 32 64 128 256), losses := [] }

theorem u39534 : Upper (D 6) (R 6) [40,96,130,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39535 : Route 9 := (fun mask => (mask,id))

def c39535 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39535 : Upper (D 6) (R 6) [40,96,130,17,68] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17,68] 13 (by decide) (choices 1) [1,2,4,256] r39535 c39535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25958
  · exact u25959
  · exact u25960
  · exact u25961

def b39536 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 134 25 273 102 70 198 326), lower := (rows 41 98 134 25 273 32 64 128 256), losses := [] }

theorem u39536 : Upper (D 6) (R 6) [40,96,130,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39537 : Route 9 := (fun mask => (mask,id))

def c39537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39537 : Upper (D 6) (R 6) [40,96,130,17,258] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17,258] 13 (by decide) (choices 1) [1,4,64] r39537 c39537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25962
  · exact u25963
  · exact u25964

def r39538 : Route 9 := (fun mask => (mask,id))

def c39538 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39538 : Upper (D 6) (R 6) [40,96,130,17,260] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17,260] 13 (by decide) (choices 1) [1,2,4,64] r39538 c39538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25965
  · exact u25966
  · exact u25967
  · exact u25968

def r39539 : Route 9 := (fun mask => (mask,id))

def c39539 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39539 : Upper (D 6) (R 6) [40,96,130,17,320] 13 := by
  apply FastRouting.sound _ _ [40,96,130,17,320] 13 (by decide) (choices 1) [1,2,4] r39539 c39539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25969
  · exact u25970
  · exact u25971

#print axioms u39539
end Delivery.IrregularNine14.P06
