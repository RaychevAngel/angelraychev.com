import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0046

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13500 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,2)], upper := (rows 11 38 133 280 84 34 97 225 353), lower := (rows 11 38 133 280 84 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 69 133 261), good := (rows 491 482 481 280 472 34 64 128 256) }] }

theorem u13500 : Upper (D 6) (R 6) [10,36,129,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13501 : Route 9 := (fun mask => (mask,id))

def c13501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13501 : Upper (D 6) (R 6) [10,36,129,272,68,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272,68,64] 13 (by decide) (choices 1) [1,2,32] r13501 c13501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2767
  · exact u2768
  · exact u2769

def b13502 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 38 133 280 112 33 70 198 326), lower := (rows 11 38 133 280 112 33 64 128 256), losses := [] }

theorem u13502 : Upper (D 6) (R 6) [10,36,129,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13503 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 133 280 112 34 69 197 325), lower := (rows 11 38 133 280 112 34 64 128 256), losses := [] }

theorem u13503 : Upper (D 6) (R 6) [10,36,129,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13504 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 280 112 36 67 195 323), lower := (rows 11 38 133 280 112 36 64 128 256), losses := [] }

theorem u13504 : Upper (D 6) (R 6) [10,36,129,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13505 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 280 112 96 71 135 263), lower := (rows 11 38 133 280 112 96 64 128 256), losses := [] }

theorem u13505 : Upper (D 6) (R 6) [10,36,129,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13506 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 296 81 34 84 212 340), lower := (rows 11 38 133 296 81 34 64 128 256), losses := [] }

theorem u13506 : Upper (D 6) (R 6) [10,36,129,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13507 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 296 81 36 82 210 338), lower := (rows 11 38 133 296 81 36 64 128 256), losses := [] }

theorem u13507 : Upper (D 6) (R 6) [10,36,129,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13508 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 296 81 48 70 198 326), lower := (rows 11 38 133 296 81 48 64 128 256), losses := [] }

theorem u13508 : Upper (D 6) (R 6) [10,36,129,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13508 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13509 : Route 9 := (fun mask => (mask,id))

def c13509 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13509 : Upper (D 6) (R 6) [10,36,129,288,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,288,65,64] 13 (by decide) (choices 1) [2,4,16] r13509 c13509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2770
  · exact u2771
  · exact u2772

def b13510 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 296 82 33 84 212 340), lower := (rows 11 38 133 296 82 33 64 128 256), losses := [] }

theorem u13510 : Upper (D 6) (R 6) [10,36,129,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13511 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 296 82 36 81 209 337), lower := (rows 11 38 133 296 82 36 64 128 256), losses := [] }

theorem u13511 : Upper (D 6) (R 6) [10,36,129,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13512 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 296 82 48 69 197 325), lower := (rows 11 38 133 296 82 48 64 128 256), losses := [] }

theorem u13512 : Upper (D 6) (R 6) [10,36,129,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13512 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13513 : Route 9 := (fun mask => (mask,id))

def c13513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13513 : Upper (D 6) (R 6) [10,36,129,288,66,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,288,66,64] 13 (by decide) (choices 1) [1,4,16] r13513 c13513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2773
  · exact u2774
  · exact u2775

def b13514 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 296 84 33 82 210 338), lower := (rows 11 38 133 296 84 33 64 128 256), losses := [] }

theorem u13514 : Upper (D 6) (R 6) [10,36,129,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13515 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 296 84 34 81 209 337), lower := (rows 11 38 133 296 84 34 64 128 256), losses := [] }

theorem u13515 : Upper (D 6) (R 6) [10,36,129,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13516 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 296 84 48 67 195 323), lower := (rows 11 38 133 296 84 48 64 128 256), losses := [] }

theorem u13516 : Upper (D 6) (R 6) [10,36,129,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13516 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13517 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 133 296 84 96 83 147 275), lower := (rows 11 38 133 296 84 96 64 128 256), losses := [] }

theorem u13517 : Upper (D 6) (R 6) [10,36,129,288,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13518 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 133 328 49 34 84 212 340), lower := (rows 11 38 133 328 49 34 64 128 256), losses := [] }

theorem u13518 : Upper (D 6) (R 6) [10,36,129,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13519 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 328 49 36 82 210 338), lower := (rows 11 38 133 328 49 36 64 128 256), losses := [] }

theorem u13519 : Upper (D 6) (R 6) [10,36,129,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13520 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 133 328 49 48 70 198 326), lower := (rows 11 38 133 328 49 48 64 128 256), losses := [] }

theorem u13520 : Upper (D 6) (R 6) [10,36,129,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13520 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13521 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 134, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 38 133 328 49 96 86 150 278), lower := (rows 11 38 133 328 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 36 149 360 49 96 96 128 256) }] }

theorem u13521 : Upper (D 6) (R 6) [10,36,129,320,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13522 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 11 38 133 328 81 34 116 180 308), lower := (rows 11 38 133 328 81 34 64 128 256), losses := [] }

theorem u13522 : Upper (D 6) (R 6) [10,36,129,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13523 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 328 81 36 114 178 306), lower := (rows 11 38 133 328 81 36 64 128 256), losses := [] }

theorem u13523 : Upper (D 6) (R 6) [10,36,129,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13524 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 38 133 328 81 48 102 166 294), lower := (rows 11 38 133 328 81 48 64 128 256), losses := [] }

theorem u13524 : Upper (D 6) (R 6) [10,36,129,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13524 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13525 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 133 328 82 33 116 180 308), lower := (rows 11 38 133 328 82 33 64 128 256), losses := [] }

theorem u13525 : Upper (D 6) (R 6) [10,36,129,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13526 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 328 82 36 113 177 305), lower := (rows 11 38 133 328 82 36 64 128 256), losses := [] }

theorem u13526 : Upper (D 6) (R 6) [10,36,129,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13527 : Route 9 := (fun mask => (mask,id))

def c13527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13527 : Upper (D 6) (R 6) [10,36,129,320,66,16] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,66,16] 13 (by decide) (choices 1) [1,4,32] r13527 c13527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2776
  · exact u2777
  · exact u2778

def b13528 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 133 328 84 33 114 178 306), lower := (rows 11 38 133 328 84 33 64 128 256), losses := [] }

theorem u13528 : Upper (D 6) (R 6) [10,36,129,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13529 : Route 9 := (fun mask => (mask,id))

def c13529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13529 : Upper (D 6) (R 6) [10,36,129,320,68,2] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,68,2] 13 (by decide) (choices 1) [1,16,32] r13529 c13529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2779
  · exact u2780
  · exact u2781

def b13530 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 133 328 84 48 99 163 291), lower := (rows 11 38 133 328 84 48 64 128 256), losses := [] }

theorem u13530 : Upper (D 6) (R 6) [10,36,129,320,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13530 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13531 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 133 328 112 33 86 150 278), lower := (rows 11 38 133 328 112 33 64 128 256), losses := [] }

theorem u13531 : Upper (D 6) (R 6) [10,36,129,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13532 : Route 9 := (fun mask => (mask,id))

def c13532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13532 : Upper (D 6) (R 6) [10,36,129,320,96,2] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,96,2] 13 (by decide) (choices 1) [1,4,16] r13532 c13532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2782
  · exact u2783
  · exact u2784

def b13533 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 328 112 36 83 147 275), lower := (rows 11 38 133 328 112 36 64 128 256), losses := [] }

theorem u13533 : Upper (D 6) (R 6) [10,36,129,320,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13534 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 328 112 48 71 135 263), lower := (rows 11 38 133 328 112 48 64 128 256), losses := [] }

theorem u13534 : Upper (D 6) (R 6) [10,36,129,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13534 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13535 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 134 25 84 33 352 480 352), lower := (rows 11 38 134 25 84 33 64 128 256), losses := [] }

theorem u13535 : Upper (D 6) (R 6) [10,36,130,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13536 : Route 9 := (fun mask => (mask,id))

def c13536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13536 : Upper (D 6) (R 6) [10,36,130,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,68,64] 13 (by decide) (choices 1) [1,32,256] r13536 c13536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2785
  · exact u2786
  · exact u2787

def r13537 : Route 9 := (fun mask => (mask,id))

def c13537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13537 : Upper (D 6) (R 6) [10,36,130,17,68,256] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,68,256] 13 (by decide) (choices 1) [1,32] r13537 c13537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2788
  · exact u2789

def b13538 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 112 33 324 452 324), lower := (rows 11 38 134 25 112 33 64 128 256), losses := [] }

theorem u13538 : Upper (D 6) (R 6) [10,36,130,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13539 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 25 112 36 321 449 321), lower := (rows 11 38 134 25 112 36 64 128 256), losses := [] }

theorem u13539 : Upper (D 6) (R 6) [10,36,130,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13540 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 25 112 96 325 389 261), lower := (rows 11 38 134 25 112 96 64 128 256), losses := [] }

theorem u13540 : Upper (D 6) (R 6) [10,36,130,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13541 : Route 9 := (fun mask => (mask,id))

def c13541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13541 : Upper (D 6) (R 6) [10,36,130,17,96,256] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,96,256] 13 (by decide) (choices 1) [1,4] r13541 c13541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2790
  · exact u2791

def b13542 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 134 25 276 33 96 224 352), lower := (rows 11 38 134 25 276 33 64 128 256), losses := [] }

theorem u13542 : Upper (D 6) (R 6) [10,36,130,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13543 : Route 9 := (fun mask => (mask,id))

def c13543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13543 : Upper (D 6) (R 6) [10,36,130,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,260,64] 13 (by decide) (choices 1) [1,32] r13543 c13543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2792
  · exact u2793

def b13544 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 304 33 68 196 324), lower := (rows 11 38 134 25 304 33 64 128 256), losses := [] }

theorem u13544 : Upper (D 6) (R 6) [10,36,130,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13545 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 25 304 36 65 193 321), lower := (rows 11 38 134 25 304 36 64 128 256), losses := [] }

theorem u13545 : Upper (D 6) (R 6) [10,36,130,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13546 : Route 9 := (fun mask => (mask,id))

def c13546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13546 : Upper (D 6) (R 6) [10,36,130,17,288,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,288,64] 13 (by decide) (choices 1) [1,4] r13546 c13546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2794
  · exact u2795

def b13547 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 336 33 100 228 356), lower := (rows 11 38 134 25 336 33 64 128 256), losses := [] }

theorem u13547 : Upper (D 6) (R 6) [10,36,130,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13548 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 25 336 36 97 225 353), lower := (rows 11 38 134 25 336 36 64 128 256), losses := [] }

theorem u13548 : Upper (D 6) (R 6) [10,36,130,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13549 : Route 9 := (fun mask => (mask,id))

def c13549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13549 : Upper (D 6) (R 6) [10,36,130,17,320,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,320,64] 13 (by decide) (choices 1) [1,4,32] r13549 c13549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2796
  · exact u2797
  · exact u2798

def b13550 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 28 81 33 352 480 352), lower := (rows 11 38 134 28 81 33 64 128 256), losses := [] }

theorem u13550 : Upper (D 6) (R 6) [10,36,130,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13551 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 28 81 96 353 417 289), lower := (rows 11 38 134 28 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 112 64 128 256), good := (rows 10 38 134 62 112 96 96 128 256) }] }

theorem u13551 : Upper (D 6) (R 6) [10,36,130,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13552 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 28 81 288 97 225 353), lower := (rows 11 38 134 28 81 288 64 128 256), losses := [] }

theorem u13552 : Upper (D 6) (R 6) [10,36,130,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13552 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13553 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 28 273 33 96 224 352), lower := (rows 11 38 134 28 273 33 64 128 256), losses := [] }

theorem u13553 : Upper (D 6) (R 6) [10,36,130,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13554 : Route 9 := (fun mask => (mask,id))

def c13554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13554 : Upper (D 6) (R 6) [10,36,130,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,20,257,64] 13 (by decide) (choices 1) [1,32] r13554 c13554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2799
  · exact u2800

def b13555 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 28 336 33 97 225 353), lower := (rows 11 38 134 28 336 33 64 128 256), losses := [] }

theorem u13555 : Upper (D 6) (R 6) [10,36,130,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13556 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 28 336 96 97 161 289), lower := (rows 11 38 134 28 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 112 64 128 256), good := (rows 10 38 134 62 368 96 96 128 256) }] }

theorem u13556 : Upper (D 6) (R 6) [10,36,130,20,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13557 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 38 134 56 81 33 324 452 324), lower := (rows 11 38 134 56 81 33 64 128 256), losses := [] }

theorem u13557 : Upper (D 6) (R 6) [10,36,130,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13558 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 56 81 36 321 449 321), lower := (rows 11 38 134 56 81 36 64 128 256), losses := [] }

theorem u13558 : Upper (D 6) (R 6) [10,36,130,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13559 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 56 81 96 325 389 261), lower := (rows 11 38 134 56 81 96 64 128 256), losses := [] }

theorem u13559 : Upper (D 6) (R 6) [10,36,130,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13559
end Delivery.IrregularNine14.P06
