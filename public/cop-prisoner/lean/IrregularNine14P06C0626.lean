import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0382
import IrregularNine14P06C0383

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37560 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 44 88 22 353 321 449 321), lower := (rows 35 134 44 88 22 32 64 128 256), losses := [] }

theorem u37560 : Upper (D 6) (R 6) [34,132,40,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37561 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 44 88 81 295 327 391 263), lower := (rows 35 134 44 88 81 32 64 128 256), losses := [] }

theorem u37561 : Upper (D 6) (R 6) [34,132,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37562 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 44 88 82 293 325 389 261), lower := (rows 35 134 44 88 82 32 64 128 256), losses := [] }

theorem u37562 : Upper (D 6) (R 6) [34,132,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37563 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 44 88 84 291 323 387 259), lower := (rows 35 134 44 88 84 32 64 128 256), losses := [] }

theorem u37563 : Upper (D 6) (R 6) [34,132,40,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37564 : Route 9 := (fun mask => (mask,id))

def c37564 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37564 : Upper (D 6) (R 6) [34,132,40,80,257] 13 := by
  apply FastRouting.sound _ _ [34,132,40,80,257] 13 (by decide) (choices 1) [1,2,4,64] r37564 c37564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22922
  · exact u22923
  · exact u22924
  · exact u22925

def r37565 : Route 9 := (fun mask => (mask,id))

def c37565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37565 : Upper (D 6) (R 6) [34,132,40,80,258] 13 := by
  apply FastRouting.sound _ _ [34,132,40,80,258] 13 (by decide) (choices 1) [1,4,64] r37565 c37565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22926
  · exact u22927
  · exact u22928

def r37566 : Route 9 := (fun mask => (mask,id))

def c37566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37566 : Upper (D 6) (R 6) [34,132,40,80,260] 13 := by
  apply FastRouting.sound _ _ [34,132,40,80,260] 13 (by decide) (choices 1) [1,2,64] r37566 c37566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22929
  · exact u22930
  · exact u22931

def b37567 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 44 88 336 39 71 135 263), lower := (rows 35 134 44 88 336 32 64 128 256), losses := [] }

theorem u37567 : Upper (D 6) (R 6) [34,132,40,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37568 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 44 265 19 116 84 212 340), lower := (rows 35 134 44 265 19 32 64 128 256), losses := [] }

theorem u37568 : Upper (D 6) (R 6) [34,132,40,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37569 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 35 134 44 265 21 114 82 210 338), lower := (rows 35 134 44 265 21 32 64 128 256), losses := [] }

theorem u37569 : Upper (D 6) (R 6) [34,132,40,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37570 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 44 265 22 113 81 209 337), lower := (rows 35 134 44 265 22 32 64 128 256), losses := [] }

theorem u37570 : Upper (D 6) (R 6) [34,132,40,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37571 : Route 9 := (fun mask => (mask,id))

def c37571 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37571 : Upper (D 6) (R 6) [34,132,40,257,65] 13 := by
  apply FastRouting.sound _ _ [34,132,40,257,65] 13 (by decide) (choices 1) [2,4,16,64] r37571 c37571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22932
  · exact u22933
  · exact u22934
  · exact u22935

def r37572 : Route 9 := (fun mask => (mask,id))

def c37572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37572 : Upper (D 6) (R 6) [34,132,40,257,66] 13 := by
  apply FastRouting.sound _ _ [34,132,40,257,66] 13 (by decide) (choices 1) [1,4,16,64] r37572 c37572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22936
  · exact u22937
  · exact u22938
  · exact u22939

def r37573 : Route 9 := (fun mask => (mask,id))

def c37573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37573 : Upper (D 6) (R 6) [34,132,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,257,68] 13 (by decide) (choices 1) [1,2,16,64] r37573 c37573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22940
  · exact u22941
  · exact u22942
  · exact u22943

def r37574 : Route 9 := (fun mask => (mask,id))

def c37574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37574 : Upper (D 6) (R 6) [34,132,40,258,5] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,5] 13 (by decide) (choices 1) [1,16,64] r37574 c37574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22944
  · exact u22945
  · exact u22946

def r37575 : Route 9 := (fun mask => (mask,id))

def c37575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37575 : Upper (D 6) (R 6) [34,132,40,258,65] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,65] 13 (by decide) (choices 1) [1,4,16,64] r37575 c37575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22947
  · exact u22948
  · exact u22949
  · exact u22950

def r37576 : Route 9 := (fun mask => (mask,id))

def c37576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37576 : Upper (D 6) (R 6) [34,132,40,258,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258,68] 13 (by decide) (choices 1) [1,16,64] r37576 c37576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22951
  · exact u22952
  · exact u22953

def b37577 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 44 280 19 101 69 197 325), lower := (rows 35 134 44 280 19 32 64 128 256), losses := [] }

theorem u37577 : Upper (D 6) (R 6) [34,132,40,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37578 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 35 134 44 280 21 99 67 195 323), lower := (rows 35 134 44 280 21 32 64 128 256), losses := [] }

theorem u37578 : Upper (D 6) (R 6) [34,132,40,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37579 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 44 280 22 97 65 193 321), lower := (rows 35 134 44 280 22 32 64 128 256), losses := [] }

theorem u37579 : Upper (D 6) (R 6) [34,132,40,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37580 : Route 9 := (fun mask => (mask,id))

def c37580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37580 : Upper (D 6) (R 6) [34,132,40,272,65] 13 := by
  apply FastRouting.sound _ _ [34,132,40,272,65] 13 (by decide) (choices 1) [1,2,4,64] r37580 c37580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22954
  · exact u22955
  · exact u22956
  · exact u22957

def r37581 : Route 9 := (fun mask => (mask,id))

def c37581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37581 : Upper (D 6) (R 6) [34,132,40,272,66] 13 := by
  apply FastRouting.sound _ _ [34,132,40,272,66] 13 (by decide) (choices 1) [1,4,64] r37581 c37581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22958
  · exact u22959
  · exact u22960

def r37582 : Route 9 := (fun mask => (mask,id))

def c37582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37582 : Upper (D 6) (R 6) [34,132,40,272,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,272,68] 13 (by decide) (choices 1) [1,2,64] r37582 c37582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22961
  · exact u22962
  · exact u22963

def b37583 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 44 328 19 117 85 213 341), lower := (rows 35 134 44 328 19 32 64 128 256), losses := [] }

theorem u37583 : Upper (D 6) (R 6) [34,132,40,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37584 : Route 9 := (fun mask => (mask,id))

def c37584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37584 : Upper (D 6) (R 6) [34,132,40,320,5] 13 := by
  apply FastRouting.sound _ _ [34,132,40,320,5] 13 (by decide) (choices 1) [1,2,16,64] r37584 c37584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22964
  · exact u22965
  · exact u22966
  · exact u22967

def b37585 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 44 328 22 113 81 209 337), lower := (rows 35 134 44 328 22 32 64 128 256), losses := [] }

theorem u37585 : Upper (D 6) (R 6) [34,132,40,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37586 : Route 9 := (fun mask => (mask,id))

def c37586 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37586 : Upper (D 6) (R 6) [34,132,40,320,65] 13 := by
  apply FastRouting.sound _ _ [34,132,40,320,65] 13 (by decide) (choices 1) [1,2,4,16] r37586 c37586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22968
  · exact u22969
  · exact u22970
  · exact u22971

def r37587 : Route 9 := (fun mask => (mask,id))

def c37587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37587 : Upper (D 6) (R 6) [34,132,40,320,66] 13 := by
  apply FastRouting.sound _ _ [34,132,40,320,66] 13 (by decide) (choices 1) [1,4,16] r37587 c37587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22972
  · exact u22973
  · exact u22974

def r37588 : Route 9 := (fun mask => (mask,id))

def c37588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37588 : Upper (D 6) (R 6) [34,132,40,320,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,320,68] 13 (by decide) (choices 1) [1,2,16] r37588 c37588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22975
  · exact u22976
  · exact u22977

def b37589 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 369, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 134 76 13 19 368 368 496 368), lower := (rows 35 134 76 13 19 32 64 128 256), losses := [] }

theorem u37589 : Upper (D 6) (R 6) [34,132,72,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37590 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 134 76 13 49 370 338 466 338), lower := (rows 35 134 76 13 49 32 64 128 256), losses := [] }

theorem u37590 : Upper (D 6) (R 6) [34,132,72,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37591 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 134 76 13 50 369 337 465 337), lower := (rows 35 134 76 13 50 32 64 128 256), losses := [] }

theorem u37591 : Upper (D 6) (R 6) [34,132,72,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37592 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 12, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 35 134 76 13 81 306 370 434 306), lower := (rows 35 134 76 13 81 32 64 128 256), losses := [] }

theorem u37592 : Upper (D 6) (R 6) [34,132,72,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37593 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 13 82 305 369 433 305), lower := (rows 35 134 76 13 82 32 64 128 256), losses := [] }

theorem u37593 : Upper (D 6) (R 6) [34,132,72,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37594 : Route 9 := (fun mask => (mask,id))

def c37594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37594 : Upper (D 6) (R 6) [34,132,72,5,96] 13 := by
  apply FastRouting.sound _ _ [34,132,72,5,96] 13 (by decide) (choices 1) [1,2,16,256] r37594 c37594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22978
  · exact u22979
  · exact u22980
  · exact u22981

def r37595 : Route 9 := (fun mask => (mask,id))

def c37595 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37595 : Upper (D 6) (R 6) [34,132,72,5,257] 13 := by
  apply FastRouting.sound _ _ [34,132,72,5,257] 13 (by decide) (choices 1) [2,16,64] r37595 c37595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22982
  · exact u22983
  · exact u22984

def r37596 : Route 9 := (fun mask => (mask,id))

def c37596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37596 : Upper (D 6) (R 6) [34,132,72,5,258] 13 := by
  apply FastRouting.sound _ _ [34,132,72,5,258] 13 (by decide) (choices 1) [1,16,64] r37596 c37596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22985
  · exact u22986
  · exact u22987

def r37597 : Route 9 := (fun mask => (mask,id))

def c37597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37597 : Upper (D 6) (R 6) [34,132,72,5,288] 13 := by
  apply FastRouting.sound _ _ [34,132,72,5,288] 13 (by decide) (choices 1) [1,2,16,64] r37597 c37597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22988
  · exact u22989
  · exact u22990
  · exact u22991

def r37598 : Route 9 := (fun mask => (mask,id))

def c37598 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37598 : Upper (D 6) (R 6) [34,132,72,5,320] 13 := by
  apply FastRouting.sound _ _ [34,132,72,5,320] 13 (by decide) (choices 1) [1,2,16] r37598 c37598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22992
  · exact u22993
  · exact u22994

def b37599 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 76 25 19 356 356 484 356), lower := (rows 35 134 76 25 19 32 64 128 256), losses := [] }

theorem u37599 : Upper (D 6) (R 6) [34,132,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37600 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 76 25 21 354 354 482 354), lower := (rows 35 134 76 25 21 32 64 128 256), losses := [] }

theorem u37600 : Upper (D 6) (R 6) [34,132,72,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37601 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 76 25 22 353 353 481 353), lower := (rows 35 134 76 25 22 32 64 128 256), losses := [] }

theorem u37601 : Upper (D 6) (R 6) [34,132,72,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37602 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 76 25 49 358 326 454 326), lower := (rows 35 134 76 25 49 32 64 128 256), losses := [] }

theorem u37602 : Upper (D 6) (R 6) [34,132,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37603 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 76 25 50 357 325 453 325), lower := (rows 35 134 76 25 50 32 64 128 256), losses := [] }

theorem u37603 : Upper (D 6) (R 6) [34,132,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37604 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 76 25 52 355 323 451 323), lower := (rows 35 134 76 25 52 32 64 128 256), losses := [] }

theorem u37604 : Upper (D 6) (R 6) [34,132,72,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37605 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 12, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 35 134 76 25 81 294 358 422 294), lower := (rows 35 134 76 25 81 32 64 128 256), losses := [] }

theorem u37605 : Upper (D 6) (R 6) [34,132,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37606 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 356, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 134 76 25 82 293 357 421 293), lower := (rows 35 134 76 25 82 32 64 128 256), losses := [] }

theorem u37606 : Upper (D 6) (R 6) [34,132,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37607 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 76 25 84 291 355 419 291), lower := (rows 35 134 76 25 84 32 64 128 256), losses := [] }

theorem u37607 : Upper (D 6) (R 6) [34,132,72,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37608 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,6),(1,5),(1,6)], upper := (rows 35 134 76 25 112 295 327 391 263), lower := (rows 35 134 76 25 112 32 64 128 256), losses := [] }

theorem u37608 : Upper (D 6) (R 6) [34,132,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37609 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 76 25 273 102 102 230 358), lower := (rows 35 134 76 25 273 32 64 128 256), losses := [] }

theorem u37609 : Upper (D 6) (R 6) [34,132,72,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37610 : Route 9 := (fun mask => (mask,id))

def c37610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37610 : Upper (D 6) (R 6) [34,132,72,17,258] 13 := by
  apply FastRouting.sound _ _ [34,132,72,17,258] 13 (by decide) (choices 1) [1,4,64] r37610 c37610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22995
  · exact u22996
  · exact u22997

def r37611 : Route 9 := (fun mask => (mask,id))

def c37611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37611 : Upper (D 6) (R 6) [34,132,72,17,260] 13 := by
  apply FastRouting.sound _ _ [34,132,72,17,260] 13 (by decide) (choices 1) [1,2,64] r37611 c37611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22998
  · exact u22999
  · exact u23000

def r37612 : Route 9 := (fun mask => (mask,id))

def c37612 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37612 : Upper (D 6) (R 6) [34,132,72,17,288] 13 := by
  apply FastRouting.sound _ _ [34,132,72,17,288] 13 (by decide) (choices 1) [1,2,4,64] r37612 c37612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23001
  · exact u23002
  · exact u23003
  · exact u23004

def r37613 : Route 9 := (fun mask => (mask,id))

def c37613 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37613 : Upper (D 6) (R 6) [34,132,72,17,320] 13 := by
  apply FastRouting.sound _ _ [34,132,72,17,320] 13 (by decide) (choices 1) [1,2,4] r37613 c37613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23005
  · exact u23006
  · exact u23007

def r37614 : Route 9 := (fun mask => (mask,id))

def c37614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37614 : Upper (D 6) (R 6) [34,132,72,18,5] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,5] 13 (by decide) (choices 1) [1,64,256] r37614 c37614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23008
  · exact u23009
  · exact u23010

def b37615 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 76 26 49 357 325 453 325), lower := (rows 35 134 76 26 49 32 64 128 256), losses := [] }

theorem u37615 : Upper (D 6) (R 6) [34,132,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37616 : Route 9 := (fun mask => (mask,id))

def c37616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37616 : Upper (D 6) (R 6) [34,132,72,18,36] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,36] 13 (by decide) (choices 1) [1,64,256] r37616 c37616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23011
  · exact u23012
  · exact u23013

def r37617 : Route 9 := (fun mask => (mask,id))

def c37617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37617 : Upper (D 6) (R 6) [34,132,72,18,65] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,65] 13 (by decide) (choices 1) [1,4,256] r37617 c37617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23014
  · exact u23015
  · exact u23016

def b37618 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 76 26 84 289 353 417 289), lower := (rows 35 134 76 26 84 32 64 128 256), losses := [] }

theorem u37618 : Upper (D 6) (R 6) [34,132,72,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37619 : Route 9 := (fun mask => (mask,id))

def c37619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37619 : Upper (D 6) (R 6) [34,132,72,18,96] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,96] 13 (by decide) (choices 1) [1,4,256] r37619 c37619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23017
  · exact u23018
  · exact u23019

#print axioms u37619
end Delivery.IrregularNine14.P06
