import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0082
import IrregularNine14P09C0083

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7680 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0),(4,5)], upper := (rows 35 70 388 152 280 97 97 225 353), lower := (rows 35 70 388 152 280 32 64 128 256), losses := [] }

theorem u7680 : Upper (D 9) (R 9) [34,68,384,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7680 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7681 : Route 9 := (fun mask => (mask,id))

def c7681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7681 : Upper (D 9) (R 9) [34,68,384,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,288] 13 (by decide) (choices 1) [1,8,64] r7681 c7681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4927
  · exact u4928
  · exact u4929

def r7682 : Route 9 := (fun mask => (mask,id))

def c7682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7682 : Upper (D 9) (R 9) [34,68,384,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,320] 13 (by decide) (choices 1) [1,8] r7682 c7682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4930
  · exact u4931

def r7683 : Route 9 := (fun mask => (mask,id))

def c7683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7683 : Upper (D 9) (R 9) [34,68,384,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160,320] 13 (by decide) (choices 1) [1,8,16] r7683 c7683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4932
  · exact u4933
  · exact u4934

def b7684 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 480 }], pairs := [(2,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 13 13 112 432 464 400 400), lower := (rows 35 194 13 13 112 32 64 128 256), losses := [] }

theorem u7684 : Upper (D 9) (R 9) [34,192,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7684 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7685 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 480 }], pairs := [(2,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 13 13 304 496 464 464 464), lower := (rows 35 194 13 13 304 32 64 128 256), losses := [] }

theorem u7685 : Upper (D 9) (R 9) [34,192,9,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7685 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7686 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 480 }], pairs := [(2,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 13 13 336 432 496 432 432), lower := (rows 35 194 13 13 336 32 64 128 256), losses := [] }

theorem u7686 : Upper (D 9) (R 9) [34,192,9,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7686 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7687 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 25 52 480 448 448 448), lower := (rows 35 194 13 25 52 32 64 128 256), losses := [] }

theorem u7687 : Upper (D 9) (R 9) [34,192,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7687 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7688 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 25 84 416 480 416 416), lower := (rows 35 194 13 25 84 32 64 128 256), losses := [] }

theorem u7688 : Upper (D 9) (R 9) [34,192,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7688 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7689 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 4, targets := 128 }], pairs := [(1,0),(1,5),(2,5),(2,7),(4,0)], upper := (rows 35 194 13 25 112 420 452 388 388), lower := (rows 35 194 13 25 112 32 64 128 256), losses := [] }

theorem u7689 : Upper (D 9) (R 9) [34,192,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7689 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7690 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 25 276 480 480 480 480), lower := (rows 35 194 13 25 276 32 64 128 256), losses := [] }

theorem u7690 : Upper (D 9) (R 9) [34,192,9,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7690 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7691 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 4, targets := 448 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,6),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 25 304 484 452 452 452), lower := (rows 35 194 13 25 304 32 64 128 256), losses := [] }

theorem u7691 : Upper (D 9) (R 9) [34,192,9,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7691 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7692 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 25 336 420 484 420 420), lower := (rows 35 194 13 25 336 32 64 128 256), losses := [] }

theorem u7692 : Upper (D 9) (R 9) [34,192,9,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7692 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7693 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 28 49 480 448 448 448), lower := (rows 35 194 13 28 49 32 64 128 256), losses := [] }

theorem u7693 : Upper (D 9) (R 9) [34,192,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7693 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7694 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 12, targets := 416 }], pairs := [(2,5),(2,7),(2,8),(3,5),(3,7)], upper := (rows 35 194 13 28 81 416 480 416 416), lower := (rows 35 194 13 28 81 32 64 128 256), losses := [] }

theorem u7694 : Upper (D 9) (R 9) [34,192,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7694 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7695 : Route 9 := (fun mask => (mask,id))

def c7695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7695 : Upper (D 9) (R 9) [34,192,9,20,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,96] 13 (by decide) (choices 1) [1,128,256] r7695 c7695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4935
  · exact u4936
  · exact u4937

def b7696 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 13 28 208 289 353 417 289), lower := (rows 35 194 13 28 208 32 64 128 256), losses := [] }

theorem u7696 : Upper (D 9) (R 9) [34,192,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7696 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7697 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 12, targets := 480 }], pairs := [(2,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 13 28 273 480 480 480 480), lower := (rows 35 194 13 28 273 32 64 128 256), losses := [] }

theorem u7697 : Upper (D 9) (R 9) [34,192,9,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7697 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7698 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7698 : Upper (D 9) (R 9) [34,192,9,20,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,288] 13 (by decide) (choices 1) [1,64,256] r7698 c7698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4938
  · exact u4939
  · exact u4940

def r7699 : Route 9 := (fun mask => (mask,id))

def c7699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7699 : Upper (D 9) (R 9) [34,192,9,20,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,320] 13 (by decide) (choices 1) [1,128,256] r7699 c7699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4941
  · exact u4942
  · exact u4943

def b7700 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 41 84 432 464 400 400), lower := (rows 35 194 13 41 84 32 64 128 256), losses := [] }

theorem u7700 : Upper (D 9) (R 9) [34,192,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7700 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7701 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 41 276 496 464 464 464), lower := (rows 35 194 13 41 276 32 64 128 256), losses := [] }

theorem u7701 : Upper (D 9) (R 9) [34,192,9,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7701 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7702 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 41 336 436 468 404 404), lower := (rows 35 194 13 41 336 32 64 128 256), losses := [] }

theorem u7702 : Upper (D 9) (R 9) [34,192,9,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7702 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7703 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 44 81 432 464 400 400), lower := (rows 35 194 13 44 81 32 64 128 256), losses := [] }

theorem u7703 : Upper (D 9) (R 9) [34,192,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7703 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7704 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 44 273 496 464 464 464), lower := (rows 35 194 13 44 273 32 64 128 256), losses := [] }

theorem u7704 : Upper (D 9) (R 9) [34,192,9,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7704 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7705 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 44 336 433 465 401 401), lower := (rows 35 194 13 44 336 32 64 128 256), losses := [] }

theorem u7705 : Upper (D 9) (R 9) [34,192,9,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7705 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7706 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 428, targets := 64 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(2,6),(3,6),(4,5)], upper := (rows 35 194 13 56 81 420 452 388 388), lower := (rows 35 194 13 56 81 32 64 128 256), losses := [] }

theorem u7706 : Upper (D 9) (R 9) [34,192,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7706 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7707 : Route 9 := (fun mask => (mask,id))

def c7707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7707 : Upper (D 9) (R 9) [34,192,9,48,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,68] 13 (by decide) (choices 1) [1,128,256] r7707 c7707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4944
  · exact u4945
  · exact u4946

def b7708 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 13 56 208 293 325 389 261), lower := (rows 35 194 13 56 208 32 64 128 256), losses := [] }

theorem u7708 : Upper (D 9) (R 9) [34,192,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7708 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7709 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7709 : Upper (D 9) (R 9) [34,192,9,48,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,257] 13 (by decide) (choices 1) [4,64,256] r7709 c7709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4947
  · exact u4948
  · exact u4949

def r7710 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7710 : Upper (D 9) (R 9) [34,192,9,48,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,260] 13 (by decide) (choices 1) [1,64,256] r7710 c7710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4950
  · exact u4951
  · exact u4952

def r7711 : Route 9 := (fun mask => (mask,id))

def c7711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7711 : Upper (D 9) (R 9) [34,192,9,48,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,320] 13 (by decide) (choices 1) [1,4,128,256] r7711 c7711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4953
  · exact u4954
  · exact u4955
  · exact u4956

def b7712 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 73 52 432 464 400 400), lower := (rows 35 194 13 73 52 32 64 128 256), losses := [] }

theorem u7712 : Upper (D 9) (R 9) [34,192,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7712 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7713 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 73 148 304 368 432 304), lower := (rows 35 194 13 73 148 32 64 128 256), losses := [] }

theorem u7713 : Upper (D 9) (R 9) [34,192,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7713 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7714 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 73 176 308 340 404 276), lower := (rows 35 194 13 73 176 32 64 128 256), losses := [] }

theorem u7714 : Upper (D 9) (R 9) [34,192,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7715 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 73 276 432 496 432 432), lower := (rows 35 194 13 73 276 32 64 128 256), losses := [] }

theorem u7715 : Upper (D 9) (R 9) [34,192,9,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7715 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7716 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 73 304 436 468 404 404), lower := (rows 35 194 13 73 304 32 64 128 256), losses := [] }

theorem u7716 : Upper (D 9) (R 9) [34,192,9,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7716 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7717 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 73 400 308 372 436 308), lower := (rows 35 194 13 73 400 32 64 128 256), losses := [] }

theorem u7717 : Upper (D 9) (R 9) [34,192,9,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7717 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7718 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 194 13 76 49 432 464 400 400), lower := (rows 35 194 13 76 49 32 64 128 256), losses := [] }

theorem u7718 : Upper (D 9) (R 9) [34,192,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7718 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7719 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 364, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(2,7),(3,7),(4,6)], upper := (rows 35 194 13 76 145 304 368 432 304), lower := (rows 35 194 13 76 145 32 64 128 256), losses := [] }

theorem u7719 : Upper (D 9) (R 9) [34,192,9,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7719 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7720 : Route 9 := (fun mask => (mask,id))

def c7720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7720 : Upper (D 9) (R 9) [34,192,9,68,160] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,160] 13 (by decide) (choices 1) [1,16,256] r7720 c7720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4957
  · exact u4958
  · exact u4959

def r7721 : Route 9 := (fun mask => (mask,id))

def c7721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7721 : Upper (D 9) (R 9) [34,192,9,68,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,257] 13 (by decide) (choices 1) [16,128,256] r7721 c7721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4960
  · exact u4961
  · exact u4962

def r7722 : Route 9 := (fun mask => (mask,id))

def c7722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7722 : Upper (D 9) (R 9) [34,192,9,68,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,288] 13 (by decide) (choices 1) [1,16,128,256] r7722 c7722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4963
  · exact u4964
  · exact u4965
  · exact u4966

def r7723 : Route 9 := (fun mask => (mask,id))

def c7723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7723 : Upper (D 9) (R 9) [34,192,9,68,384] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,384] 13 (by decide) (choices 1) [1,16,256] r7723 c7723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4967
  · exact u4968
  · exact u4969

def b7724 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 194 13 88 49 420 452 388 388), lower := (rows 35 194 13 88 49 32 64 128 256), losses := [] }

theorem u7724 : Upper (D 9) (R 9) [34,192,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7724 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7725 : Route 9 := (fun mask => (mask,id))

def c7725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7725 : Upper (D 9) (R 9) [34,192,9,80,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,36] 13 (by decide) (choices 1) [1,128,256] r7725 c7725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4970
  · exact u4971
  · exact u4972

def r7726 : Route 9 := (fun mask => (mask,id))

def c7726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7726 : Upper (D 9) (R 9) [34,192,9,80,129] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,129] 13 (by decide) (choices 1) [4,256] r7726 c7726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4973
  · exact u4974

def r7727 : Route 9 := (fun mask => (mask,id))

def c7727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7727 : Upper (D 9) (R 9) [34,192,9,80,132] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,132] 13 (by decide) (choices 1) [1,256] r7727 c7727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4975
  · exact u4976

def r7728 : Route 9 := (fun mask => (mask,id))

def c7728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7728 : Upper (D 9) (R 9) [34,192,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,160] 13 (by decide) (choices 1) [1,4,256] r7728 c7728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4977
  · exact u4978
  · exact u4979

def r7729 : Route 9 := (fun mask => (mask,id))

def c7729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7729 : Upper (D 9) (R 9) [34,192,9,80,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,257] 13 (by decide) (choices 1) [4,128,256] r7729 c7729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4980
  · exact u4981
  · exact u4982

def r7730 : Route 9 := (fun mask => (mask,id))

def c7730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7730 : Upper (D 9) (R 9) [34,192,9,80,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,260] 13 (by decide) (choices 1) [1,128,256] r7730 c7730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4983
  · exact u4984
  · exact u4985

def r7731 : Route 9 := (fun mask => (mask,id))

def c7731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7731 : Upper (D 9) (R 9) [34,192,9,80,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,288] 13 (by decide) (choices 1) [1,4,128,256] r7731 c7731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4986
  · exact u4987
  · exact u4988
  · exact u4989

def r7732 : Route 9 := (fun mask => (mask,id))

def c7732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7732 : Upper (D 9) (R 9) [34,192,9,80,384] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384] 13 (by decide) (choices 1) [1,4,256] r7732 c7732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4990
  · exact u4991
  · exact u4992

def b7733 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 364, targets := 128 },{ cop := 2, region := 400, targets := 64 }], pairs := [(1,5),(2,7),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 104 145 308 340 404 276), lower := (rows 35 194 13 104 145 32 64 128 256), losses := [] }

theorem u7733 : Upper (D 9) (R 9) [34,192,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7733 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7734 : Route 9 := (fun mask => (mask,id))

def c7734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7734 : Upper (D 9) (R 9) [34,192,9,96,132] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,132] 13 (by decide) (choices 1) [1,16,256] r7734 c7734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4993
  · exact u4994
  · exact u4995

def r7735 : Route 9 := (fun mask => (mask,id))

def c7735 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7735 : Upper (D 9) (R 9) [34,192,9,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,257] 13 (by decide) (choices 1) [4,16,128,256] r7735 c7735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4996
  · exact u4997
  · exact u4998
  · exact u4999

def r7736 : Route 9 := (fun mask => (mask,id))

def c7736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7736 : Upper (D 9) (R 9) [34,192,9,96,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,260] 13 (by decide) (choices 1) [1,16,128,256] r7736 c7736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5000
  · exact u5001
  · exact u5002
  · exact u5003

def r7737 : Route 9 := (fun mask => (mask,id))

def c7737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7737 : Upper (D 9) (R 9) [34,192,9,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,384] 13 (by decide) (choices 1) [1,4,16,256] r7737 c7737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5004
  · exact u5005
  · exact u5006
  · exact u5007

def b7738 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 13 200 52 305 337 401 273), lower := (rows 35 194 13 200 52 32 64 128 256), losses := [] }

theorem u7738 : Upper (D 9) (R 9) [34,192,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7738 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7739 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 13 200 273 308 372 436 308), lower := (rows 35 194 13 200 273 32 64 128 256), losses := [] }

theorem u7739 : Upper (D 9) (R 9) [34,192,9,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7739 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7739
end Delivery.IrregularNine14.P09
