import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0083
import IrregularNine14P09C0084
import IrregularNine14P09C0085

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7740 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 13 200 276 305 369 433 305), lower := (rows 35 194 13 200 276 32 64 128 256), losses := [] }

theorem u7740 : Upper (D 9) (R 9) [34,192,9,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7740 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7741 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 13 200 304 309 341 405 277), lower := (rows 35 194 13 200 304 32 64 128 256), losses := [] }

theorem u7741 : Upper (D 9) (R 9) [34,192,9,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7741 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7742 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 265 52 496 464 464 464), lower := (rows 35 194 13 265 52 32 64 128 256), losses := [] }

theorem u7742 : Upper (D 9) (R 9) [34,192,9,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7742 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7743 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 265 84 432 496 432 432), lower := (rows 35 194 13 265 84 32 64 128 256), losses := [] }

theorem u7743 : Upper (D 9) (R 9) [34,192,9,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7743 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7744 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 265 112 436 468 404 404), lower := (rows 35 194 13 265 112 32 64 128 256), losses := [] }

theorem u7744 : Upper (D 9) (R 9) [34,192,9,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7744 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7745 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5),(4,6)], upper := (rows 35 194 13 265 276 240 240 240 496), lower := (rows 35 194 13 265 276 32 64 128 256), losses := [] }

theorem u7745 : Upper (D 9) (R 9) [34,192,9,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7745 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7746 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 265 304 244 212 212 468), lower := (rows 35 194 13 265 304 32 64 128 256), losses := [] }

theorem u7746 : Upper (D 9) (R 9) [34,192,9,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7746 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7747 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 265 336 180 244 180 436), lower := (rows 35 194 13 265 336 32 64 128 256), losses := [] }

theorem u7747 : Upper (D 9) (R 9) [34,192,9,257,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7747 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7748 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 194 13 268 49 496 464 464 464), lower := (rows 35 194 13 268 49 32 64 128 256), losses := [] }

theorem u7748 : Upper (D 9) (R 9) [34,192,9,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7748 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7749 : Route 9 := (fun mask => (mask,id))

def c7749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7749 : Upper (D 9) (R 9) [34,192,9,260,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,65] 13 (by decide) (choices 1) [16,128,256] r7749 c7749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5008
  · exact u5009
  · exact u5010

def r7750 : Route 9 := (fun mask => (mask,id))

def c7750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7750 : Upper (D 9) (R 9) [34,192,9,260,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,96] 13 (by decide) (choices 1) [1,16,128,256] r7750 c7750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5011
  · exact u5012
  · exact u5013
  · exact u5014

def b7751 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 13 268 208 305 369 433 305), lower := (rows 35 194 13 268 208 32 64 128 256), losses := [] }

theorem u7751 : Upper (D 9) (R 9) [34,192,9,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7751 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7752 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5),(3,6)], upper := (rows 35 194 13 268 273 240 240 240 496), lower := (rows 35 194 13 268 273 32 64 128 256), losses := [] }

theorem u7752 : Upper (D 9) (R 9) [34,192,9,260,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7752 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7753 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7753 : Upper (D 9) (R 9) [34,192,9,260,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,288] 13 (by decide) (choices 1) [1,16,64] r7753 c7753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5015
  · exact u5016
  · exact u5017

def r7754 : Route 9 := (fun mask => (mask,id))

def c7754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7754 : Upper (D 9) (R 9) [34,192,9,260,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260,320] 13 (by decide) (choices 1) [1,16,128] r7754 c7754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5018
  · exact u5019
  · exact u5020

def b7755 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 194 13 280 49 484 452 452 452), lower := (rows 35 194 13 280 49 32 64 128 256), losses := [] }

theorem u7755 : Upper (D 9) (R 9) [34,192,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7755 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7756 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7756 : Upper (D 9) (R 9) [34,192,9,272,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,36] 13 (by decide) (choices 1) [1,64,256] r7756 c7756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5021
  · exact u5022
  · exact u5023

def r7757 : Route 9 := (fun mask => (mask,id))

def c7757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7757 : Upper (D 9) (R 9) [34,192,9,272,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,65] 13 (by decide) (choices 1) [4,128,256] r7757 c7757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5024
  · exact u5025
  · exact u5026

def r7758 : Route 9 := (fun mask => (mask,id))

def c7758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7758 : Upper (D 9) (R 9) [34,192,9,272,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,68] 13 (by decide) (choices 1) [1,128,256] r7758 c7758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5027
  · exact u5028
  · exact u5029

def r7759 : Route 9 := (fun mask => (mask,id))

def c7759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7759 : Upper (D 9) (R 9) [34,192,9,272,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,96] 13 (by decide) (choices 1) [1,4,128,256] r7759 c7759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5030
  · exact u5031
  · exact u5032
  · exact u5033

def b7760 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 13 280 208 293 357 421 293), lower := (rows 35 194 13 280 208 32 64 128 256), losses := [] }

theorem u7760 : Upper (D 9) (R 9) [34,192,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7760 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7761 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5),(3,6)], upper := (rows 35 194 13 280 273 228 228 228 484), lower := (rows 35 194 13 280 273 32 64 128 256), losses := [] }

theorem u7761 : Upper (D 9) (R 9) [34,192,9,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7761 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7762 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 227, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 13 280 276 225 225 225 481), lower := (rows 35 194 13 280 276 32 64 128 256), losses := [] }

theorem u7762 : Upper (D 9) (R 9) [34,192,9,272,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7762 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7763 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 13 280 304 229 197 197 453), lower := (rows 35 194 13 280 304 32 64 128 256), losses := [] }

theorem u7763 : Upper (D 9) (R 9) [34,192,9,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7763 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7764 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 13 280 336 165 229 165 421), lower := (rows 35 194 13 280 336 32 64 128 256), losses := [] }

theorem u7764 : Upper (D 9) (R 9) [34,192,9,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7764 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7765 : Route 9 := (fun mask => (mask,id))

def c7765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7765 : Upper (D 9) (R 9) [34,192,9,288,65] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,65] 13 (by decide) (choices 1) [4,16,128,256] r7765 c7765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5034
  · exact u5035
  · exact u5036
  · exact u5037

def r7766 : Route 9 := (fun mask => (mask,id))

def c7766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7766 : Upper (D 9) (R 9) [34,192,9,288,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,68] 13 (by decide) (choices 1) [1,16,128,256] r7766 c7766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5038
  · exact u5039
  · exact u5040
  · exact u5041

def b7767 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 13 296 208 309 341 405 277), lower := (rows 35 194 13 296 208 32 64 128 256), losses := [] }

theorem u7767 : Upper (D 9) (R 9) [34,192,9,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7767 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7768 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7768 : Upper (D 9) (R 9) [34,192,9,288,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,257] 13 (by decide) (choices 1) [4,16,64] r7768 c7768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5042
  · exact u5043
  · exact u5044

def r7769 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7769 : Upper (D 9) (R 9) [34,192,9,288,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,260] 13 (by decide) (choices 1) [1,16,64] r7769 c7769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5045
  · exact u5046
  · exact u5047

def r7770 : Route 9 := (fun mask => (mask,id))

def c7770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7770 : Upper (D 9) (R 9) [34,192,9,288,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288,320] 13 (by decide) (choices 1) [1,4,16,128] r7770 c7770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5048
  · exact u5049
  · exact u5050
  · exact u5051

def b7771 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 194 13 328 49 436 468 404 404), lower := (rows 35 194 13 328 49 32 64 128 256), losses := [] }

theorem u7771 : Upper (D 9) (R 9) [34,192,9,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7771 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7772 : Route 9 := (fun mask => (mask,id))

def c7772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7772 : Upper (D 9) (R 9) [34,192,9,320,36] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,36] 13 (by decide) (choices 1) [1,16,128,256] r7772 c7772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5052
  · exact u5053
  · exact u5054
  · exact u5055

def r7773 : Route 9 := (fun mask => (mask,id))

def c7773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7773 : Upper (D 9) (R 9) [34,192,9,320,129] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,129] 13 (by decide) (choices 1) [4,16,256] r7773 c7773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5056
  · exact u5057
  · exact u5058

def r7774 : Route 9 := (fun mask => (mask,id))

def c7774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7774 : Upper (D 9) (R 9) [34,192,9,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,132] 13 (by decide) (choices 1) [1,16,256] r7774 c7774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5059
  · exact u5060
  · exact u5061

def r7775 : Route 9 := (fun mask => (mask,id))

def c7775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7775 : Upper (D 9) (R 9) [34,192,9,320,160] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,160] 13 (by decide) (choices 1) [1,4,16,256] r7775 c7775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5062
  · exact u5063
  · exact u5064
  · exact u5065

def r7776 : Route 9 := (fun mask => (mask,id))

def c7776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7776 : Upper (D 9) (R 9) [34,192,9,320,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,257] 13 (by decide) (choices 1) [4,16,128] r7776 c7776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5066
  · exact u5067
  · exact u5068

def r7777 : Route 9 := (fun mask => (mask,id))

def c7777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7777 : Upper (D 9) (R 9) [34,192,9,320,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,260] 13 (by decide) (choices 1) [1,16,128] r7777 c7777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5069
  · exact u5070
  · exact u5071

def r7778 : Route 9 := (fun mask => (mask,id))

def c7778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7778 : Upper (D 9) (R 9) [34,192,9,320,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,288] 13 (by decide) (choices 1) [1,4,16,128] r7778 c7778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5072
  · exact u5073
  · exact u5074
  · exact u5075

def r7779 : Route 9 := (fun mask => (mask,id))

def c7779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7779 : Upper (D 9) (R 9) [34,192,9,320,384] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,384] 13 (by decide) (choices 1) [1,4,16] r7779 c7779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5076
  · exact u5077
  · exact u5078

def b7780 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 194 28 41 81 420 452 388 388), lower := (rows 35 194 28 41 81 32 64 128 256), losses := [] }

theorem u7780 : Upper (D 9) (R 9) [34,192,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7780 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7781 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 194 28 41 84 417 449 385 385), lower := (rows 35 194 28 41 84 32 64 128 256), losses := [] }

theorem u7781 : Upper (D 9) (R 9) [34,192,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7781 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7782 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 194 28 41 273 484 452 452 452), lower := (rows 35 194 28 41 273 32 64 128 256), losses := [] }

theorem u7782 : Upper (D 9) (R 9) [34,192,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7782 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7783 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 194 28 41 276 481 449 449 449), lower := (rows 35 194 28 41 276 32 64 128 256), losses := [] }

theorem u7783 : Upper (D 9) (R 9) [34,192,24,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7783 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7784 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 194 28 41 336 421 453 389 389), lower := (rows 35 194 28 41 336 32 64 128 256), losses := [] }

theorem u7784 : Upper (D 9) (R 9) [34,192,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7784 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7785 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 428, targets := 64 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(3,6),(4,5)], upper := (rows 35 194 28 44 81 417 449 385 385), lower := (rows 35 194 28 44 81 32 64 128 256), losses := [] }

theorem u7785 : Upper (D 9) (R 9) [34,192,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7785 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7786 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 16, targets := 289 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5),(4,8)], upper := (rows 35 194 28 44 208 289 321 385 257), lower := (rows 35 194 28 44 208 32 64 128 256), losses := [] }

theorem u7786 : Upper (D 9) (R 9) [34,192,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7786 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7787 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7787 : Upper (D 9) (R 9) [34,192,24,36,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,36,257] 13 (by decide) (choices 1) [1,64,256] r7787 c7787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5079
  · exact u5080
  · exact u5081

def r7788 : Route 9 := (fun mask => (mask,id))

def c7788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7788 : Upper (D 9) (R 9) [34,192,24,36,320] 13 := by
  apply FastRouting.sound _ _ [34,192,24,36,320] 13 (by decide) (choices 1) [1,128,256] r7788 c7788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5082
  · exact u5083
  · exact u5084

def b7789 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 364, targets := 128 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,6),(2,7),(3,7),(4,6)], upper := (rows 35 194 28 73 145 292 356 420 292), lower := (rows 35 194 28 73 145 32 64 128 256), losses := [] }

theorem u7789 : Upper (D 9) (R 9) [34,192,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7789 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7790 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 297, targets := 128 },{ cop := 3, region := 436, targets := 64 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(2,6),(3,7),(4,6)], upper := (rows 35 194 28 73 148 289 353 417 289), lower := (rows 35 194 28 73 148 32 64 128 256), losses := [] }

theorem u7790 : Upper (D 9) (R 9) [34,192,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7790 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7791 : Route 9 := (fun mask => (mask,id))

def c7791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7791 : Upper (D 9) (R 9) [34,192,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,160] 13 (by decide) (choices 1) [1,4,256] r7791 c7791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5085
  · exact u5086
  · exact u5087

def r7792 : Route 9 := (fun mask => (mask,id))

def c7792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7792 : Upper (D 9) (R 9) [34,192,24,65,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,257] 13 (by decide) (choices 1) [4,128,256] r7792 c7792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5088
  · exact u5089
  · exact u5090

def r7793 : Route 9 := (fun mask => (mask,id))

def c7793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7793 : Upper (D 9) (R 9) [34,192,24,65,260] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,260] 13 (by decide) (choices 1) [1,128,256] r7793 c7793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5091
  · exact u5092
  · exact u5093

def r7794 : Route 9 := (fun mask => (mask,id))

def c7794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7794 : Upper (D 9) (R 9) [34,192,24,65,288] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,288] 13 (by decide) (choices 1) [1,4,128,256] r7794 c7794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5094
  · exact u5095
  · exact u5096
  · exact u5097

def r7795 : Route 9 := (fun mask => (mask,id))

def c7795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7795 : Upper (D 9) (R 9) [34,192,24,65,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,384] 13 (by decide) (choices 1) [1,4,256] r7795 c7795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5098
  · exact u5099
  · exact u5100

def r7796 : Route 9 := (fun mask => (mask,id))

def c7796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7796 : Upper (D 9) (R 9) [34,192,24,68,160] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,160] 13 (by decide) (choices 1) [1,256] r7796 c7796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5101
  · exact u5102

def r7797 : Route 9 := (fun mask => (mask,id))

def c7797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7797 : Upper (D 9) (R 9) [34,192,24,68,257] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,257] 13 (by decide) (choices 1) [1,128,256] r7797 c7797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5103
  · exact u5104
  · exact u5105

def r7798 : Route 9 := (fun mask => (mask,id))

def c7798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7798 : Upper (D 9) (R 9) [34,192,24,68,288] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,288] 13 (by decide) (choices 1) [1,128,256] r7798 c7798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5106
  · exact u5107
  · exact u5108

def r7799 : Route 9 := (fun mask => (mask,id))

def c7799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7799 : Upper (D 9) (R 9) [34,192,24,68,384] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,384] 13 (by decide) (choices 1) [1,256] r7799 c7799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5109
  · exact u5110

#print axioms u7799
end Delivery.IrregularNine14.P09
