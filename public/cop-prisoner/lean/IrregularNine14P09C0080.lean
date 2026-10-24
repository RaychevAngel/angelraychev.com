import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0026
import IrregularNine14P09C0027

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4800 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 164 73 280 48 449 385 385), lower := (rows 35 70 164 73 280 48 64 128 256), losses := [] }

theorem u4800 : Upper (D 9) (R 9) [34,68,160,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4800 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4801 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 73 280 160 337 401 273), lower := (rows 35 70 164 73 280 160 64 128 256), losses := [] }

theorem u4801 : Upper (D 9) (R 9) [34,68,160,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4801 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4802 : Route 9 := (fun mask => (mask,id))

def c4802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4802 : Upper (D 9) (R 9) [34,68,160,65,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,264,256] 13 (by decide) (choices 1) [1,16,128] r4802 c4802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1601
  · exact u1602
  · exact u1603

def b4803 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(3,5),(3,7),(3,8)], upper := (rows 35 70 164 73 400 33 344 408 280), lower := (rows 35 70 164 73 400 33 64 128 256), losses := [] }

theorem u4803 : Upper (D 9) (R 9) [34,68,160,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4803 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4804 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 164 73 400 40 337 401 273), lower := (rows 35 70 164 73 400 40 64 128 256), losses := [] }

theorem u4804 : Upper (D 9) (R 9) [34,68,160,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4804 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4805 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 70 164 73 400 48 329 393 265), lower := (rows 35 70 164 73 400 48 64 128 256), losses := [] }

theorem u4805 : Upper (D 9) (R 9) [34,68,160,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4805 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4806 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 164 73 400 288 89 153 281), lower := (rows 35 70 164 73 400 288 64 128 256), losses := [] }

theorem u4806 : Upper (D 9) (R 9) [34,68,160,65,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4806 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4807 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 88 145 33 328 392 264), lower := (rows 35 70 164 88 145 33 64 128 256), losses := [] }

theorem u4807 : Upper (D 9) (R 9) [34,68,160,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4807 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4808 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 164 88 145 40 321 385 257), lower := (rows 35 70 164 88 145 40 64 128 256), losses := [] }

theorem u4808 : Upper (D 9) (R 9) [34,68,160,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4808 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4809 : Route 9 := (fun mask => (mask,id))

def c4809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4809 : Upper (D 9) (R 9) [34,68,160,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,129,256] 13 (by decide) (choices 1) [1,8,256] r4809 c4809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1604
  · exact u1605
  · exact u1606

def b4810 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 88 273 33 456 392 392), lower := (rows 35 70 164 88 273 33 64 128 256), losses := [] }

theorem u4810 : Upper (D 9) (R 9) [34,68,160,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4810 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4811 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 164 88 273 40 449 385 385), lower := (rows 35 70 164 88 273 40 64 128 256), losses := [] }

theorem u4811 : Upper (D 9) (R 9) [34,68,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4811 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4812 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 88 273 160 329 393 265), lower := (rows 35 70 164 88 273 160 64 128 256), losses := [] }

theorem u4812 : Upper (D 9) (R 9) [34,68,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4812 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4813 : Route 9 := (fun mask => (mask,id))

def c4813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4813 : Upper (D 9) (R 9) [34,68,160,80,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257,256] 13 (by decide) (choices 1) [1,8,128] r4813 c4813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1607
  · exact u1608
  · exact u1609

def b4814 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 280 33 449 385 385), lower := (rows 35 70 164 88 280 33 64 128 256), losses := [] }

theorem u4814 : Upper (D 9) (R 9) [34,68,160,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4814 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4815 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 88 280 160 321 385 257), lower := (rows 35 70 164 88 280 160 64 128 256), losses := [] }

theorem u4815 : Upper (D 9) (R 9) [34,68,160,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4815 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4816 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 35 70 164 88 280 288 193 129 385), lower := (rows 35 70 164 88 280 288 64 128 256), losses := [] }

theorem u4816 : Upper (D 9) (R 9) [34,68,160,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4816 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4817 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 88 400 33 329 393 265), lower := (rows 35 70 164 88 400 33 64 128 256), losses := [] }

theorem u4817 : Upper (D 9) (R 9) [34,68,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4817 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4818 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 164 88 400 40 321 385 257), lower := (rows 35 70 164 88 400 40 64 128 256), losses := [] }

theorem u4818 : Upper (D 9) (R 9) [34,68,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4818 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4819 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 65 }], pairs := [(1,0),(2,0),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 400 288 73 137 265), lower := (rows 35 70 164 88 400 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 304 64 128 256), good := (rows 34 70 164 126 436 288 64 128 288) }] }

theorem u4819 : Upper (D 9) (R 9) [34,68,160,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4819 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4820 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 164 137 273 40 336 464 336), lower := (rows 35 70 164 137 273 40 64 128 256), losses := [] }

theorem u4820 : Upper (D 9) (R 9) [34,68,160,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4820 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4821 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 336, targets := 128 }], pairs := [(1,5),(3,5),(4,5),(4,7)], upper := (rows 35 70 164 137 273 48 328 456 328), lower := (rows 35 70 164 137 273 48 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 25 25 0 121 185 313), good := (rows 475 70 454 473 473 472 64 128 256) }] }

theorem u4821 : Upper (D 9) (R 9) [34,68,160,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4821 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4822 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 137 273 96 344 408 280), lower := (rows 35 70 164 137 273 96 64 128 256), losses := [] }

theorem u4822 : Upper (D 9) (R 9) [34,68,160,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4822 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4823 : Route 9 := (fun mask => (mask,id))

def c4823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4823 : Upper (D 9) (R 9) [34,68,160,129,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,257,256] 13 (by decide) (choices 1) [8,16] r4823 c4823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1610
  · exact u1611

def b4824 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 137 280 33 336 464 336), lower := (rows 35 70 164 137 280 33 64 128 256), losses := [] }

theorem u4824 : Upper (D 9) (R 9) [34,68,160,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4824 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4825 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 164 137 280 48 321 449 321), lower := (rows 35 70 164 137 280 48 64 128 256), losses := [] }

theorem u4825 : Upper (D 9) (R 9) [34,68,160,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4825 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4826 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 137 280 96 337 401 273), lower := (rows 35 70 164 137 280 96 64 128 256), losses := [] }

theorem u4826 : Upper (D 9) (R 9) [34,68,160,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4826 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4827 : Route 9 := (fun mask => (mask,id))

def c4827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4827 : Upper (D 9) (R 9) [34,68,160,129,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,264,256] 13 (by decide) (choices 1) [1,16] r4827 c4827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1612
  · exact u1613

def b4828 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 137 336 33 344 408 280), lower := (rows 35 70 164 137 336 33 64 128 256), losses := [] }

theorem u4828 : Upper (D 9) (R 9) [34,68,160,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4828 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4829 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 164 137 336 40 337 401 273), lower := (rows 35 70 164 137 336 40 64 128 256), losses := [] }

theorem u4829 : Upper (D 9) (R 9) [34,68,160,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4829 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4830 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(3,6),(4,5)], upper := (rows 35 70 164 137 336 48 329 393 265), lower := (rows 35 70 164 137 336 48 64 128 256), losses := [] }

theorem u4830 : Upper (D 9) (R 9) [34,68,160,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4830 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4831 : Route 9 := (fun mask => (mask,id))

def c4831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4831 : Upper (D 9) (R 9) [34,68,160,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,320,256] 13 (by decide) (choices 1) [1,8,16] r4831 c4831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1614
  · exact u1615
  · exact u1616

def b4832 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 152 273 33 328 456 328), lower := (rows 35 70 164 152 273 33 64 128 256), losses := [] }

theorem u4832 : Upper (D 9) (R 9) [34,68,160,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4832 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4833 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 164 152 273 40 321 449 321), lower := (rows 35 70 164 152 273 40 64 128 256), losses := [] }

theorem u4833 : Upper (D 9) (R 9) [34,68,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4833 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4834 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 152 273 96 329 393 265), lower := (rows 35 70 164 152 273 96 64 128 256), losses := [] }

theorem u4834 : Upper (D 9) (R 9) [34,68,160,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4834 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4835 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 200, targets := 256 }], pairs := [(2,0),(2,6),(3,5),(3,8),(4,5)], upper := (rows 35 70 164 152 273 288 73 201 329), lower := (rows 35 70 164 152 273 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 34 70 164 188 304 288 64 128 288) },{ target := 6, region := (rows 1 2 12 8 16 304 0 128 256), good := (rows 35 6 164 188 305 288 0 128 288) }] }

theorem u4835 : Upper (D 9) (R 9) [34,68,160,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4835 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4836 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 152 280 33 321 449 321), lower := (rows 35 70 164 152 280 33 64 128 256), losses := [] }

theorem u4836 : Upper (D 9) (R 9) [34,68,160,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4836 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4837 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 152 280 96 321 385 257), lower := (rows 35 70 164 152 280 96 64 128 256), losses := [] }

theorem u4837 : Upper (D 9) (R 9) [34,68,160,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4837 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4838 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 35 70 164 152 280 288 65 193 321), lower := (rows 35 70 164 152 280 288 64 128 256), losses := [] }

theorem u4838 : Upper (D 9) (R 9) [34,68,160,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4838 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4839 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 152 336 33 329 393 265), lower := (rows 35 70 164 152 336 33 64 128 256), losses := [] }

theorem u4839 : Upper (D 9) (R 9) [34,68,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4839 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4840 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 164 152 336 40 321 385 257), lower := (rows 35 70 164 152 336 40 64 128 256), losses := [] }

theorem u4840 : Upper (D 9) (R 9) [34,68,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4840 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4841 : Route 9 := (fun mask => (mask,id))

def c4841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4841 : Upper (D 9) (R 9) [34,68,160,144,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,320,256] 13 (by decide) (choices 1) [1,8] r4841 c4841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1617
  · exact u1618

def b4842 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 200 273 33 344 408 280), lower := (rows 35 70 164 200 273 33 64 128 256), losses := [] }

theorem u4842 : Upper (D 9) (R 9) [34,68,160,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4842 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4843 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 39, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 35 70 164 200 273 40 337 401 273), lower := (rows 35 70 164 200 273 40 64 128 256), losses := [] }

theorem u4843 : Upper (D 9) (R 9) [34,68,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4843 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4844 : Route 9 := (fun mask => (mask,id))

def c4844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4844 : Upper (D 9) (R 9) [34,68,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,16] 13 (by decide) (choices 1) [1,8,256] r4844 c4844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1619
  · exact u1620
  · exact u1621

def r4845 : Route 9 := (fun mask => (mask,id))

def c4845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4845 : Upper (D 9) (R 9) [34,68,160,192,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,256] 13 (by decide) (choices 1) [1,8,16] r4845 c4845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1622
  · exact u1623
  · exact u1624

def b4846 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 200 280 33 337 401 273), lower := (rows 35 70 164 200 280 33 64 128 256), losses := [] }

theorem u4846 : Upper (D 9) (R 9) [34,68,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4846 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4847 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 164 200 280 48 321 385 257), lower := (rows 35 70 164 200 280 48 64 128 256), losses := [] }

theorem u4847 : Upper (D 9) (R 9) [34,68,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4847 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4848 : Route 9 := (fun mask => (mask,id))

def c4848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4848 : Upper (D 9) (R 9) [34,68,160,192,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,264,256] 13 (by decide) (choices 1) [1,16] r4848 c4848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1625
  · exact u1626

def b4849 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 265 336 33 216 152 408), lower := (rows 35 70 164 265 336 33 64 128 256), losses := [] }

theorem u4849 : Upper (D 9) (R 9) [34,68,160,257,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4849 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4850 : Route 9 := (fun mask => (mask,id))

def c4850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4850 : Upper (D 9) (R 9) [34,68,160,257,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,320,8] 13 (by decide) (choices 1) [1,16,128] r4850 c4850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1627
  · exact u1628
  · exact u1629

def b4851 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(3,6),(4,5)], upper := (rows 35 70 164 265 336 48 201 137 393), lower := (rows 35 70 164 265 336 48 64 128 256), losses := [] }

theorem u4851 : Upper (D 9) (R 9) [34,68,160,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4851 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4852 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 70 164 265 336 160 89 153 281), lower := (rows 35 70 164 265 336 160 64 128 256), losses := [] }

theorem u4852 : Upper (D 9) (R 9) [34,68,160,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4852 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4853 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 265 400 33 88 216 344), lower := (rows 35 70 164 265 400 33 64 128 256), losses := [] }

theorem u4853 : Upper (D 9) (R 9) [34,68,160,257,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4853 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4854 : Route 9 := (fun mask => (mask,id))

def c4854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4854 : Upper (D 9) (R 9) [34,68,160,257,384,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,384,8] 13 (by decide) (choices 1) [1,16] r4854 c4854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1630
  · exact u1631

def b4855 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 70 164 265 400 48 73 201 329), lower := (rows 35 70 164 265 400 48 64 128 256), losses := [] }

theorem u4855 : Upper (D 9) (R 9) [34,68,160,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4855 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4856 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 70 164 265 400 96 89 153 281), lower := (rows 35 70 164 265 400 96 64 128 256), losses := [] }

theorem u4856 : Upper (D 9) (R 9) [34,68,160,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4856 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4857 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 70 164 328 400 33 89 153 281), lower := (rows 35 70 164 328 400 33 64 128 256), losses := [] }

theorem u4857 : Upper (D 9) (R 9) [34,68,160,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4857 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4858 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 164 328 400 40 81 145 273), lower := (rows 35 70 164 328 400 40 64 128 256), losses := [] }

theorem u4858 : Upper (D 9) (R 9) [34,68,160,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4858 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4859 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 70 164 328 400 48 73 137 265), lower := (rows 35 70 164 328 400 48 64 128 256), losses := [] }

theorem u4859 : Upper (D 9) (R 9) [34,68,160,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4859 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4859
end Delivery.IrregularNine14.P09
