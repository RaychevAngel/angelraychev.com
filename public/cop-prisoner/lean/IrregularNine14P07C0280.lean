import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0065

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16800 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 88 146 34 449 385 385), lower := (rows 13 98 37 88 146 34 64 128 256), losses := [] }

theorem u16800 : Upper (D 7) (R 7) [12,96,33,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16801 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 322, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 13 98 37 88 146 160 323 387 259), lower := (rows 13 98 37 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 14 98 36 122 178 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 13 96 37 125 176 160 64 160 256) }] }

theorem u16801 : Upper (D 7) (R 7) [12,96,33,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16802 : Route 9 := (fun mask => (mask,id))

def c16802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16802 : Upper (D 7) (R 7) [12,96,33,80,130,256] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,130,256] 13 (by decide) (choices 1) [1,2,128] r16802 c16802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3921
  · exact u3922
  · exact u3923

def b16803 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 88 273 34 194 130 386), lower := (rows 13 98 37 88 273 34 64 128 256), losses := [] }

theorem u16803 : Upper (D 7) (R 7) [12,96,33,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16804 : Route 9 := (fun mask => (mask,id))

def c16804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16804 : Upper (D 7) (R 7) [12,96,33,80,257,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,257,128] 13 (by decide) (choices 1) [2,128] r16804 c16804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3924
  · exact u3925

def b16805 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 98 37 88 274 33 194 130 386), lower := (rows 13 98 37 88 274 33 64 128 256), losses := [] }

theorem u16805 : Upper (D 7) (R 7) [12,96,33,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16806 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 88 274 34 193 129 385), lower := (rows 13 98 37 88 274 34 64 128 256), losses := [] }

theorem u16806 : Upper (D 7) (R 7) [12,96,33,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16807 : Route 9 := (fun mask => (mask,id))

def c16807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16807 : Upper (D 7) (R 7) [12,96,33,80,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,258,128] 13 (by decide) (choices 1) [1,2,128] r16807 c16807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3926
  · exact u3927
  · exact u3928

def b16808 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 98 37 88 400 33 194 130 386), lower := (rows 13 98 37 88 400 33 64 128 256), losses := [] }

theorem u16808 : Upper (D 7) (R 7) [12,96,33,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16809 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 88 400 34 195 131 387), lower := (rows 13 98 37 88 400 34 64 128 256), losses := [] }

theorem u16809 : Upper (D 7) (R 7) [12,96,33,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16810 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 13 98 37 88 400 160 67 131 259), lower := (rows 13 98 37 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 14 98 36 122 432 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 13 96 37 125 432 160 64 160 256) }] }

theorem u16810 : Upper (D 7) (R 7) [12,96,33,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16811 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 137 274 34 208 208 464), lower := (rows 13 98 37 137 274 34 64 128 256), losses := [] }

theorem u16811 : Upper (D 7) (R 7) [12,96,33,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16812 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 13 98 37 137 274 48 194 194 450), lower := (rows 13 98 37 137 274 48 64 128 256), losses := [] }

theorem u16812 : Upper (D 7) (R 7) [12,96,33,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16812 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16813 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 137 274 96 210 146 402), lower := (rows 13 98 37 137 274 96 64 128 256), losses := [] }

theorem u16813 : Upper (D 7) (R 7) [12,96,33,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16814 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 13, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 137 274 160 82 210 338), lower := (rows 13 98 37 137 274 160 64 128 256), losses := [] }

theorem u16814 : Upper (D 7) (R 7) [12,96,33,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16815 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 137 336 34 210 146 402), lower := (rows 13 98 37 137 336 34 64 128 256), losses := [] }

theorem u16815 : Upper (D 7) (R 7) [12,96,33,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16816 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 137 336 48 194 130 386), lower := (rows 13 98 37 137 336 48 64 128 256), losses := [] }

theorem u16816 : Upper (D 7) (R 7) [12,96,33,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16816 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16817 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 13, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 137 336 160 82 146 274), lower := (rows 13 98 37 137 336 160 64 128 256), losses := [] }

theorem u16817 : Upper (D 7) (R 7) [12,96,33,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16818 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 138 81 34 464 400 400), lower := (rows 13 98 37 138 81 34 64 128 256), losses := [] }

theorem u16818 : Upper (D 7) (R 7) [12,96,33,130,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16819 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 138 81 48 450 386 386), lower := (rows 13 98 37 138 81 48 64 128 256), losses := [] }

theorem u16819 : Upper (D 7) (R 7) [12,96,33,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16819 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16820 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 138 81 160 338 402 274), lower := (rows 13 98 37 138 81 160 64 128 256), losses := [] }

theorem u16820 : Upper (D 7) (R 7) [12,96,33,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16821 : Route 9 := (fun mask => (mask,id))

def c16821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16821 : Upper (D 7) (R 7) [12,96,33,130,65,256] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,65,256] 13 (by decide) (choices 1) [2,16,128] r16821 c16821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3929
  · exact u3930
  · exact u3931

def b16822 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 138 208 33 338 402 274), lower := (rows 13 98 37 138 208 33 64 128 256), losses := [] }

theorem u16822 : Upper (D 7) (R 7) [12,96,33,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16823 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 138 208 34 337 401 273), lower := (rows 13 98 37 138 208 34 64 128 256), losses := [] }

theorem u16823 : Upper (D 7) (R 7) [12,96,33,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16824 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 138 208 48 323 387 259), lower := (rows 13 98 37 138 208 48 64 128 256), losses := [] }

theorem u16824 : Upper (D 7) (R 7) [12,96,33,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16824 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16825 : Route 9 := (fun mask => (mask,id))

def c16825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16825 : Upper (D 7) (R 7) [12,96,33,130,192,256] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,192,256] 13 (by decide) (choices 1) [1,2,16] r16825 c16825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3932
  · exact u3933
  · exact u3934

def b16826 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 138 273 34 208 208 464), lower := (rows 13 98 37 138 273 34 64 128 256), losses := [] }

theorem u16826 : Upper (D 7) (R 7) [12,96,33,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16827 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 13 98 37 138 273 48 194 194 450), lower := (rows 13 98 37 138 273 48 64 128 256), losses := [] }

theorem u16827 : Upper (D 7) (R 7) [12,96,33,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16827 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16828 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 138 273 96 210 146 402), lower := (rows 13 98 37 138 273 96 64 128 256), losses := [] }

theorem u16828 : Upper (D 7) (R 7) [12,96,33,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16829 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 138 273 160 82 210 338), lower := (rows 13 98 37 138 273 160 64 128 256), losses := [] }

theorem u16829 : Upper (D 7) (R 7) [12,96,33,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16830 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 138 274 33 208 208 464), lower := (rows 13 98 37 138 274 33 64 128 256), losses := [] }

theorem u16830 : Upper (D 7) (R 7) [12,96,33,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16831 : Route 9 := (fun mask => (mask,id))

def c16831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16831 : Upper (D 7) (R 7) [12,96,33,130,258,16] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,258,16] 13 (by decide) (choices 1) [1,128] r16831 c16831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3935
  · exact u3936

def b16832 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 138 274 96 209 145 401), lower := (rows 13 98 37 138 274 96 64 128 256), losses := [] }

theorem u16832 : Upper (D 7) (R 7) [12,96,33,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16833 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 138 274 160 81 209 337), lower := (rows 13 98 37 138 274 160 64 128 256), losses := [] }

theorem u16833 : Upper (D 7) (R 7) [12,96,33,130,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16834 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 138 336 33 210 146 402), lower := (rows 13 98 37 138 336 33 64 128 256), losses := [] }

theorem u16834 : Upper (D 7) (R 7) [12,96,33,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16835 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 138 336 34 209 145 401), lower := (rows 13 98 37 138 336 34 64 128 256), losses := [] }

theorem u16835 : Upper (D 7) (R 7) [12,96,33,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16836 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 37 138 336 48 195 131 387), lower := (rows 13 98 37 138 336 48 64 128 256), losses := [] }

theorem u16836 : Upper (D 7) (R 7) [12,96,33,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16836 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16837 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 138 336 160 83 147 275), lower := (rows 13 98 37 138 336 160 64 128 256), losses := [] }

theorem u16837 : Upper (D 7) (R 7) [12,96,33,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16838 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 138 400 33 82 210 338), lower := (rows 13 98 37 138 400 33 64 128 256), losses := [] }

theorem u16838 : Upper (D 7) (R 7) [12,96,33,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16839 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 37 138 400 34 81 209 337), lower := (rows 13 98 37 138 400 34 64 128 256), losses := [] }

theorem u16839 : Upper (D 7) (R 7) [12,96,33,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16840 : Route 9 := (fun mask => (mask,id))

def c16840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16840 : Upper (D 7) (R 7) [12,96,33,130,384,16] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,384,16] 13 (by decide) (choices 1) [1,2] r16840 c16840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3937
  · exact u3938

def b16841 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 138 400 96 83 147 275), lower := (rows 13 98 37 138 400 96 64 128 256), losses := [] }

theorem u16841 : Upper (D 7) (R 7) [12,96,33,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16842 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,0),(3,0),(3,1),(3,5)], upper := (rows 13 98 37 152 19 34 448 448 448), lower := (rows 13 98 37 152 19 34 64 128 256), losses := [] }

theorem u16842 : Upper (D 7) (R 7) [12,96,33,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16843 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 152 19 96 450 386 386), lower := (rows 13 98 37 152 19 96 64 128 256), losses := [] }

theorem u16843 : Upper (D 7) (R 7) [12,96,33,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16844 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 152 19 160 322 450 322), lower := (rows 13 98 37 152 19 160 64 128 256), losses := [] }

theorem u16844 : Upper (D 7) (R 7) [12,96,33,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16845 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 13 98 37 152 19 288 194 194 450), lower := (rows 13 98 37 152 19 288 64 128 256), losses := [] }

theorem u16845 : Upper (D 7) (R 7) [12,96,33,144,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16845 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16846 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 38, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 37 152 81 34 450 386 386), lower := (rows 13 98 37 152 81 34 64 128 256), losses := [] }

theorem u16846 : Upper (D 7) (R 7) [12,96,33,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16847 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 152 81 160 322 386 258), lower := (rows 13 98 37 152 81 160 64 128 256), losses := [] }

theorem u16847 : Upper (D 7) (R 7) [12,96,33,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16848 : Route 9 := (fun mask => (mask,id))

def c16848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16848 : Upper (D 7) (R 7) [12,96,33,144,65,256] 13 := by
  apply FastRouting.sound _ _ [12,96,33,144,65,256] 13 (by decide) (choices 1) [2,128] r16848 c16848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3939
  · exact u3940

def b16849 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(3,0)], upper := (rows 13 98 37 152 273 34 194 194 450), lower := (rows 13 98 37 152 273 34 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 12 20 0 98 162 290), good := (rows 29 450 477 152 273 450 64 128 256) }] }

theorem u16849 : Upper (D 7) (R 7) [12,96,33,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16850 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 152 273 96 194 130 386), lower := (rows 13 98 37 152 273 96 64 128 256), losses := [] }

theorem u16850 : Upper (D 7) (R 7) [12,96,33,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16851 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 152 273 160 66 194 322), lower := (rows 13 98 37 152 273 160 64 128 256), losses := [] }

theorem u16851 : Upper (D 7) (R 7) [12,96,33,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16852 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 152 274 33 194 194 450), lower := (rows 13 98 37 152 274 33 64 128 256), losses := [] }

theorem u16852 : Upper (D 7) (R 7) [12,96,33,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16853 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 13 98 37 152 274 34 193 193 449), lower := (rows 13 98 37 152 274 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 128 256), good := (rows 13 34 37 189 306 34 0 128 256) }] }

theorem u16853 : Upper (D 7) (R 7) [12,96,33,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16854 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 37 152 274 96 195 131 387), lower := (rows 13 98 37 152 274 96 64 128 256), losses := [] }

theorem u16854 : Upper (D 7) (R 7) [12,96,33,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16855 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 152 274 160 67 195 323), lower := (rows 13 98 37 152 274 160 64 128 256), losses := [] }

theorem u16855 : Upper (D 7) (R 7) [12,96,33,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16856 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 98 37 152 336 33 194 130 386), lower := (rows 13 98 37 152 336 33 64 128 256), losses := [] }

theorem u16856 : Upper (D 7) (R 7) [12,96,33,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16857 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 152 336 34 195 131 387), lower := (rows 13 98 37 152 336 34 64 128 256), losses := [{ target := 7, region := (rows 9 82 13 8 16 122 64 0 256), good := (rows 45 98 37 63 370 34 98 0 256) }] }

theorem u16857 : Upper (D 7) (R 7) [12,96,33,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16858 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 37 152 336 160 67 131 259), lower := (rows 13 98 37 152 336 160 64 128 256), losses := [] }

theorem u16858 : Upper (D 7) (R 7) [12,96,33,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16859 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 98 37 200 146 33 338 402 274), lower := (rows 13 98 37 200 146 33 64 128 256), losses := [] }

theorem u16859 : Upper (D 7) (R 7) [12,96,33,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16859
end Delivery.IrregularNine14.P07
