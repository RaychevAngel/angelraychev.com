import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0030
import IrregularNine14P09C0031

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5100 : Route 9 := (fun mask => (mask,id))

def c5100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5100 : Upper (D 9) (R 9) [34,192,24,65,384,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,65,384,256] 13 (by decide) (choices 1) [1,4,32] r5100 c5100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1826
  · exact u1827
  · exact u1828

def b5101 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 28 76 176 33 321 385 257), lower := (rows 35 194 28 76 176 33 64 128 256), losses := [] }

theorem u5101 : Upper (D 9) (R 9) [34,192,24,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5101 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5102 : Route 9 := (fun mask => (mask,id))

def c5102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5102 : Upper (D 9) (R 9) [34,192,24,68,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,160,256] 13 (by decide) (choices 1) [1,256] r5102 c5102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1829
  · exact u1830

def b5103 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(1,0),(4,6)], upper := (rows 35 194 28 76 273 33 480 416 416), lower := (rows 35 194 28 76 273 33 64 128 256), losses := [] }

theorem u5103 : Upper (D 9) (R 9) [34,192,24,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5103 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5104 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6),(4,7)], upper := (rows 35 194 28 76 273 160 353 417 289), lower := (rows 35 194 28 76 273 160 64 128 256), losses := [] }

theorem u5104 : Upper (D 9) (R 9) [34,192,24,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5104 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5105 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 5, region := 195, targets := 256 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,6)], upper := (rows 35 194 28 76 273 288 225 161 417), lower := (rows 35 194 28 76 273 288 64 128 256), losses := [{ target := 8, region := (rows 33 51 20 24 16 32 97 161 0), good := (rows 227 194 30 76 223 227 64 128 0) }] }

theorem u5105 : Upper (D 9) (R 9) [34,192,24,68,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5105 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5106 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(0,7),(0,8),(1,5),(4,6)], upper := (rows 35 194 28 76 304 33 449 385 385), lower := (rows 35 194 28 76 304 33 64 128 256), losses := [] }

theorem u5106 : Upper (D 9) (R 9) [34,192,24,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5107 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6),(4,7)], upper := (rows 35 194 28 76 304 160 321 385 257), lower := (rows 35 194 28 76 304 160 64 128 256), losses := [] }

theorem u5107 : Upper (D 9) (R 9) [34,192,24,68,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5107 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5108 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 28 76 304 288 193 129 385), lower := (rows 35 194 28 76 304 288 64 128 256), losses := [] }

theorem u5108 : Upper (D 9) (R 9) [34,192,24,68,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5108 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5109 : Route 9 := (fun mask => (mask,id))

def c5109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5109 : Upper (D 9) (R 9) [34,192,24,68,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,68,384,1] 13 (by decide) (choices 1) [1,32,256] r5109 c5109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1831
  · exact u1832
  · exact u1833

def b5110 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(4,6)], upper := (rows 35 194 28 76 400 288 97 161 289), lower := (rows 35 194 28 76 400 288 64 128 256), losses := [] }

theorem u5110 : Upper (D 9) (R 9) [34,192,24,68,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5111 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(3,7),(3,8)], upper := (rows 35 194 28 104 273 33 452 388 388), lower := (rows 35 194 28 104 273 33 64 128 256), losses := [] }

theorem u5111 : Upper (D 9) (R 9) [34,192,24,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5111 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5112 : Route 9 := (fun mask => (mask,id))

def c5112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5112 : Upper (D 9) (R 9) [34,192,24,96,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,257,4] 13 (by decide) (choices 1) [1,128,256] r5112 c5112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1834
  · exact u1835
  · exact u1836

def b5113 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(3,8),(4,7)], upper := (rows 35 194 28 104 273 160 325 389 261), lower := (rows 35 194 28 104 273 160 64 128 256), losses := [] }

theorem u5113 : Upper (D 9) (R 9) [34,192,24,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5113 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5114 : Route 9 := (fun mask => (mask,id))

def c5114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5114 : Upper (D 9) (R 9) [34,192,24,96,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,257,256] 13 (by decide) (choices 1) [1,4,128] r5114 c5114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1837
  · exact u1838
  · exact u1839

def b5115 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(0,8),(1,5),(3,7),(3,8)], upper := (rows 35 194 28 104 276 33 449 385 385), lower := (rows 35 194 28 104 276 33 64 128 256), losses := [] }

theorem u5115 : Upper (D 9) (R 9) [34,192,24,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5115 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5116 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8),(2,7),(3,7),(3,8),(4,7)], upper := (rows 35 194 28 104 276 160 321 385 257), lower := (rows 35 194 28 104 276 160 64 128 256), losses := [] }

theorem u5116 : Upper (D 9) (R 9) [34,192,24,96,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5116 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5117 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 203, targets := 256 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,5),(1,8),(3,8)], upper := (rows 35 194 28 104 276 288 193 129 385), lower := (rows 35 194 28 104 276 288 64 128 256), losses := [] }

theorem u5117 : Upper (D 9) (R 9) [34,192,24,96,260,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5117 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5118 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 194 28 104 400 33 325 389 261), lower := (rows 35 194 28 104 400 33 64 128 256), losses := [] }

theorem u5118 : Upper (D 9) (R 9) [34,192,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5118 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5119 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(1,5),(3,7),(4,5),(4,6)], upper := (rows 35 194 28 104 400 36 321 385 257), lower := (rows 35 194 28 104 400 36 64 128 256), losses := [] }

theorem u5119 : Upper (D 9) (R 9) [34,192,24,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5119 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5120 : Route 9 := (fun mask => (mask,id))

def c5120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5120 : Upper (D 9) (R 9) [34,192,24,96,384,256] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,384,256] 13 (by decide) (choices 1) [1,4] r5120 c5120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1840
  · exact u1841

def b5121 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 52, targets := 192 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,6),(2,7),(4,6),(4,7)], upper := (rows 35 194 28 265 304 33 196 196 452), lower := (rows 35 194 28 265 304 33 64 128 256), losses := [] }

theorem u5121 : Upper (D 9) (R 9) [34,192,24,257,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5121 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5122 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 52, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 35 194 28 265 304 36 193 193 449), lower := (rows 35 194 28 265 304 36 64 128 256), losses := [] }

theorem u5122 : Upper (D 9) (R 9) [34,192,24,257,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5122 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5123 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 194 28 265 304 96 197 133 389), lower := (rows 35 194 28 265 304 96 64 128 256), losses := [] }

theorem u5123 : Upper (D 9) (R 9) [34,192,24,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5123 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5124 : Route 9 := (fun mask => (mask,id))

def c5124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5124 : Upper (D 9) (R 9) [34,192,24,257,320,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,257,320,1] 13 (by decide) (choices 1) [4,32,128] r5124 c5124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1842
  · exact u1843
  · exact u1844

def r5125 : Route 9 := (fun mask => (mask,id))

def c5125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5125 : Upper (D 9) (R 9) [34,192,24,257,320,4] 13 := by
  apply FastRouting.sound _ _ [34,192,24,257,320,4] 13 (by decide) (choices 1) [1,32,128] r5125 c5125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1845
  · exact u1846
  · exact u1847

def b5126 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 265 336 160 101 165 293), lower := (rows 35 194 28 265 336 160 64 128 256), losses := [] }

theorem u5126 : Upper (D 9) (R 9) [34,192,24,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5126 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5127 : Route 9 := (fun mask => (mask,id))

def c5127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5127 : Upper (D 9) (R 9) [34,192,24,288,320,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,288,320,1] 13 (by decide) (choices 1) [1,4,128] r5127 c5127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1848
  · exact u1849
  · exact u1850

def b5128 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(3,0)], upper := (rows 35 194 28 296 336 36 193 129 385), lower := (rows 35 194 28 296 336 36 64 128 256), losses := [] }

theorem u5128 : Upper (D 9) (R 9) [34,192,24,288,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5128 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5129 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 296 336 160 69 133 261), lower := (rows 35 194 28 296 336 160 64 128 256), losses := [] }

theorem u5129 : Upper (D 9) (R 9) [34,192,24,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5129 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5130 : Route 9 := (fun mask => (mask,id))

def c5130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5130 : Upper (D 9) (R 9) [34,192,24,320,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,320,384,1] 13 (by decide) (choices 1) [1,4,32] r5130 c5130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1851
  · exact u1852
  · exact u1853

def b5131 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 227, targets := 256 },{ cop := 0, region := 400, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(4,6)], upper := (rows 35 194 28 328 400 36 97 161 289), lower := (rows 35 194 28 328 400 36 64 128 256), losses := [] }

theorem u5131 : Upper (D 9) (R 9) [34,192,24,320,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5131 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5132 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 44 73 145 36 336 400 272), lower := (rows 35 194 44 73 145 36 64 128 256), losses := [] }

theorem u5132 : Upper (D 9) (R 9) [34,192,40,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5132 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5133 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 44 73 145 48 324 388 260), lower := (rows 35 194 44 73 145 48 64 128 256), losses := [] }

theorem u5133 : Upper (D 9) (R 9) [34,192,40,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5133 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5134 : Route 9 := (fun mask => (mask,id))

def c5134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5134 : Upper (D 9) (R 9) [34,192,40,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,129,256] 13 (by decide) (choices 1) [4,16,256] r5134 c5134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1854
  · exact u1855
  · exact u1856

def b5135 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 2, region := 466, targets := 1 }], pairs := [(0,8),(1,0),(2,8),(3,8),(4,8)], upper := (rows 35 194 44 73 148 33 336 400 272), lower := (rows 35 194 44 73 148 33 64 128 256), losses := [] }

theorem u5135 : Upper (D 9) (R 9) [34,192,40,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5135 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5136 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 44 73 148 48 321 385 257), lower := (rows 35 194 44 73 148 48 64 128 256), losses := [] }

theorem u5136 : Upper (D 9) (R 9) [34,192,40,65,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5136 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5137 : Route 9 := (fun mask => (mask,id))

def c5137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5137 : Upper (D 9) (R 9) [34,192,40,65,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,132,256] 13 (by decide) (choices 1) [1,16,256] r5137 c5137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1857
  · exact u1858
  · exact u1859

def b5138 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 44 73 273 36 464 400 400), lower := (rows 35 194 44 73 273 36 64 128 256), losses := [] }

theorem u5138 : Upper (D 9) (R 9) [34,192,40,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5138 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5139 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 3, region := 436, targets := 64 }], pairs := [(1,0),(1,5),(2,6),(4,6)], upper := (rows 35 194 44 73 273 48 452 388 388), lower := (rows 35 194 44 73 273 48 64 128 256), losses := [] }

theorem u5139 : Upper (D 9) (R 9) [34,192,40,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5139 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5140 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 44 73 273 160 340 404 276), lower := (rows 35 194 44 73 273 160 64 128 256), losses := [] }

theorem u5140 : Upper (D 9) (R 9) [34,192,40,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5140 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5141 : Route 9 := (fun mask => (mask,id))

def c5141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5141 : Upper (D 9) (R 9) [34,192,40,65,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,257,256] 13 (by decide) (choices 1) [4,16,128] r5141 c5141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1860
  · exact u1861
  · exact u1862

def b5142 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 44 73 276 33 464 400 400), lower := (rows 35 194 44 73 276 33 64 128 256), losses := [] }

theorem u5142 : Upper (D 9) (R 9) [34,192,40,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5142 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5143 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 436, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,6)], upper := (rows 35 194 44 73 276 48 449 385 385), lower := (rows 35 194 44 73 276 48 64 128 256), losses := [] }

theorem u5143 : Upper (D 9) (R 9) [34,192,40,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5143 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5144 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 44 73 276 160 337 401 273), lower := (rows 35 194 44 73 276 160 64 128 256), losses := [] }

theorem u5144 : Upper (D 9) (R 9) [34,192,40,65,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5144 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5145 : Route 9 := (fun mask => (mask,id))

def c5145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5145 : Upper (D 9) (R 9) [34,192,40,65,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,260,256] 13 (by decide) (choices 1) [1,16,128] r5145 c5145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1863
  · exact u1864
  · exact u1865

def b5146 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 44 73 400 33 340 404 276), lower := (rows 35 194 44 73 400 33 64 128 256), losses := [] }

theorem u5146 : Upper (D 9) (R 9) [34,192,40,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5146 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5147 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 44 73 400 36 337 401 273), lower := (rows 35 194 44 73 400 36 64 128 256), losses := [] }

theorem u5147 : Upper (D 9) (R 9) [34,192,40,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5147 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5148 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(2,7),(3,7),(4,6)], upper := (rows 35 194 44 73 400 48 325 389 261), lower := (rows 35 194 44 73 400 48 64 128 256), losses := [] }

theorem u5148 : Upper (D 9) (R 9) [34,192,40,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5148 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5149 : Route 9 := (fun mask => (mask,id))

def c5149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5149 : Upper (D 9) (R 9) [34,192,40,65,384,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,384,256] 13 (by decide) (choices 1) [1,4,16] r5149 c5149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1866
  · exact u1867
  · exact u1868

def b5150 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 44 76 273 33 464 400 400), lower := (rows 35 194 44 76 273 33 64 128 256), losses := [] }

theorem u5150 : Upper (D 9) (R 9) [34,192,40,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5150 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5151 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 194 44 76 273 48 449 385 385), lower := (rows 35 194 44 76 273 48 64 128 256), losses := [] }

theorem u5151 : Upper (D 9) (R 9) [34,192,40,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5151 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5152 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 44 76 273 160 337 401 273), lower := (rows 35 194 44 76 273 160 64 128 256), losses := [] }

theorem u5152 : Upper (D 9) (R 9) [34,192,40,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5152 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5153 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 194, targets := 256 }], pairs := [(0,6),(1,5),(1,8),(4,5),(4,6)], upper := (rows 35 194 44 76 273 288 209 145 401), lower := (rows 35 194 44 76 273 288 64 128 256), losses := [] }

theorem u5153 : Upper (D 9) (R 9) [34,192,40,68,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5153 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5154 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,7)], upper := (rows 35 194 44 76 400 33 337 401 273), lower := (rows 35 194 44 76 400 33 64 128 256), losses := [] }

theorem u5154 : Upper (D 9) (R 9) [34,192,40,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5154 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5155 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 332, targets := 128 }], pairs := [(1,5),(2,7),(3,7),(4,5)], upper := (rows 35 194 44 76 400 48 321 385 257), lower := (rows 35 194 44 76 400 48 64 128 256), losses := [] }

theorem u5155 : Upper (D 9) (R 9) [34,192,40,68,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5155 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5156 : Route 9 := (fun mask => (mask,id))

def c5156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5156 : Upper (D 9) (R 9) [34,192,40,68,384,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,384,256] 13 (by decide) (choices 1) [1,16] r5156 c5156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1869
  · exact u1870

def b5157 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 61, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 44 88 145 33 324 388 260), lower := (rows 35 194 44 88 145 33 64 128 256), losses := [] }

theorem u5157 : Upper (D 9) (R 9) [34,192,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5157 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5158 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 61, targets := 256 }], pairs := [(0,8),(2,8),(3,8),(4,8)], upper := (rows 35 194 44 88 145 36 321 385 257), lower := (rows 35 194 44 88 145 36 64 128 256), losses := [] }

theorem u5158 : Upper (D 9) (R 9) [34,192,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5158 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5159 : Route 9 := (fun mask => (mask,id))

def c5159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5159 : Upper (D 9) (R 9) [34,192,40,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,129,256] 13 (by decide) (choices 1) [1,4,256] r5159 c5159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1871
  · exact u1872
  · exact u1873

#print axioms u5159
end Delivery.IrregularNine14.P09
