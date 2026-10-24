import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0102

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20820 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 74 52 140 274 36 65 193 321), lower := (rows 35 74 52 140 274 36 64 128 256), losses := [] }

theorem u20820 : Upper (D 6) (R 6) [34,72,48,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20821 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 140 274 96 69 133 261), lower := (rows 35 74 52 140 274 96 64 128 256), losses := [] }

theorem u20821 : Upper (D 6) (R 6) [34,72,48,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20822 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 52 140 276 33 67 195 323), lower := (rows 35 74 52 140 276 33 64 128 256), losses := [] }

theorem u20822 : Upper (D 6) (R 6) [34,72,48,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20823 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 140 276 34 65 193 321), lower := (rows 35 74 52 140 276 34 64 128 256), losses := [] }

theorem u20823 : Upper (D 6) (R 6) [34,72,48,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20824 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 140 276 96 67 131 259), lower := (rows 35 74 52 140 276 96 64 128 256), losses := [] }

theorem u20824 : Upper (D 6) (R 6) [34,72,48,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20825 : Route 9 := (fun mask => (mask,id))

def c20825 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20825 : Upper (D 6) (R 6) [34,72,48,132,320,1] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132,320,1] 13 (by decide) (choices 1) [1,2,4] r20825 c20825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6124
  · exact u6125
  · exact u6126

def b20826 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 140 336 34 69 133 261), lower := (rows 35 74 52 140 336 34 64 128 256), losses := [] }

theorem u20826 : Upper (D 6) (R 6) [34,72,48,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20827 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 140 336 36 67 131 259), lower := (rows 35 74 52 140 336 36 64 128 256), losses := [] }

theorem u20827 : Upper (D 6) (R 6) [34,72,48,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20828 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 52 392 81 33 70 134 262), lower := (rows 35 74 52 392 81 33 64 128 256), losses := [] }

theorem u20828 : Upper (D 6) (R 6) [34,72,48,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20829 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 392 81 34 69 133 261), lower := (rows 35 74 52 392 81 34 64 128 256), losses := [] }

theorem u20829 : Upper (D 6) (R 6) [34,72,48,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20830 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 392 81 36 71 135 263), lower := (rows 35 74 52 392 81 36 64 128 256), losses := [] }

theorem u20830 : Upper (D 6) (R 6) [34,72,48,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20831 : Route 9 := (fun mask => (mask,id))

def c20831 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20831 : Upper (D 6) (R 6) [34,72,48,384,68,1] 13 := by
  apply FastRouting.sound _ _ [34,72,48,384,68,1] 13 (by decide) (choices 1) [1,2,4] r20831 c20831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6127
  · exact u6128
  · exact u6129

def b20832 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 392 84 34 69 133 261), lower := (rows 35 74 52 392 84 34 64 128 256), losses := [] }

theorem u20832 : Upper (D 6) (R 6) [34,72,48,384,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20833 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 52 392 84 36 67 131 259), lower := (rows 35 74 52 392 84 36 64 128 256), losses := [] }

theorem u20833 : Upper (D 6) (R 6) [34,72,48,384,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20834 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 13 145 34 356 420 292), lower := (rows 35 74 84 13 145 34 64 128 256), losses := [] }

theorem u20834 : Upper (D 6) (R 6) [34,72,80,5,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20835 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 400, targets := 4 },{ cop := 0, region := 400, targets := 64 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 35 74 84 13 145 36 354 418 290), lower := (rows 35 74 84 13 145 36 64 128 256), losses := [] }

theorem u20835 : Upper (D 6) (R 6) [34,72,80,5,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20836 : Route 9 := (fun mask => (mask,id))

def c20836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20836 : Upper (D 6) (R 6) [34,72,80,5,129,256] 13 := by
  apply FastRouting.sound _ _ [34,72,80,5,129,256] 13 (by decide) (choices 1) [2,4,32] r20836 c20836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6130
  · exact u6131
  · exact u6132

def b20837 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 84 13 146 33 356 420 292), lower := (rows 35 74 84 13 146 33 64 128 256), losses := [] }

theorem u20837 : Upper (D 6) (R 6) [34,72,80,5,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20838 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 400, targets := 4 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 35 74 84 13 146 36 353 417 289), lower := (rows 35 74 84 13 146 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 90 80 475 146 32 64 128 256) }] }

theorem u20838 : Upper (D 6) (R 6) [34,72,80,5,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20839 : PairBound 9 := { available := 37, camps := [], pairs := [(0,6),(3,6)], upper := (rows 35 74 84 13 146 288 101 165 293), lower := (rows 35 74 84 13 146 288 64 128 256), losses := [{ target := 6, region := (rows 19 2 4 12 18 302 0 140 268), good := (rows 51 443 445 429 179 288 0 128 288) }] }

theorem u20839 : Upper (D 6) (R 6) [34,72,80,5,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20839 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20840 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 84 13 176 33 326 390 262), lower := (rows 35 74 84 13 176 33 64 128 256), losses := [] }

theorem u20840 : Upper (D 6) (R 6) [34,72,80,5,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20841 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 13 176 34 325 389 261), lower := (rows 35 74 84 13 176 34 64 128 256), losses := [] }

theorem u20841 : Upper (D 6) (R 6) [34,72,80,5,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20842 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 322, targets := 36 },{ cop := 0, region := 400, targets := 4 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 84 13 176 36 323 387 259), lower := (rows 35 74 84 13 176 36 64 128 256), losses := [] }

theorem u20842 : Upper (D 6) (R 6) [34,72,80,5,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20843 : Route 9 := (fun mask => (mask,id))

def c20843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20843 : Upper (D 6) (R 6) [34,72,80,5,160,256] 13 := by
  apply FastRouting.sound _ _ [34,72,80,5,160,256] 13 (by decide) (choices 1) [1,2,4] r20843 c20843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6133
  · exact u6134
  · exact u6135

def b20844 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 84 13 400 33 102 166 294), lower := (rows 35 74 84 13 400 33 64 128 256), losses := [] }

theorem u20844 : Upper (D 6) (R 6) [34,72,80,5,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20845 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 13 400 34 101 165 293), lower := (rows 35 74 84 13 400 34 64 128 256), losses := [] }

theorem u20845 : Upper (D 6) (R 6) [34,72,80,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20846 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 400, targets := 4 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 35 74 84 13 400 36 99 163 291), lower := (rows 35 74 84 13 400 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 90 80 475 400 32 64 128 256) }] }

theorem u20846 : Upper (D 6) (R 6) [34,72,80,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20847 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 44 145 33 326 390 262), lower := (rows 35 74 84 44 145 33 64 128 256), losses := [] }

theorem u20847 : Upper (D 6) (R 6) [34,72,80,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20848 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 44 145 34 325 389 261), lower := (rows 35 74 84 44 145 34 64 128 256), losses := [] }

theorem u20848 : Upper (D 6) (R 6) [34,72,80,36,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20849 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 84 44 145 36 323 387 259), lower := (rows 35 74 84 44 145 36 64 128 256), losses := [] }

theorem u20849 : Upper (D 6) (R 6) [34,72,80,36,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20850 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 84 44 145 288 71 135 263), lower := (rows 35 74 84 44 145 288 64 128 256), losses := [] }

theorem u20850 : Upper (D 6) (R 6) [34,72,80,36,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20850 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20851 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 44 146 33 325 389 261), lower := (rows 35 74 84 44 146 33 64 128 256), losses := [] }

theorem u20851 : Upper (D 6) (R 6) [34,72,80,36,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20852 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 84 44 146 36 321 385 257), lower := (rows 35 74 84 44 146 36 64 128 256), losses := [] }

theorem u20852 : Upper (D 6) (R 6) [34,72,80,36,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20853 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 84 44 146 288 69 133 261), lower := (rows 35 74 84 44 146 288 64 128 256), losses := [] }

theorem u20853 : Upper (D 6) (R 6) [34,72,80,36,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20853 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20854 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 44 400 33 71 135 263), lower := (rows 35 74 84 44 400 33 64 128 256), losses := [] }

theorem u20854 : Upper (D 6) (R 6) [34,72,80,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20855 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 44 400 34 69 133 261), lower := (rows 35 74 84 44 400 34 64 128 256), losses := [] }

theorem u20855 : Upper (D 6) (R 6) [34,72,80,36,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20856 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 84 44 400 36 67 131 259), lower := (rows 35 74 84 44 400 36 64 128 256), losses := [] }

theorem u20856 : Upper (D 6) (R 6) [34,72,80,36,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20857 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 137 21 34 356 420 292), lower := (rows 35 74 84 137 21 34 64 128 256), losses := [] }

theorem u20857 : Upper (D 6) (R 6) [34,72,80,129,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20858 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 84 137 21 36 354 418 290), lower := (rows 35 74 84 137 21 36 64 128 256), losses := [] }

theorem u20858 : Upper (D 6) (R 6) [34,72,80,129,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20859 : Route 9 := (fun mask => (mask,id))

def c20859 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20859 : Upper (D 6) (R 6) [34,72,80,129,5,256] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,5,256] 13 (by decide) (choices 1) [2,4,32] r20859 c20859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6136
  · exact u6137
  · exact u6138

def b20860 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 84 137 52 33 326 390 262), lower := (rows 35 74 84 137 52 33 64 128 256), losses := [] }

theorem u20860 : Upper (D 6) (R 6) [34,72,80,129,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20861 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 137 52 34 325 389 261), lower := (rows 35 74 84 137 52 34 64 128 256), losses := [] }

theorem u20861 : Upper (D 6) (R 6) [34,72,80,129,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20862 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 84 137 52 36 323 387 259), lower := (rows 35 74 84 137 52 36 64 128 256), losses := [] }

theorem u20862 : Upper (D 6) (R 6) [34,72,80,129,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20863 : Route 9 := (fun mask => (mask,id))

def c20863 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20863 : Upper (D 6) (R 6) [34,72,80,129,36,256] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,36,256] 13 (by decide) (choices 1) [1,2,4] r20863 c20863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6139
  · exact u6140
  · exact u6141

def b20864 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 137 273 34 100 164 292), lower := (rows 35 74 84 137 273 34 64 128 256), losses := [] }

theorem u20864 : Upper (D 6) (R 6) [34,72,80,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20865 : Route 9 := (fun mask => (mask,id))

def c20865 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20865 : Upper (D 6) (R 6) [34,72,80,129,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,257,4] 13 (by decide) (choices 1) [2,4,32] r20865 c20865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6142
  · exact u6143
  · exact u6144

def b20866 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 84 137 274 33 100 164 292), lower := (rows 35 74 84 137 274 33 64 128 256), losses := [] }

theorem u20866 : Upper (D 6) (R 6) [34,72,80,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20867 : Route 9 := (fun mask => (mask,id))

def c20867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20867 : Upper (D 6) (R 6) [34,72,80,129,258,4] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,258,4] 13 (by decide) (choices 1) [1,4,32] r20867 c20867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6145
  · exact u6146
  · exact u6147

def b20868 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 84 137 276 33 102 166 294), lower := (rows 35 74 84 137 276 33 64 128 256), losses := [] }

theorem u20868 : Upper (D 6) (R 6) [34,72,80,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20869 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 137 276 34 101 165 293), lower := (rows 35 74 84 137 276 34 64 128 256), losses := [] }

theorem u20869 : Upper (D 6) (R 6) [34,72,80,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20870 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 84 137 276 36 99 163 291), lower := (rows 35 74 84 137 276 36 64 128 256), losses := [] }

theorem u20870 : Upper (D 6) (R 6) [34,72,80,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20871 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 84 137 304 33 70 134 262), lower := (rows 35 74 84 137 304 33 64 128 256), losses := [] }

theorem u20871 : Upper (D 6) (R 6) [34,72,80,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20872 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 84 137 304 34 69 133 261), lower := (rows 35 74 84 137 304 34 64 128 256), losses := [] }

theorem u20872 : Upper (D 6) (R 6) [34,72,80,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20873 : Route 9 := (fun mask => (mask,id))

def c20873 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20873 : Upper (D 6) (R 6) [34,72,80,129,288,4] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,288,4] 13 (by decide) (choices 1) [1,2,4] r20873 c20873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6148
  · exact u6149
  · exact u6150

def b20874 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 84 138 21 33 356 420 292), lower := (rows 35 74 84 138 21 33 64 128 256), losses := [] }

theorem u20874 : Upper (D 6) (R 6) [34,72,80,130,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20875 : PairBound 9 := { available := 289, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 84 138 21 36 353 417 289), lower := (rows 35 74 84 138 21 36 64 128 256), losses := [] }

theorem u20875 : Upper (D 6) (R 6) [34,72,80,130,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20876 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 84 138 21 288 101 165 293), lower := (rows 35 74 84 138 21 288 64 128 256), losses := [] }

theorem u20876 : Upper (D 6) (R 6) [34,72,80,130,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20876 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20877 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 84 138 52 33 325 389 261), lower := (rows 35 74 84 138 52 33 64 128 256), losses := [] }

theorem u20877 : Upper (D 6) (R 6) [34,72,80,130,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20878 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 84 138 52 36 321 385 257), lower := (rows 35 74 84 138 52 36 64 128 256), losses := [] }

theorem u20878 : Upper (D 6) (R 6) [34,72,80,130,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20879 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 84 138 52 288 69 133 261), lower := (rows 35 74 84 138 52 288 64 128 256), losses := [] }

theorem u20879 : Upper (D 6) (R 6) [34,72,80,130,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20879 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20879
end Delivery.IrregularNine14.P06
