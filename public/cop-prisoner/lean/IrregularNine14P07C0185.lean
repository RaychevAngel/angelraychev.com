import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11100 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 133 11 176 34 80 200 328), lower := (rows 97 262 133 11 176 34 80 128 256), losses := [] }

theorem u11100 : Upper (D 7) (R 7) [96,260,129,3,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11100 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11101 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 97 262 133 11 176 40 66 208 336), lower := (rows 97 262 133 11 176 40 66 128 256), losses := [] }

theorem u11101 : Upper (D 7) (R 7) [96,260,129,3,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11101 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11102 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 262 133 11 176 40 80 194 322), lower := (rows 97 262 133 11 176 40 80 128 256), losses := [] }

theorem u11102 : Upper (D 7) (R 7) [96,260,129,3,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11102 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11103 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 133 25 26 34 96 192 448), lower := (rows 97 262 133 25 26 34 96 128 256), losses := [] }

theorem u11103 : Upper (D 7) (R 7) [96,260,129,17,10,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11104 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 197, targets := 2 },{ cop := 2, region := 354, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 97 262 133 25 26 34 192 224 352), lower := (rows 97 262 133 25 26 34 192 128 256), losses := [{ target := 7, region := (rows 1 6 4 12 22 54 64 0 257), good := (rows 353 318 319 313 58 50 64 0 256) }] }

theorem u11104 : Upper (D 7) (R 7) [96,260,129,17,10,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11105 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 133 25 26 96 192 162 290), lower := (rows 97 262 133 25 26 96 192 128 256), losses := [] }

theorem u11105 : Upper (D 7) (R 7) [96,260,129,17,10,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11106 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 0, region := 132, targets := 2 }], pairs := [(0,7),(2,1),(3,7)], upper := (rows 97 262 133 25 146 34 72 224 352), lower := (rows 97 262 133 25 146 34 72 128 256), losses := [] }

theorem u11106 : Upper (D 7) (R 7) [96,260,129,17,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11106 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11107 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 133 25 146 34 96 200 328), lower := (rows 97 262 133 25 146 34 96 128 256), losses := [] }

theorem u11107 : Upper (D 7) (R 7) [96,260,129,17,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11108 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 133 25 146 40 96 194 322), lower := (rows 97 262 133 25 146 40 96 128 256), losses := [] }

theorem u11108 : Upper (D 7) (R 7) [96,260,129,17,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11108 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11109 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 262 133 25 176 34 66 200 328), lower := (rows 97 262 133 25 176 34 66 128 256), losses := [] }

theorem u11109 : Upper (D 7) (R 7) [96,260,129,17,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11110 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 262 133 25 176 34 72 194 322), lower := (rows 97 262 133 25 176 34 72 128 256), losses := [] }

theorem u11110 : Upper (D 7) (R 7) [96,260,129,17,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11110 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11111 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 97 262 133 26 152 33 66 224 352), lower := (rows 97 262 133 26 152 33 66 128 256), losses := [] }

theorem u11111 : Upper (D 7) (R 7) [96,260,129,18,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11112 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 133 26 152 33 96 194 322), lower := (rows 97 262 133 26 152 33 96 128 256), losses := [] }

theorem u11112 : Upper (D 7) (R 7) [96,260,129,18,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11113 : Route 9 := (fun mask => (mask,id))

def c11113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11113 : Upper (D 7) (R 7) [96,260,129,18,160,2,1] 13 := by
  apply FastRouting.sound _ _ [96,260,129,18,160,2,1] 13 (by decide) (choices 1) [8,64] r11113 c11113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u831
  · exact u832

def b11114 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 97 262 133 26 176 34 72 193 321), lower := (rows 97 262 133 26 176 34 72 128 256), losses := [] }

theorem u11114 : Upper (D 7) (R 7) [96,260,129,18,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11114 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11115 : Route 9 := (fun mask => (mask,id))

def c11115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11115 : Upper (D 7) (R 7) [96,260,129,48,130,1,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,48,130,1,2] 13 (by decide) (choices 1) [8,64] r11115 c11115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u833
  · exact u834

def b11116 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 133 56 146 33 72 194 322), lower := (rows 97 262 133 56 146 33 72 128 256), losses := [] }

theorem u11116 : Upper (D 7) (R 7) [96,260,129,48,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11116 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11117 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 80, targets := 34 },{ cop := 3, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,5)], upper := (rows 97 262 133 56 208 34 65 138 266), lower := (rows 97 262 133 56 208 34 65 128 256), losses := [] }

theorem u11117 : Upper (D 7) (R 7) [96,260,129,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11118 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 262 133 56 208 34 66 137 265), lower := (rows 97 262 133 56 208 34 66 128 256), losses := [] }

theorem u11118 : Upper (D 7) (R 7) [96,260,129,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11119 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 133 56 208 34 72 131 259), lower := (rows 97 262 133 56 208 34 72 128 256), losses := [] }

theorem u11119 : Upper (D 7) (R 7) [96,260,129,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11119 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11120 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,5),(4,1)], upper := (rows 97 262 134 11 56 160 65 208 336), lower := (rows 97 262 134 11 56 160 65 128 256), losses := [{ target := 5, region := (rows 1 18 20 8 16 0 73 144 272), good := (rows 65 262 134 75 478 128 65 128 256) }] }

theorem u11120 : Upper (D 7) (R 7) [96,260,130,3,40,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11121 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 134 11 56 160 80 193 321), lower := (rows 97 262 134 11 56 160 80 128 256), losses := [] }

theorem u11121 : Upper (D 7) (R 7) [96,260,130,3,40,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11121 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11122 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 390, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 262 134 11 145 40 80 224 352), lower := (rows 97 262 134 11 145 40 80 128 256), losses := [] }

theorem u11122 : Upper (D 7) (R 7) [96,260,130,3,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11122 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11123 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 134 11 145 40 96 208 336), lower := (rows 97 262 134 11 145 40 96 128 256), losses := [] }

theorem u11123 : Upper (D 7) (R 7) [96,260,130,3,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11123 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11124 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 134 11 145 48 96 200 328), lower := (rows 97 262 134 11 145 48 96 128 256), losses := [] }

theorem u11124 : Upper (D 7) (R 7) [96,260,130,3,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11124 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11125 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 97 262 134 11 152 33 80 224 352), lower := (rows 97 262 134 11 152 33 80 128 256), losses := [] }

theorem u11125 : Upper (D 7) (R 7) [96,260,130,3,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11125 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11126 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 134 11 152 33 96 208 336), lower := (rows 97 262 134 11 152 33 96 128 256), losses := [] }

theorem u11126 : Upper (D 7) (R 7) [96,260,130,3,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11127 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 134 11 176 33 72 208 336), lower := (rows 97 262 134 11 176 33 72 128 256), losses := [] }

theorem u11127 : Upper (D 7) (R 7) [96,260,130,3,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11127 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11128 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 134 11 176 33 80 200 328), lower := (rows 97 262 134 11 176 33 80 128 256), losses := [] }

theorem u11128 : Upper (D 7) (R 7) [96,260,130,3,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11128 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11129 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(3,1)], upper := (rows 97 262 134 25 26 33 192 224 352), lower := (rows 97 262 134 25 26 33 192 128 256), losses := [] }

theorem u11129 : Upper (D 7) (R 7) [96,260,130,17,10,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11130 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 134 25 26 96 192 161 289), lower := (rows 97 262 134 25 26 96 192 128 256), losses := [] }

theorem u11130 : Upper (D 7) (R 7) [96,260,130,17,10,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11131 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 134 25 176 40 65 194 322), lower := (rows 97 262 134 25 176 40 65 128 256), losses := [] }

theorem u11131 : Upper (D 7) (R 7) [96,260,130,17,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11131 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11132 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 262 134 25 176 40 66 193 321), lower := (rows 97 262 134 25 176 40 66 128 256), losses := [] }

theorem u11132 : Upper (D 7) (R 7) [96,260,130,17,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11132 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11133 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 97 262 134 26 145 33 72 224 352), lower := (rows 97 262 134 26 145 33 72 128 256), losses := [] }

theorem u11133 : Upper (D 7) (R 7) [96,260,130,18,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11133 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11134 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 134 26 145 33 96 200 328), lower := (rows 97 262 134 26 145 33 96 128 256), losses := [] }

theorem u11134 : Upper (D 7) (R 7) [96,260,130,18,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11135 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 134 26 176 33 65 200 328), lower := (rows 97 262 134 26 176 33 65 128 256), losses := [] }

theorem u11135 : Upper (D 7) (R 7) [96,260,130,18,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11136 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 262 134 26 176 33 72 193 321), lower := (rows 97 262 134 26 176 33 72 128 256), losses := [] }

theorem u11136 : Upper (D 7) (R 7) [96,260,130,18,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11136 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11137 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 390, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(2,0)], upper := (rows 97 262 134 42 88 33 65 144 400), lower := (rows 97 262 134 42 88 33 65 128 256), losses := [] }

theorem u11137 : Upper (D 7) (R 7) [96,260,130,34,72,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11138 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 134 42 88 33 80 129 385), lower := (rows 97 262 134 42 88 33 80 128 256), losses := [] }

theorem u11138 : Upper (D 7) (R 7) [96,260,130,34,72,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11138 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11139 : Route 9 := (fun mask => (mask,id))

def c11139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11139 : Upper (D 7) (R 7) [96,260,130,34,72,1,128] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,72,1,128] 13 (by decide) (choices 1) [1,16] r11139 c11139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u835
  · exact u836

def b11140 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 134 42 145 33 72 208 336), lower := (rows 97 262 134 42 145 33 72 128 256), losses := [] }

theorem u11140 : Upper (D 7) (R 7) [96,260,130,34,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11140 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11141 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 134 42 145 33 80 200 328), lower := (rows 97 262 134 42 145 33 80 128 256), losses := [] }

theorem u11141 : Upper (D 7) (R 7) [96,260,130,34,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11141 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11142 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 134 42 152 33 65 208 336), lower := (rows 97 262 134 42 152 33 65 128 256), losses := [] }

theorem u11142 : Upper (D 7) (R 7) [96,260,130,34,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11143 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 262 134 42 152 33 80 193 321), lower := (rows 97 262 134 42 152 33 80 128 256), losses := [] }

theorem u11143 : Upper (D 7) (R 7) [96,260,130,34,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11143 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11144 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 134 42 208 33 65 152 280), lower := (rows 97 262 134 42 208 33 65 128 256), losses := [] }

theorem u11144 : Upper (D 7) (R 7) [96,260,130,34,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11145 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 134 42 208 33 72 145 273), lower := (rows 97 262 134 42 208 33 72 128 256), losses := [] }

theorem u11145 : Upper (D 7) (R 7) [96,260,130,34,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11145 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11146 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 134 42 208 33 80 137 265), lower := (rows 97 262 134 42 208 33 80 128 256), losses := [] }

theorem u11146 : Upper (D 7) (R 7) [96,260,130,34,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11146 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11147 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(1,0),(4,1)], upper := (rows 97 262 140 11 145 34 80 224 352), lower := (rows 97 262 140 11 145 34 80 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 46 80 129 257), good := (rows 480 294 174 430 464 34 80 128 256) }] }

theorem u11147 : Upper (D 7) (R 7) [96,260,136,3,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11147 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11148 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 140 11 145 34 96 208 336), lower := (rows 97 262 140 11 145 34 96 128 256), losses := [] }

theorem u11148 : Upper (D 7) (R 7) [96,260,136,3,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11149 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 140 11 145 48 96 194 322), lower := (rows 97 262 140 11 145 48 96 128 256), losses := [] }

theorem u11149 : Upper (D 7) (R 7) [96,260,136,3,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11149 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11150 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 4, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(3,7)], upper := (rows 97 262 140 11 146 33 80 224 352), lower := (rows 97 262 140 11 146 33 80 128 256), losses := [] }

theorem u11150 : Upper (D 7) (R 7) [96,260,136,3,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11150 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11151 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 140 11 146 33 96 208 336), lower := (rows 97 262 140 11 146 33 96 128 256), losses := [] }

theorem u11151 : Upper (D 7) (R 7) [96,260,136,3,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11152 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 262 140 26 145 33 66 224 352), lower := (rows 97 262 140 26 145 33 66 128 256), losses := [] }

theorem u11152 : Upper (D 7) (R 7) [96,260,136,18,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11153 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 140 26 145 33 96 194 322), lower := (rows 97 262 140 26 145 33 96 128 256), losses := [] }

theorem u11153 : Upper (D 7) (R 7) [96,260,136,18,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11154 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 140 26 176 33 65 194 322), lower := (rows 97 262 140 26 176 33 65 128 256), losses := [] }

theorem u11154 : Upper (D 7) (R 7) [96,260,136,18,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11155 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 262 140 26 176 33 66 193 321), lower := (rows 97 262 140 26 176 33 66 128 256), losses := [] }

theorem u11155 : Upper (D 7) (R 7) [96,260,136,18,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11156 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 140 42 82 33 65 144 400), lower := (rows 97 262 140 42 82 33 65 128 256), losses := [] }

theorem u11156 : Upper (D 7) (R 7) [96,260,136,34,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11157 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 140 42 82 33 80 129 385), lower := (rows 97 262 140 42 82 33 80 128 256), losses := [] }

theorem u11157 : Upper (D 7) (R 7) [96,260,136,34,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11157 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11158 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 41, targets := 128 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,0)], upper := (rows 97 262 140 42 82 33 192 145 273), lower := (rows 97 262 140 42 82 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 32 196 128 256), good := (rows 96 342 204 58 82 32 192 192 256) }] }

theorem u11158 : Upper (D 7) (R 7) [96,260,136,34,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11159 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 140 42 145 33 66 208 336), lower := (rows 97 262 140 42 145 33 66 128 256), losses := [] }

theorem u11159 : Upper (D 7) (R 7) [96,260,136,34,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11159
end Delivery.IrregularNine14.P07
