import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0012

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6120 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 98 37 56 84 40 193 129 385), lower := (rows 259 98 37 56 84 40 64 128 256), losses := [] }

theorem u6120 : Upper (D 8) (R 8) [258,96,33,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6120 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6121 : Route 9 := (fun mask => (mask,id))

def c6121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6121 : Upper (D 8) (R 8) [258,96,33,48,68,128] 13 := by
  apply FastRouting.sound _ _ [258,96,33,48,68,128] 13 (by decide) (choices 1) [1,8,128] r6121 c6121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u763
  · exact u764
  · exact u765

def b6122 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 259 98 37 56 145 36 200 200 456), lower := (rows 259 98 37 56 145 36 64 128 256), losses := [] }

theorem u6122 : Upper (D 8) (R 8) [258,96,33,48,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6122 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6123 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 259 98 37 56 145 40 196 196 452), lower := (rows 259 98 37 56 145 40 64 128 256), losses := [] }

theorem u6123 : Upper (D 8) (R 8) [258,96,33,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6123 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6124 : PairBound 9 := { available := 140, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 37 56 145 96 204 140 396), lower := (rows 259 98 37 56 145 96 64 128 256), losses := [] }

theorem u6124 : Upper (D 8) (R 8) [258,96,33,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6125 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 56 145 160 76 204 332), lower := (rows 259 98 37 56 145 160 64 128 256), losses := [] }

theorem u6125 : Upper (D 8) (R 8) [258,96,33,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6126 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 56 148 33 200 200 456), lower := (rows 259 98 37 56 148 33 64 128 256), losses := [] }

theorem u6126 : Upper (D 8) (R 8) [258,96,33,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6127 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 98 37 56 148 40 193 193 449), lower := (rows 259 98 37 56 148 40 64 128 256), losses := [] }

theorem u6127 : Upper (D 8) (R 8) [258,96,33,48,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6127 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6128 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 37 56 148 96 201 137 393), lower := (rows 259 98 37 56 148 96 64 128 256), losses := [] }

theorem u6128 : Upper (D 8) (R 8) [258,96,33,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6129 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 56 148 160 73 201 329), lower := (rows 259 98 37 56 148 160 64 128 256), losses := [] }

theorem u6129 : Upper (D 8) (R 8) [258,96,33,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6130 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 56 152 33 196 196 452), lower := (rows 259 98 37 56 152 33 64 128 256), losses := [] }

theorem u6130 : Upper (D 8) (R 8) [258,96,33,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6131 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 98 37 56 152 36 193 193 449), lower := (rows 259 98 37 56 152 36 64 128 256), losses := [] }

theorem u6131 : Upper (D 8) (R 8) [258,96,33,48,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6131 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6132 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 37 56 152 96 197 133 389), lower := (rows 259 98 37 56 152 96 64 128 256), losses := [] }

theorem u6132 : Upper (D 8) (R 8) [258,96,33,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6133 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 37 56 152 160 69 197 325), lower := (rows 259 98 37 56 152 160 64 128 256), losses := [] }

theorem u6133 : Upper (D 8) (R 8) [258,96,33,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6134 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 56 208 33 204 140 396), lower := (rows 259 98 37 56 208 33 64 128 256), losses := [] }

theorem u6134 : Upper (D 8) (R 8) [258,96,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6135 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 98 37 56 208 36 201 137 393), lower := (rows 259 98 37 56 208 36 64 128 256), losses := [] }

theorem u6135 : Upper (D 8) (R 8) [258,96,33,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6135 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6136 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 98 37 56 208 40 197 133 389), lower := (rows 259 98 37 56 208 40 64 128 256), losses := [] }

theorem u6136 : Upper (D 8) (R 8) [258,96,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6136 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6137 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 56 208 160 77 141 269), lower := (rows 259 98 37 56 208 160 64 128 256), losses := [] }

theorem u6137 : Upper (D 8) (R 8) [258,96,33,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6138 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 259 98 37 76 145 40 240 176 432), lower := (rows 259 98 37 76 145 40 64 128 256), losses := [] }

theorem u6138 : Upper (D 8) (R 8) [258,96,33,68,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6138 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6139 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 259 98 37 76 145 48 232 168 424), lower := (rows 259 98 37 76 145 48 64 128 256), losses := [] }

theorem u6139 : Upper (D 8) (R 8) [258,96,33,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6139 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6140 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 37 76 145 160 120 184 312), lower := (rows 259 98 37 76 145 160 64 128 256), losses := [] }

theorem u6140 : Upper (D 8) (R 8) [258,96,33,68,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6141 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 76 152 33 240 176 432), lower := (rows 259 98 37 76 152 33 64 128 256), losses := [] }

theorem u6141 : Upper (D 8) (R 8) [258,96,33,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6142 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 37 76 152 48 225 161 417), lower := (rows 259 98 37 76 152 48 64 128 256), losses := [] }

theorem u6142 : Upper (D 8) (R 8) [258,96,33,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6142 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6143 : Route 9 := (fun mask => (mask,id))

def c6143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6143 : Upper (D 8) (R 8) [258,96,33,68,136,128] 13 := by
  apply FastRouting.sound _ _ [258,96,33,68,136,128] 13 (by decide) (choices 1) [1,16,32] r6143 c6143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u766
  · exact u767
  · exact u768

def b6144 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 76 176 33 216 152 408), lower := (rows 259 98 37 76 176 33 64 128 256), losses := [] }

theorem u6144 : Upper (D 8) (R 8) [258,96,33,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6145 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 98 37 76 176 40 209 145 401), lower := (rows 259 98 37 76 176 40 64 128 256), losses := [] }

theorem u6145 : Upper (D 8) (R 8) [258,96,33,68,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6145 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6146 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 98 37 76 176 48 201 137 393), lower := (rows 259 98 37 76 176 48 64 128 256), losses := [] }

theorem u6146 : Upper (D 8) (R 8) [258,96,33,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6146 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6147 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 76 176 160 89 153 281), lower := (rows 259 98 37 76 176 160 64 128 256), losses := [] }

theorem u6147 : Upper (D 8) (R 8) [258,96,33,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6148 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 259 98 37 88 145 36 232 168 424), lower := (rows 259 98 37 88 145 36 64 128 256), losses := [] }

theorem u6148 : Upper (D 8) (R 8) [258,96,33,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6148 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6149 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 259 98 37 88 145 40 228 164 420), lower := (rows 259 98 37 88 145 40 64 128 256), losses := [] }

theorem u6149 : Upper (D 8) (R 8) [258,96,33,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6149 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6150 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 37 88 145 160 108 172 300), lower := (rows 259 98 37 88 145 160 64 128 256), losses := [] }

theorem u6150 : Upper (D 8) (R 8) [258,96,33,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6151 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 88 148 33 232 168 424), lower := (rows 259 98 37 88 148 33 64 128 256), losses := [] }

theorem u6151 : Upper (D 8) (R 8) [258,96,33,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6152 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 37 88 148 40 225 161 417), lower := (rows 259 98 37 88 148 40 64 128 256), losses := [] }

theorem u6152 : Upper (D 8) (R 8) [258,96,33,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6152 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6153 : PairBound 9 := { available := 41, camps := [], pairs := [(1,0)], upper := (rows 259 98 37 88 148 160 105 169 297), lower := (rows 259 98 37 88 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 258 98 36 122 180 160 64 160 256) }] }

theorem u6153 : Upper (D 8) (R 8) [258,96,33,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6154 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 88 176 33 204 140 396), lower := (rows 259 98 37 88 176 33 64 128 256), losses := [] }

theorem u6154 : Upper (D 8) (R 8) [258,96,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6155 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 98 37 88 176 36 201 137 393), lower := (rows 259 98 37 88 176 36 64 128 256), losses := [] }

theorem u6155 : Upper (D 8) (R 8) [258,96,33,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6155 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6156 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 98 37 88 176 40 197 133 389), lower := (rows 259 98 37 88 176 40 64 128 256), losses := [] }

theorem u6156 : Upper (D 8) (R 8) [258,96,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6156 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6157 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 88 176 160 77 141 269), lower := (rows 259 98 37 88 176 160 64 128 256), losses := [] }

theorem u6157 : Upper (D 8) (R 8) [258,96,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6158 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 259 98 37 137 148 40 112 240 368), lower := (rows 259 98 37 137 148 40 64 128 256), losses := [] }

theorem u6158 : Upper (D 8) (R 8) [258,96,33,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6158 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6159 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 259 98 37 137 148 48 104 232 360), lower := (rows 259 98 37 137 148 48 64 128 256), losses := [] }

theorem u6159 : Upper (D 8) (R 8) [258,96,33,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6159 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6160 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 37 137 148 96 120 184 312), lower := (rows 259 98 37 137 148 96 64 128 256), losses := [] }

theorem u6160 : Upper (D 8) (R 8) [258,96,33,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6161 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 259 98 37 137 176 36 88 216 344), lower := (rows 259 98 37 137 176 36 64 128 256), losses := [] }

theorem u6161 : Upper (D 8) (R 8) [258,96,33,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6161 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6162 : PairBound 9 := { available := 84, camps := [], pairs := [], upper := (rows 259 98 37 137 176 40 84 212 340), lower := (rows 259 98 37 137 176 40 64 128 256), losses := [] }

theorem u6162 : Upper (D 8) (R 8) [258,96,33,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6162 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6163 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 259 98 37 137 176 48 76 204 332), lower := (rows 259 98 37 137 176 48 64 128 256), losses := [] }

theorem u6163 : Upper (D 8) (R 8) [258,96,33,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6163 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6164 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 37 137 176 96 92 156 284), lower := (rows 259 98 37 137 176 96 64 128 256), losses := [] }

theorem u6164 : Upper (D 8) (R 8) [258,96,33,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6165 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 259 98 37 137 208 36 120 184 312), lower := (rows 259 98 37 137 208 36 64 128 256), losses := [] }

theorem u6165 : Upper (D 8) (R 8) [258,96,33,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6165 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6166 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 259 98 37 137 208 40 116 180 308), lower := (rows 259 98 37 137 208 40 64 128 256), losses := [] }

theorem u6166 : Upper (D 8) (R 8) [258,96,33,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6166 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6167 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 259 98 37 137 208 48 108 172 300), lower := (rows 259 98 37 137 208 48 64 128 256), losses := [] }

theorem u6167 : Upper (D 8) (R 8) [258,96,33,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6167 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6168 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 140 176 33 88 216 344), lower := (rows 259 98 37 140 176 33 64 128 256), losses := [] }

theorem u6168 : Upper (D 8) (R 8) [258,96,33,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6169 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 259 98 37 140 176 40 81 209 337), lower := (rows 259 98 37 140 176 40 64 128 256), losses := [] }

theorem u6169 : Upper (D 8) (R 8) [258,96,33,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6169 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6170 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 259 98 37 140 176 48 73 201 329), lower := (rows 259 98 37 140 176 48 64 128 256), losses := [] }

theorem u6170 : Upper (D 8) (R 8) [258,96,33,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6170 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6171 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 37 140 176 96 89 153 281), lower := (rows 259 98 37 140 176 96 64 128 256), losses := [] }

theorem u6171 : Upper (D 8) (R 8) [258,96,33,132,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6172 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 140 208 33 120 184 312), lower := (rows 259 98 37 140 208 33 64 128 256), losses := [] }

theorem u6172 : Upper (D 8) (R 8) [258,96,33,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6173 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 98 37 140 208 40 113 177 305), lower := (rows 259 98 37 140 208 40 64 128 256), losses := [] }

theorem u6173 : Upper (D 8) (R 8) [258,96,33,132,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6173 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6174 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 98 37 140 208 48 105 169 297), lower := (rows 259 98 37 140 208 48 64 128 256), losses := [] }

theorem u6174 : Upper (D 8) (R 8) [258,96,33,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6174 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6175 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 168 208 33 92 156 284), lower := (rows 259 98 37 168 208 33 64 128 256), losses := [] }

theorem u6175 : Upper (D 8) (R 8) [258,96,33,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6176 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 259 98 37 168 208 36 89 153 281), lower := (rows 259 98 37 168 208 36 64 128 256), losses := [] }

theorem u6176 : Upper (D 8) (R 8) [258,96,33,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6176 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6177 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 259 98 37 168 208 40 85 149 277), lower := (rows 259 98 37 168 208 40 64 128 256), losses := [] }

theorem u6177 : Upper (D 8) (R 8) [258,96,33,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6177 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6178 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 259 98 37 168 208 48 77 141 269), lower := (rows 259 98 37 168 208 48 64 128 256), losses := [] }

theorem u6178 : Upper (D 8) (R 8) [258,96,33,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6178 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6179 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 44 88 145 33 228 164 420), lower := (rows 259 98 44 88 145 33 64 128 256), losses := [] }

theorem u6179 : Upper (D 8) (R 8) [258,96,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6179
end Delivery.IrregularNine14.P08
