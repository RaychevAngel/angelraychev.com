import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0011

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5100 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 38 196 56 273 34 201 137 393), lower := (rows 97 38 196 56 273 34 64 128 256), losses := [] }

theorem u5100 : Upper (D 8) (R 8) [96,36,192,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5100 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5101 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 196 56 273 40 195 131 387), lower := (rows 97 38 196 56 273 40 64 128 256), losses := [] }

theorem u5101 : Upper (D 8) (R 8) [96,36,192,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5101 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5102 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 56 273 160 75 139 267), lower := (rows 97 38 196 56 273 160 64 128 256), losses := [] }

theorem u5102 : Upper (D 8) (R 8) [96,36,192,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5103 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 56 274 33 201 137 393), lower := (rows 97 38 196 56 274 33 64 128 256), losses := [] }

theorem u5103 : Upper (D 8) (R 8) [96,36,192,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5104 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 196 56 274 40 193 129 385), lower := (rows 97 38 196 56 274 40 64 128 256), losses := [] }

theorem u5104 : Upper (D 8) (R 8) [96,36,192,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5104 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5105 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 56 274 160 73 137 265), lower := (rows 97 38 196 56 274 160 64 128 256), losses := [] }

theorem u5105 : Upper (D 8) (R 8) [96,36,192,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5106 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 56 280 33 195 131 387), lower := (rows 97 38 196 56 280 33 64 128 256), losses := [] }

theorem u5106 : Upper (D 8) (R 8) [96,36,192,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5107 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 196 56 280 34 193 129 385), lower := (rows 97 38 196 56 280 34 64 128 256), losses := [] }

theorem u5107 : Upper (D 8) (R 8) [96,36,192,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5107 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5108 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 56 280 160 67 131 259), lower := (rows 97 38 196 56 280 160 64 128 256), losses := [] }

theorem u5108 : Upper (D 8) (R 8) [96,36,192,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5109 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 56 400 33 75 139 267), lower := (rows 97 38 196 56 400 33 64 128 256), losses := [] }

theorem u5109 : Upper (D 8) (R 8) [96,36,192,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5110 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 196 56 400 34 73 137 265), lower := (rows 97 38 196 56 400 34 64 128 256), losses := [] }

theorem u5110 : Upper (D 8) (R 8) [96,36,192,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5110 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5111 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 196 56 400 40 67 131 259), lower := (rows 97 38 196 56 400 40 64 128 256), losses := [] }

theorem u5111 : Upper (D 8) (R 8) [96,36,192,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5111 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5112 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 38 196 137 273 34 120 184 312), lower := (rows 97 38 196 137 273 34 64 128 256), losses := [] }

theorem u5112 : Upper (D 8) (R 8) [96,36,192,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5112 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5113 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 38 196 137 273 40 114 178 306), lower := (rows 97 38 196 137 273 40 64 128 256), losses := [] }

theorem u5113 : Upper (D 8) (R 8) [96,36,192,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5113 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5114 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 38 196 137 273 48 106 170 298), lower := (rows 97 38 196 137 273 48 64 128 256), losses := [] }

theorem u5114 : Upper (D 8) (R 8) [96,36,192,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5114 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5115 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 137 274 33 120 184 312), lower := (rows 97 38 196 137 274 33 64 128 256), losses := [] }

theorem u5115 : Upper (D 8) (R 8) [96,36,192,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5116 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 196 137 274 40 113 177 305), lower := (rows 97 38 196 137 274 40 64 128 256), losses := [] }

theorem u5116 : Upper (D 8) (R 8) [96,36,192,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5116 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5117 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 196 137 274 48 105 169 297), lower := (rows 97 38 196 137 274 48 64 128 256), losses := [] }

theorem u5117 : Upper (D 8) (R 8) [96,36,192,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5117 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5118 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 137 280 33 114 178 306), lower := (rows 97 38 196 137 280 33 64 128 256), losses := [] }

theorem u5118 : Upper (D 8) (R 8) [96,36,192,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5119 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 196 137 280 34 113 177 305), lower := (rows 97 38 196 137 280 34 64 128 256), losses := [] }

theorem u5119 : Upper (D 8) (R 8) [96,36,192,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5119 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5120 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 196 137 280 48 99 163 291), lower := (rows 97 38 196 137 280 48 64 128 256), losses := [] }

theorem u5120 : Upper (D 8) (R 8) [96,36,192,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5120 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5121 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 137 304 33 90 154 282), lower := (rows 97 38 196 137 304 33 64 128 256), losses := [] }

theorem u5121 : Upper (D 8) (R 8) [96,36,192,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5122 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 196 137 304 34 89 153 281), lower := (rows 97 38 196 137 304 34 64 128 256), losses := [] }

theorem u5122 : Upper (D 8) (R 8) [96,36,192,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5122 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5123 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 196 137 304 40 83 147 275), lower := (rows 97 38 196 137 304 40 64 128 256), losses := [] }

theorem u5123 : Upper (D 8) (R 8) [96,36,192,129,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5123 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5124 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 196 137 304 48 75 139 267), lower := (rows 97 38 196 137 304 48 64 128 256), losses := [] }

theorem u5124 : Upper (D 8) (R 8) [96,36,192,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5124 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5125 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 152 273 33 106 170 298), lower := (rows 97 38 196 152 273 33 64 128 256), losses := [] }

theorem u5125 : Upper (D 8) (R 8) [96,36,192,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5126 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 196 152 273 34 105 169 297), lower := (rows 97 38 196 152 273 34 64 128 256), losses := [] }

theorem u5126 : Upper (D 8) (R 8) [96,36,192,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5126 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5127 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 196 152 273 40 99 163 291), lower := (rows 97 38 196 152 273 40 64 128 256), losses := [] }

theorem u5127 : Upper (D 8) (R 8) [96,36,192,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5127 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5128 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 152 304 33 75 139 267), lower := (rows 97 38 196 152 304 33 64 128 256), losses := [] }

theorem u5128 : Upper (D 8) (R 8) [96,36,192,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5129 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 196 152 304 34 73 137 265), lower := (rows 97 38 196 152 304 34 64 128 256), losses := [] }

theorem u5129 : Upper (D 8) (R 8) [96,36,192,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5129 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5130 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 196 152 304 40 67 131 259), lower := (rows 97 38 196 152 304 40 64 128 256), losses := [] }

theorem u5130 : Upper (D 8) (R 8) [96,36,192,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5130 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5131 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 168 273 33 90 154 282), lower := (rows 97 38 196 168 273 33 64 128 256), losses := [] }

theorem u5131 : Upper (D 8) (R 8) [96,36,192,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5132 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 196 168 273 34 89 153 281), lower := (rows 97 38 196 168 273 34 64 128 256), losses := [] }

theorem u5132 : Upper (D 8) (R 8) [96,36,192,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5132 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5133 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 196 168 273 40 83 147 275), lower := (rows 97 38 196 168 273 40 64 128 256), losses := [] }

theorem u5133 : Upper (D 8) (R 8) [96,36,192,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5133 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5134 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 196 168 273 48 75 139 267), lower := (rows 97 38 196 168 273 48 64 128 256), losses := [] }

theorem u5134 : Upper (D 8) (R 8) [96,36,192,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5134 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5135 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 168 274 33 89 153 281), lower := (rows 97 38 196 168 274 33 64 128 256), losses := [] }

theorem u5135 : Upper (D 8) (R 8) [96,36,192,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5136 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 196 168 274 40 81 145 273), lower := (rows 97 38 196 168 274 40 64 128 256), losses := [] }

theorem u5136 : Upper (D 8) (R 8) [96,36,192,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5136 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5137 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 196 168 274 48 73 137 265), lower := (rows 97 38 196 168 274 48 64 128 256), losses := [] }

theorem u5137 : Upper (D 8) (R 8) [96,36,192,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5137 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5138 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 168 280 33 83 147 275), lower := (rows 97 38 196 168 280 33 64 128 256), losses := [] }

theorem u5138 : Upper (D 8) (R 8) [96,36,192,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5139 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 196 168 280 34 81 145 273), lower := (rows 97 38 196 168 280 34 64 128 256), losses := [] }

theorem u5139 : Upper (D 8) (R 8) [96,36,192,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5139 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5140 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 196 168 280 48 67 131 259), lower := (rows 97 38 196 168 280 48 64 128 256), losses := [] }

theorem u5140 : Upper (D 8) (R 8) [96,36,192,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5140 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5141 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 97 38 261 74 145 40 240 176 432), lower := (rows 97 38 261 74 145 40 64 128 256), losses := [] }

theorem u5141 : Upper (D 8) (R 8) [96,36,257,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5141 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5142 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 38 261 74 145 48 232 168 424), lower := (rows 97 38 261 74 145 48 64 128 256), losses := [] }

theorem u5142 : Upper (D 8) (R 8) [96,36,257,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5142 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5143 : Route 9 := (fun mask => (mask,id))

def c5143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5143 : Upper (D 8) (R 8) [96,36,257,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,36,257,66,129,128] 13 (by decide) (choices 1) [8,16,32] r5143 c5143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u681
  · exact u682
  · exact u683

def b5144 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 74 152 33 240 176 432), lower := (rows 97 38 261 74 152 33 64 128 256), losses := [] }

theorem u5144 : Upper (D 8) (R 8) [96,36,257,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5145 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 261 74 152 48 225 161 417), lower := (rows 97 38 261 74 152 48 64 128 256), losses := [] }

theorem u5145 : Upper (D 8) (R 8) [96,36,257,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5145 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5146 : Route 9 := (fun mask => (mask,id))

def c5146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5146 : Upper (D 8) (R 8) [96,36,257,66,136,128] 13 := by
  apply FastRouting.sound _ _ [96,36,257,66,136,128] 13 (by decide) (choices 1) [1,16,32] r5146 c5146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u684
  · exact u685
  · exact u686

def b5147 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 74 176 33 216 152 408), lower := (rows 97 38 261 74 176 33 64 128 256), losses := [] }

theorem u5147 : Upper (D 8) (R 8) [96,36,257,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5148 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 38 261 74 176 40 209 145 401), lower := (rows 97 38 261 74 176 40 64 128 256), losses := [] }

theorem u5148 : Upper (D 8) (R 8) [96,36,257,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5148 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5149 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 38 261 74 176 48 201 137 393), lower := (rows 97 38 261 74 176 48 64 128 256), losses := [] }

theorem u5149 : Upper (D 8) (R 8) [96,36,257,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5149 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5150 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 74 176 160 89 153 281), lower := (rows 97 38 261 74 176 160 64 128 256), losses := [] }

theorem u5150 : Upper (D 8) (R 8) [96,36,257,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5151 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 38 261 88 145 34 232 168 424), lower := (rows 97 38 261 88 145 34 64 128 256), losses := [] }

theorem u5151 : Upper (D 8) (R 8) [96,36,257,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5151 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5152 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 97 38 261 88 145 40 226 162 418), lower := (rows 97 38 261 88 145 40 64 128 256), losses := [] }

theorem u5152 : Upper (D 8) (R 8) [96,36,257,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5152 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5153 : Route 9 := (fun mask => (mask,id))

def c5153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5153 : Upper (D 8) (R 8) [96,36,257,80,129,128] 13 := by
  apply FastRouting.sound _ _ [96,36,257,80,129,128] 13 (by decide) (choices 1) [2,8,32] r5153 c5153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u687
  · exact u688
  · exact u689

def b5154 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 88 146 33 232 168 424), lower := (rows 97 38 261 88 146 33 64 128 256), losses := [] }

theorem u5154 : Upper (D 8) (R 8) [96,36,257,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5155 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 261 88 146 40 225 161 417), lower := (rows 97 38 261 88 146 40 64 128 256), losses := [] }

theorem u5155 : Upper (D 8) (R 8) [96,36,257,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5155 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5156 : Route 9 := (fun mask => (mask,id))

def c5156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5156 : Upper (D 8) (R 8) [96,36,257,80,130,128] 13 := by
  apply FastRouting.sound _ _ [96,36,257,80,130,128] 13 (by decide) (choices 1) [1,8,32] r5156 c5156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u690
  · exact u691
  · exact u692

def b5157 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 88 176 33 202 138 394), lower := (rows 97 38 261 88 176 33 64 128 256), losses := [] }

theorem u5157 : Upper (D 8) (R 8) [96,36,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5158 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 38 261 88 176 34 201 137 393), lower := (rows 97 38 261 88 176 34 64 128 256), losses := [] }

theorem u5158 : Upper (D 8) (R 8) [96,36,257,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5158 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5159 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 38 261 88 176 40 195 131 387), lower := (rows 97 38 261 88 176 40 64 128 256), losses := [] }

theorem u5159 : Upper (D 8) (R 8) [96,36,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5159 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5159
end Delivery.IrregularNine14.P08
