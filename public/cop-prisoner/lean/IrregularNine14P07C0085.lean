import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5100 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(4,1),(4,7)], upper := (rows 35 70 13 138 112 288 192 145 273), lower := (rows 35 70 13 138 112 288 192 128 256), losses := [] }

theorem u5100 : Upper (D 7) (R 7) [34,68,9,130,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5100 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5101 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 13 138 145 288 80 224 352), lower := (rows 35 70 13 138 145 288 80 128 256), losses := [] }

theorem u5101 : Upper (D 7) (R 7) [34,68,9,130,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5101 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5102 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,7),(4,1)], upper := (rows 35 70 13 138 145 288 96 208 336), lower := (rows 35 70 13 138 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 304 369 144 272), good := (rows 98 70 78 138 496 352 96 128 352) },{ target := 7, region := (rows 1 6 4 8 16 304 369 0 272), good := (rows 99 70 79 10 369 352 96 0 352) }] }

theorem u5102 : Upper (D 7) (R 7) [34,68,9,130,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5102 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5103 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 13 138 176 288 65 208 336), lower := (rows 35 70 13 138 176 288 65 128 256), losses := [] }

theorem u5103 : Upper (D 7) (R 7) [34,68,9,130,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5103 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5104 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7),(4,1)], upper := (rows 35 70 13 138 176 288 80 193 321), lower := (rows 35 70 13 138 176 288 80 128 256), losses := [] }

theorem u5104 : Upper (D 7) (R 7) [34,68,9,130,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5104 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5105 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 13 138 208 288 65 176 304), lower := (rows 35 70 13 138 208 288 65 128 256), losses := [] }

theorem u5105 : Upper (D 7) (R 7) [34,68,9,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5105 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5106 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 13 138 208 288 80 161 289), lower := (rows 35 70 13 138 208 288 80 128 256), losses := [] }

theorem u5106 : Upper (D 7) (R 7) [34,68,9,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5106 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5107 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,7),(4,1)], upper := (rows 35 70 13 138 208 288 96 145 273), lower := (rows 35 70 13 138 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 288 353 128 256), good := (rows 98 70 78 138 208 352 96 128 352) },{ target := 7, region := (rows 1 6 4 8 16 288 353 0 256), good := (rows 99 70 79 10 80 352 96 0 352) }] }

theorem u5107 : Upper (D 7) (R 7) [34,68,9,130,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5107 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5108 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 13 138 400 48 65 224 352), lower := (rows 35 70 13 138 400 48 65 128 256), losses := [] }

theorem u5108 : Upper (D 7) (R 7) [34,68,9,130,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5108 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5109 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(1,7),(4,1)], upper := (rows 35 70 13 138 400 48 96 193 321), lower := (rows 35 70 13 138 400 48 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 48 113 128 256), good := (rows 98 70 78 138 496 112 96 128 256) },{ target := 7, region := (rows 1 6 4 8 16 48 113 0 261), good := (rows 355 326 335 10 368 112 96 0 256) }] }

theorem u5109 : Upper (D 7) (R 7) [34,68,9,130,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5109 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5110 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,1),(4,7)], upper := (rows 35 70 13 152 112 288 65 130 386), lower := (rows 35 70 13 152 112 288 65 128 256), losses := [] }

theorem u5110 : Upper (D 7) (R 7) [34,68,9,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5110 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5111 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 35 70 13 152 112 288 66 129 385), lower := (rows 35 70 13 152 112 288 66 128 256), losses := [] }

theorem u5111 : Upper (D 7) (R 7) [34,68,9,144,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5111 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5112 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(4,7)], upper := (rows 35 70 13 152 112 288 192 131 259), lower := (rows 35 70 13 152 112 288 192 128 256), losses := [] }

theorem u5112 : Upper (D 7) (R 7) [34,68,9,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5112 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5113 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 152 274 160 65 224 352), lower := (rows 35 70 13 152 274 160 65 128 256), losses := [] }

theorem u5113 : Upper (D 7) (R 7) [34,68,9,144,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5114 : Route 9 := (fun mask => (mask,id))

def c5114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5114 : Upper (D 7) (R 7) [34,68,9,144,258,128,32] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,258,128,32] 13 (by decide) (choices 1) [1,64] r5114 c5114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u382
  · exact u383

def b5115 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,7)], upper := (rows 35 70 13 152 304 160 65 194 322), lower := (rows 35 70 13 152 304 160 65 128 256), losses := [] }

theorem u5115 : Upper (D 7) (R 7) [34,68,9,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5116 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 66, targets := 1 },{ cop := 2, region := 66, targets := 32 },{ cop := 2, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(4,7)], upper := (rows 35 70 13 152 304 160 66 193 321), lower := (rows 35 70 13 152 304 160 66 128 256), losses := [] }

theorem u5116 : Upper (D 7) (R 7) [34,68,9,144,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5117 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 152 336 160 65 162 290), lower := (rows 35 70 13 152 336 160 65 128 256), losses := [] }

theorem u5117 : Upper (D 7) (R 7) [34,68,9,144,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5118 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(4,7)], upper := (rows 35 70 13 152 336 160 66 161 289), lower := (rows 35 70 13 152 336 160 66 128 256), losses := [] }

theorem u5118 : Upper (D 7) (R 7) [34,68,9,144,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5119 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(1,7),(4,7)], upper := (rows 35 70 13 152 336 160 96 131 259), lower := (rows 35 70 13 152 336 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 237 128 256), good := (rows 98 70 110 248 336 224 96 224 256) },{ target := 7, region := (rows 1 6 4 8 23 32 97 0 261), good := (rows 371 342 351 24 336 96 96 0 256) }] }

theorem u5119 : Upper (D 7) (R 7) [34,68,9,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5120 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 168 81 288 66 144 400), lower := (rows 35 70 13 168 81 288 66 128 256), losses := [] }

theorem u5120 : Upper (D 7) (R 7) [34,68,9,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5120 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5121 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 13 168 81 288 80 130 386), lower := (rows 35 70 13 168 81 288 80 128 256), losses := [] }

theorem u5121 : Upper (D 7) (R 7) [34,68,9,160,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5121 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5122 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 305, targets := 128 },{ cop := 2, region := 210, targets := 32 }], pairs := [(0,7),(1,5),(4,7)], upper := (rows 35 70 13 168 81 288 192 146 274), lower := (rows 35 70 13 168 81 288 192 128 256), losses := [] }

theorem u5122 : Upper (D 7) (R 7) [34,68,9,160,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5122 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5123 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 168 145 288 66 208 336), lower := (rows 35 70 13 168 145 288 66 128 256), losses := [] }

theorem u5123 : Upper (D 7) (R 7) [34,68,9,160,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5123 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5124 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 70 13 168 145 288 80 194 322), lower := (rows 35 70 13 168 145 288 80 128 256), losses := [] }

theorem u5124 : Upper (D 7) (R 7) [34,68,9,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5124 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5125 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 168 208 288 65 146 274), lower := (rows 35 70 13 168 208 288 65 128 256), losses := [] }

theorem u5125 : Upper (D 7) (R 7) [34,68,9,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5125 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5126 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 168 208 288 66 145 273), lower := (rows 35 70 13 168 208 288 66 128 256), losses := [] }

theorem u5126 : Upper (D 7) (R 7) [34,68,9,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5126 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5127 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 13 168 208 288 80 131 259), lower := (rows 35 70 13 168 208 288 80 128 256), losses := [] }

theorem u5127 : Upper (D 7) (R 7) [34,68,9,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5127 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5128 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 13 200 145 288 66 176 304), lower := (rows 35 70 13 200 145 288 66 128 256), losses := [] }

theorem u5128 : Upper (D 7) (R 7) [34,68,9,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5128 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5129 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 13 200 145 288 80 162 290), lower := (rows 35 70 13 200 145 288 80 128 256), losses := [] }

theorem u5129 : Upper (D 7) (R 7) [34,68,9,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5129 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5130 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 70 13 200 145 288 96 146 274), lower := (rows 35 70 13 200 145 288 96 128 256), losses := [] }

theorem u5130 : Upper (D 7) (R 7) [34,68,9,192,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5130 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5131 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 70 13 200 176 288 65 146 274), lower := (rows 35 70 13 200 176 288 65 128 256), losses := [] }

theorem u5131 : Upper (D 7) (R 7) [34,68,9,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5131 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5132 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 13 200 176 288 66 145 273), lower := (rows 35 70 13 200 176 288 66 128 256), losses := [] }

theorem u5132 : Upper (D 7) (R 7) [34,68,9,192,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5132 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5133 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 13 200 176 288 80 131 259), lower := (rows 35 70 13 200 176 288 80 128 256), losses := [] }

theorem u5133 : Upper (D 7) (R 7) [34,68,9,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5133 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5134 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 35 70 13 266 81 160 80 160 416), lower := (rows 35 70 13 266 81 160 80 128 256), losses := [] }

theorem u5134 : Upper (D 7) (R 7) [34,68,9,258,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5134 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5135 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 70 13 266 81 160 96 144 400), lower := (rows 35 70 13 266 81 160 96 128 256), losses := [] }

theorem u5135 : Upper (D 7) (R 7) [34,68,9,258,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5136 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,6),(4,1),(4,5)], upper := (rows 35 70 13 266 81 160 192 176 304), lower := (rows 35 70 13 266 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 224 128 256), good := (rows 83 70 29 266 81 192 192 192 256) },{ target := 6, region := (rows 3 2 12 8 16 240 0 144 272), good := (rows 35 39 13 271 433 160 160 160 256) }] }

theorem u5136 : Upper (D 7) (R 7) [34,68,9,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5137 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 266 112 160 65 144 400), lower := (rows 35 70 13 266 112 160 65 128 256), losses := [] }

theorem u5137 : Upper (D 7) (R 7) [34,68,9,258,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5138 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 13 266 112 160 80 129 385), lower := (rows 35 70 13 266 112 160 80 128 256), losses := [] }

theorem u5138 : Upper (D 7) (R 7) [34,68,9,258,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5138 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5139 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 266 112 160 192 145 273), lower := (rows 35 70 13 266 112 160 192 128 256), losses := [] }

theorem u5139 : Upper (D 7) (R 7) [34,68,9,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5140 : Route 9 := (fun mask => (mask,id))

def c5140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5140 : Upper (D 7) (R 7) [34,68,9,258,129,128,16] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,129,128,16] 13 (by decide) (choices 1) [32,64] r5140 c5140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u384
  · exact u385

def b5141 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,7),(2,7),(4,1)], upper := (rows 35 70 13 266 145 160 96 208 336), lower := (rows 35 70 13 266 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 176 241 144 272), good := (rows 98 70 78 266 496 224 96 224 256) },{ target := 7, region := (rows 1 22 20 24 16 32 97 0 272), good := (rows 99 70 79 266 351 96 96 0 256) }] }

theorem u5141 : Upper (D 7) (R 7) [34,68,9,258,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5142 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 266 208 160 65 176 304), lower := (rows 35 70 13 266 208 160 65 128 256), losses := [] }

theorem u5142 : Upper (D 7) (R 7) [34,68,9,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5143 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 13 266 208 160 80 161 289), lower := (rows 35 70 13 266 208 160 80 128 256), losses := [] }

theorem u5143 : Upper (D 7) (R 7) [34,68,9,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5143 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5144 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 80, targets := 3 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 35 70 13 266 208 160 96 145 273), lower := (rows 35 70 13 266 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 176 176 241 128 256), good := (rows 114 70 78 266 240 240 112 240 256) },{ target := 7, region := (rows 1 6 4 8 16 32 97 0 256), good := (rows 99 70 79 266 80 96 96 0 256) }] }

theorem u5144 : Upper (D 7) (R 7) [34,68,9,258,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5145 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 35 70 13 280 112 160 65 130 386), lower := (rows 35 70 13 280 112 160 65 128 256), losses := [] }

theorem u5145 : Upper (D 7) (R 7) [34,68,9,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5146 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 35 70 13 280 112 160 66 129 385), lower := (rows 35 70 13 280 112 160 66 128 256), losses := [] }

theorem u5146 : Upper (D 7) (R 7) [34,68,9,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5147 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 280 112 160 192 131 259), lower := (rows 35 70 13 280 112 160 192 128 256), losses := [] }

theorem u5147 : Upper (D 7) (R 7) [34,68,9,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5148 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 280 146 160 65 224 352), lower := (rows 35 70 13 280 146 160 65 128 256), losses := [] }

theorem u5148 : Upper (D 7) (R 7) [34,68,9,272,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5149 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 35 70 13 280 146 160 96 193 321), lower := (rows 35 70 13 280 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 176 249 128 256), good := (rows 98 70 78 376 242 224 96 224 256) },{ target := 6, region := (rows 17 2 12 8 16 176 0 128 256), good := (rows 35 6 13 317 179 160 32 160 256) },{ target := 7, region := (rows 1 6 4 8 16 32 97 0 261), good := (rows 355 326 335 280 18 96 96 0 256) }] }

theorem u5149 : Upper (D 7) (R 7) [34,68,9,272,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5150 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 13 280 208 160 65 162 290), lower := (rows 35 70 13 280 208 160 65 128 256), losses := [] }

theorem u5150 : Upper (D 7) (R 7) [34,68,9,272,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5151 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(1,7)], upper := (rows 35 70 13 280 208 160 66 161 289), lower := (rows 35 70 13 280 208 160 66 128 256), losses := [] }

theorem u5151 : Upper (D 7) (R 7) [34,68,9,272,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5152 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(4,0),(4,1)], upper := (rows 35 70 13 280 208 160 96 131 259), lower := (rows 35 70 13 280 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 176 176 249 128 256), good := (rows 114 70 78 376 240 240 112 240 256) }] }

theorem u5152 : Upper (D 7) (R 7) [34,68,9,272,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5153 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 13 296 81 160 66 144 400), lower := (rows 35 70 13 296 81 160 66 128 256), losses := [] }

theorem u5153 : Upper (D 7) (R 7) [34,68,9,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5154 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 296 81 160 80 130 386), lower := (rows 35 70 13 296 81 160 80 128 256), losses := [] }

theorem u5154 : Upper (D 7) (R 7) [34,68,9,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5154 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5155 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(0,6),(1,5),(4,1),(4,5)], upper := (rows 35 70 13 296 81 160 192 146 274), lower := (rows 35 70 13 296 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 113 100 29 360 113 224 224 224 256) },{ target := 6, region := (rows 3 2 4 8 16 224 0 128 256), good := (rows 35 39 13 296 49 160 160 160 256) }] }

theorem u5155 : Upper (D 7) (R 7) [34,68,9,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5156 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 2, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 70 13 296 145 160 66 208 336), lower := (rows 35 70 13 296 145 160 66 128 256), losses := [] }

theorem u5156 : Upper (D 7) (R 7) [34,68,9,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5157 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 1, region := 424, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 70 13 296 145 160 80 194 322), lower := (rows 35 70 13 296 145 160 80 128 256), losses := [] }

theorem u5157 : Upper (D 7) (R 7) [34,68,9,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5157 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5158 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 296 146 160 65 208 336), lower := (rows 35 70 13 296 146 160 65 128 256), losses := [] }

theorem u5158 : Upper (D 7) (R 7) [34,68,9,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5159 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 35 70 13 296 146 160 80 193 321), lower := (rows 35 70 13 296 146 160 80 128 256), losses := [] }

theorem u5159 : Upper (D 7) (R 7) [34,68,9,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5159 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5159
end Delivery.IrregularNine14.P07
