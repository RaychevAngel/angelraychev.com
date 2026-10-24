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

def b5160 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 88 176 160 75 139 267), lower := (rows 97 38 261 88 176 160 64 128 256), losses := [] }

theorem u5160 : Upper (D 8) (R 8) [96,36,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5161 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 38 261 137 146 40 112 240 368), lower := (rows 97 38 261 137 146 40 64 128 256), losses := [] }

theorem u5161 : Upper (D 8) (R 8) [96,36,257,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5161 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5162 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 38 261 137 146 48 104 232 360), lower := (rows 97 38 261 137 146 48 64 128 256), losses := [] }

theorem u5162 : Upper (D 8) (R 8) [96,36,257,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5162 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5163 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 137 146 96 120 184 312), lower := (rows 97 38 261 137 146 96 64 128 256), losses := [] }

theorem u5163 : Upper (D 8) (R 8) [96,36,257,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5164 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 97 38 261 137 176 34 88 216 344), lower := (rows 97 38 261 137 176 34 64 128 256), losses := [] }

theorem u5164 : Upper (D 8) (R 8) [96,36,257,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5164 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5165 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 97 38 261 137 176 40 82 210 338), lower := (rows 97 38 261 137 176 40 64 128 256), losses := [] }

theorem u5165 : Upper (D 8) (R 8) [96,36,257,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5165 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5166 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 97 38 261 137 176 48 74 202 330), lower := (rows 97 38 261 137 176 48 64 128 256), losses := [] }

theorem u5166 : Upper (D 8) (R 8) [96,36,257,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5166 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5167 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 137 176 96 90 154 282), lower := (rows 97 38 261 137 176 96 64 128 256), losses := [] }

theorem u5167 : Upper (D 8) (R 8) [96,36,257,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5168 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 38 261 137 208 34 120 184 312), lower := (rows 97 38 261 137 208 34 64 128 256), losses := [] }

theorem u5168 : Upper (D 8) (R 8) [96,36,257,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5168 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5169 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 38 261 137 208 40 114 178 306), lower := (rows 97 38 261 137 208 40 64 128 256), losses := [] }

theorem u5169 : Upper (D 8) (R 8) [96,36,257,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5169 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5170 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 38 261 137 208 48 106 170 298), lower := (rows 97 38 261 137 208 48 64 128 256), losses := [] }

theorem u5170 : Upper (D 8) (R 8) [96,36,257,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5170 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5171 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 138 176 33 88 216 344), lower := (rows 97 38 261 138 176 33 64 128 256), losses := [] }

theorem u5171 : Upper (D 8) (R 8) [96,36,257,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5172 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 261 138 176 40 81 209 337), lower := (rows 97 38 261 138 176 40 64 128 256), losses := [] }

theorem u5172 : Upper (D 8) (R 8) [96,36,257,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5172 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5173 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 38 261 138 176 48 73 201 329), lower := (rows 97 38 261 138 176 48 64 128 256), losses := [] }

theorem u5173 : Upper (D 8) (R 8) [96,36,257,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5173 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5174 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 138 176 96 89 153 281), lower := (rows 97 38 261 138 176 96 64 128 256), losses := [] }

theorem u5174 : Upper (D 8) (R 8) [96,36,257,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5175 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 138 208 33 120 184 312), lower := (rows 97 38 261 138 208 33 64 128 256), losses := [] }

theorem u5175 : Upper (D 8) (R 8) [96,36,257,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5176 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 261 138 208 40 113 177 305), lower := (rows 97 38 261 138 208 40 64 128 256), losses := [] }

theorem u5176 : Upper (D 8) (R 8) [96,36,257,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5176 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5177 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 261 138 208 48 105 169 297), lower := (rows 97 38 261 138 208 48 64 128 256), losses := [] }

theorem u5177 : Upper (D 8) (R 8) [96,36,257,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5177 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5178 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 168 208 33 90 154 282), lower := (rows 97 38 261 168 208 33 64 128 256), losses := [] }

theorem u5178 : Upper (D 8) (R 8) [96,36,257,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5179 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 261 168 208 34 89 153 281), lower := (rows 97 38 261 168 208 34 64 128 256), losses := [] }

theorem u5179 : Upper (D 8) (R 8) [96,36,257,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5179 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5180 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 261 168 208 40 83 147 275), lower := (rows 97 38 261 168 208 40 64 128 256), losses := [] }

theorem u5180 : Upper (D 8) (R 8) [96,36,257,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5180 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5181 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 261 168 208 48 75 139 267), lower := (rows 97 38 261 168 208 48 64 128 256), losses := [] }

theorem u5181 : Upper (D 8) (R 8) [96,36,257,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5181 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5182 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 262 88 145 33 232 168 424), lower := (rows 97 38 262 88 145 33 64 128 256), losses := [] }

theorem u5182 : Upper (D 8) (R 8) [96,36,258,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5183 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 262 88 145 40 225 161 417), lower := (rows 97 38 262 88 145 40 64 128 256), losses := [] }

theorem u5183 : Upper (D 8) (R 8) [96,36,258,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5183 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r5184 : Route 9 := (fun mask => (mask,id))

def c5184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5184 : Upper (D 8) (R 8) [96,36,258,80,129,128] 13 := by
  apply FastRouting.sound _ _ [96,36,258,80,129,128] 13 (by decide) (choices 1) [1,8,32] r5184 c5184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u693
  · exact u694
  · exact u695

def b5185 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 262 88 176 33 201 137 393), lower := (rows 97 38 262 88 176 33 64 128 256), losses := [] }

theorem u5185 : Upper (D 8) (R 8) [96,36,258,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5186 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 262 88 176 40 193 129 385), lower := (rows 97 38 262 88 176 40 64 128 256), losses := [] }

theorem u5186 : Upper (D 8) (R 8) [96,36,258,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5186 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5187 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 73, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 262 88 176 160 73 137 265), lower := (rows 97 38 262 88 176 160 64 128 256), losses := [] }

theorem u5187 : Upper (D 8) (R 8) [96,36,258,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5188 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 262 137 176 33 88 216 344), lower := (rows 97 38 262 137 176 33 64 128 256), losses := [] }

theorem u5188 : Upper (D 8) (R 8) [96,36,258,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5189 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 262 137 176 40 81 209 337), lower := (rows 97 38 262 137 176 40 64 128 256), losses := [] }

theorem u5189 : Upper (D 8) (R 8) [96,36,258,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5189 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5190 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 38 262 137 176 48 73 201 329), lower := (rows 97 38 262 137 176 48 64 128 256), losses := [] }

theorem u5190 : Upper (D 8) (R 8) [96,36,258,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5190 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5191 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 262 137 176 96 89 153 281), lower := (rows 97 38 262 137 176 96 64 128 256), losses := [] }

theorem u5191 : Upper (D 8) (R 8) [96,36,258,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5192 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 262 137 208 33 120 184 312), lower := (rows 97 38 262 137 208 33 64 128 256), losses := [] }

theorem u5192 : Upper (D 8) (R 8) [96,36,258,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5193 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 262 137 208 40 113 177 305), lower := (rows 97 38 262 137 208 40 64 128 256), losses := [] }

theorem u5193 : Upper (D 8) (R 8) [96,36,258,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5193 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5194 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 38 262 137 208 48 105 169 297), lower := (rows 97 38 262 137 208 48 64 128 256), losses := [] }

theorem u5194 : Upper (D 8) (R 8) [96,36,258,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5194 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5195 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 262 168 208 33 89 153 281), lower := (rows 97 38 262 168 208 33 64 128 256), losses := [] }

theorem u5195 : Upper (D 8) (R 8) [96,36,258,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5196 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 262 168 208 40 81 145 273), lower := (rows 97 38 262 168 208 40 64 128 256), losses := [] }

theorem u5196 : Upper (D 8) (R 8) [96,36,258,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5196 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5197 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 262 168 208 48 73 137 265), lower := (rows 97 38 262 168 208 48 64 128 256), losses := [] }

theorem u5197 : Upper (D 8) (R 8) [96,36,258,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5197 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5198 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 88 145 33 226 162 418), lower := (rows 97 38 268 88 145 33 64 128 256), losses := [] }

theorem u5198 : Upper (D 8) (R 8) [96,36,264,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5199 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 268 88 145 34 225 161 417), lower := (rows 97 38 268 88 145 34 64 128 256), losses := [] }

theorem u5199 : Upper (D 8) (R 8) [96,36,264,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5199 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5200 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 88 145 160 99 163 291), lower := (rows 97 38 268 88 145 160 64 128 256), losses := [] }

theorem u5200 : Upper (D 8) (R 8) [96,36,264,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5201 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 88 146 33 225 161 417), lower := (rows 97 38 268 88 146 33 64 128 256), losses := [] }

theorem u5201 : Upper (D 8) (R 8) [96,36,264,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5202 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 88 146 160 97 161 289), lower := (rows 97 38 268 88 146 160 64 128 256), losses := [] }

theorem u5202 : Upper (D 8) (R 8) [96,36,264,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5203 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 88 176 33 195 131 387), lower := (rows 97 38 268 88 176 33 64 128 256), losses := [] }

theorem u5203 : Upper (D 8) (R 8) [96,36,264,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5204 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 268 88 176 34 193 129 385), lower := (rows 97 38 268 88 176 34 64 128 256), losses := [] }

theorem u5204 : Upper (D 8) (R 8) [96,36,264,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5204 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5205 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 88 176 160 67 131 259), lower := (rows 97 38 268 88 176 160 64 128 256), losses := [] }

theorem u5205 : Upper (D 8) (R 8) [96,36,264,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5206 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 268 137 82 33 240 176 432), lower := (rows 97 38 268 137 82 33 64 128 256), losses := [] }

theorem u5206 : Upper (D 8) (R 8) [96,36,264,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5207 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 38 268 137 82 48 225 161 417), lower := (rows 97 38 268 137 82 48 64 128 256), losses := [] }

theorem u5207 : Upper (D 8) (R 8) [96,36,264,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5207 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5208 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 137 82 160 113 177 305), lower := (rows 97 38 268 137 82 160 64 128 256), losses := [] }

theorem u5208 : Upper (D 8) (R 8) [96,36,264,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5209 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 268 137 176 33 82 210 338), lower := (rows 97 38 268 137 176 33 64 128 256), losses := [] }

theorem u5209 : Upper (D 8) (R 8) [96,36,264,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5210 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 268 137 176 34 81 209 337), lower := (rows 97 38 268 137 176 34 64 128 256), losses := [] }

theorem u5210 : Upper (D 8) (R 8) [96,36,264,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5210 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5211 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 268 137 176 48 67 195 323), lower := (rows 97 38 268 137 176 48 64 128 256), losses := [] }

theorem u5211 : Upper (D 8) (R 8) [96,36,264,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5211 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5212 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 137 176 96 83 147 275), lower := (rows 97 38 268 137 176 96 64 128 256), losses := [] }

theorem u5212 : Upper (D 8) (R 8) [96,36,264,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5213 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 268 137 208 33 114 178 306), lower := (rows 97 38 268 137 208 33 64 128 256), losses := [] }

theorem u5213 : Upper (D 8) (R 8) [96,36,264,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5214 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 38 268 137 208 34 113 177 305), lower := (rows 97 38 268 137 208 34 64 128 256), losses := [] }

theorem u5214 : Upper (D 8) (R 8) [96,36,264,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5214 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5215 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 38 268 137 208 48 99 163 291), lower := (rows 97 38 268 137 208 48 64 128 256), losses := [] }

theorem u5215 : Upper (D 8) (R 8) [96,36,264,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5215 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5216 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 82 33 225 161 417), lower := (rows 97 38 268 152 82 33 64 128 256), losses := [] }

theorem u5216 : Upper (D 8) (R 8) [96,36,264,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5217 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 82 160 97 161 289), lower := (rows 97 38 268 152 82 160 64 128 256), losses := [] }

theorem u5217 : Upper (D 8) (R 8) [96,36,264,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5218 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 168 82 33 209 145 401), lower := (rows 97 38 268 168 82 33 64 128 256), losses := [] }

theorem u5218 : Upper (D 8) (R 8) [96,36,264,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5219 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 268 168 82 48 193 129 385), lower := (rows 97 38 268 168 82 48 64 128 256), losses := [] }

theorem u5219 : Upper (D 8) (R 8) [96,36,264,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5219 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5219
end Delivery.IrregularNine14.P08
