import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0009

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4140 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 386 37 104 176 48 77 141 269), lower := (rows 67 386 37 104 176 48 64 128 256), losses := [] }

theorem u4140 : Upper (D 8) (R 8) [66,384,33,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4140 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4141 : Route 9 := (fun mask => (mask,id))

def c4141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4141 : Upper (D 8) (R 8) [66,384,40,80,160,1] 13 := by
  apply FastRouting.sound _ _ [66,384,40,80,160,1] 13 (by decide) (choices 1) [1,4,32] r4141 c4141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u578
  · exact u579
  · exact u580

def b4142 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 44 88 176 36 97 161 289), lower := (rows 67 386 44 88 176 36 64 128 256), losses := [] }

theorem u4142 : Upper (D 8) (R 8) [66,384,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4142 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4143 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 386 44 152 112 33 101 165 293), lower := (rows 67 386 44 152 112 33 64 128 256), losses := [] }

theorem u4143 : Upper (D 8) (R 8) [66,384,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4144 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 44 152 112 36 97 161 289), lower := (rows 67 386 44 152 112 36 64 128 256), losses := [] }

theorem u4144 : Upper (D 8) (R 8) [66,384,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4144 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4145 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 56 208 33 480 416 416), lower := (rows 97 7 14 56 208 33 64 128 256), losses := [] }

theorem u4145 : Upper (D 8) (R 8) [96,5,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4146 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 56 208 160 353 417 289), lower := (rows 97 7 14 56 208 160 64 128 256), losses := [] }

theorem u4146 : Upper (D 8) (R 8) [96,5,10,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4147 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 14 56 208 288 225 161 417), lower := (rows 97 7 14 56 208 288 64 128 256), losses := [] }

theorem u4147 : Upper (D 8) (R 8) [96,5,10,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4147 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4148 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 56 336 33 224 160 416), lower := (rows 97 7 14 56 336 33 64 128 256), losses := [] }

theorem u4148 : Upper (D 8) (R 8) [96,5,10,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4149 : Route 9 := (fun mask => (mask,id))

def c4149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4149 : Upper (D 8) (R 8) [96,5,10,48,320,128] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,320,128] 13 (by decide) (choices 1) [1,32,128] r4149 c4149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u581
  · exact u582
  · exact u583

def b4150 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 56 400 33 224 224 480), lower := (rows 97 7 14 56 400 33 64 128 256), losses := [] }

theorem u4150 : Upper (D 8) (R 8) [96,5,10,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4151 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 56 400 96 225 161 417), lower := (rows 97 7 14 56 400 96 64 128 256), losses := [] }

theorem u4151 : Upper (D 8) (R 8) [96,5,10,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4152 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 56 400 160 97 225 353), lower := (rows 97 7 14 56 400 160 64 128 256), losses := [] }

theorem u4152 : Upper (D 8) (R 8) [96,5,10,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4153 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 152 304 33 224 224 480), lower := (rows 97 7 14 152 304 33 64 128 256), losses := [] }

theorem u4153 : Upper (D 8) (R 8) [96,5,10,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4154 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 152 304 96 225 161 417), lower := (rows 97 7 14 152 304 96 64 128 256), losses := [] }

theorem u4154 : Upper (D 8) (R 8) [96,5,10,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4155 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 304 160 97 225 353), lower := (rows 97 7 14 152 304 160 64 128 256), losses := [] }

theorem u4155 : Upper (D 8) (R 8) [96,5,10,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4156 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 152 336 33 224 160 416), lower := (rows 97 7 14 152 336 33 64 128 256), losses := [] }

theorem u4156 : Upper (D 8) (R 8) [96,5,10,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4157 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 336 160 97 161 289), lower := (rows 97 7 14 152 336 160 64 128 256), losses := [] }

theorem u4157 : Upper (D 8) (R 8) [96,5,10,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4158 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 168 304 33 208 208 464), lower := (rows 97 7 14 168 304 33 64 128 256), losses := [] }

theorem u4158 : Upper (D 8) (R 8) [96,5,10,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4159 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 14 168 304 48 193 193 449), lower := (rows 97 7 14 168 304 48 64 128 256), losses := [] }

theorem u4159 : Upper (D 8) (R 8) [96,5,10,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4159 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4160 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 168 304 96 209 145 401), lower := (rows 97 7 14 168 304 96 64 128 256), losses := [] }

theorem u4160 : Upper (D 8) (R 8) [96,5,10,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4161 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 168 304 160 81 209 337), lower := (rows 97 7 14 168 304 160 64 128 256), losses := [] }

theorem u4161 : Upper (D 8) (R 8) [96,5,10,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4162 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 168 336 33 240 176 432), lower := (rows 97 7 14 168 336 33 64 128 256), losses := [] }

theorem u4162 : Upper (D 8) (R 8) [96,5,10,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4163 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 14 168 336 48 225 161 417), lower := (rows 97 7 14 168 336 48 64 128 256), losses := [] }

theorem u4163 : Upper (D 8) (R 8) [96,5,10,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4163 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4164 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 168 336 160 113 177 305), lower := (rows 97 7 14 168 336 160 64 128 256), losses := [] }

theorem u4164 : Upper (D 8) (R 8) [96,5,10,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4165 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 280 176 33 224 224 480), lower := (rows 97 7 14 280 176 33 64 128 256), losses := [] }

theorem u4165 : Upper (D 8) (R 8) [96,5,10,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4166 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 280 176 96 225 161 417), lower := (rows 97 7 14 280 176 96 64 128 256), losses := [] }

theorem u4166 : Upper (D 8) (R 8) [96,5,10,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4167 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 280 176 160 97 225 353), lower := (rows 97 7 14 280 176 160 64 128 256), losses := [] }

theorem u4167 : Upper (D 8) (R 8) [96,5,10,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4168 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 280 208 33 224 160 416), lower := (rows 97 7 14 280 208 33 64 128 256), losses := [] }

theorem u4168 : Upper (D 8) (R 8) [96,5,10,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4169 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 280 208 160 97 161 289), lower := (rows 97 7 14 280 208 160 64 128 256), losses := [] }

theorem u4169 : Upper (D 8) (R 8) [96,5,10,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4170 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 296 176 33 208 208 464), lower := (rows 97 7 14 296 176 33 64 128 256), losses := [] }

theorem u4170 : Upper (D 8) (R 8) [96,5,10,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4171 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 14 296 176 48 193 193 449), lower := (rows 97 7 14 296 176 48 64 128 256), losses := [] }

theorem u4171 : Upper (D 8) (R 8) [96,5,10,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4171 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4172 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 296 176 96 209 145 401), lower := (rows 97 7 14 296 176 96 64 128 256), losses := [] }

theorem u4172 : Upper (D 8) (R 8) [96,5,10,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4173 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 296 176 160 81 209 337), lower := (rows 97 7 14 296 176 160 64 128 256), losses := [] }

theorem u4173 : Upper (D 8) (R 8) [96,5,10,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4174 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 296 208 33 240 176 432), lower := (rows 97 7 14 296 208 33 64 128 256), losses := [] }

theorem u4174 : Upper (D 8) (R 8) [96,5,10,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4175 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 14 296 208 48 225 161 417), lower := (rows 97 7 14 296 208 48 64 128 256), losses := [] }

theorem u4175 : Upper (D 8) (R 8) [96,5,10,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4175 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4176 : Route 9 := (fun mask => (mask,id))

def c4176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4176 : Upper (D 8) (R 8) [96,5,10,288,192,128] 13 := by
  apply FastRouting.sound _ _ [96,5,10,288,192,128] 13 (by decide) (choices 1) [1,16,32] r4176 c4176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u584
  · exact u585
  · exact u586

def b4177 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 42 176 33 448 448 448), lower := (rows 97 7 28 42 176 33 64 128 256), losses := [] }

theorem u4177 : Upper (D 8) (R 8) [96,5,24,34,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4178 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 42 176 96 449 385 385), lower := (rows 97 7 28 42 176 96 64 128 256), losses := [] }

theorem u4178 : Upper (D 8) (R 8) [96,5,24,34,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4179 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 42 176 160 321 449 321), lower := (rows 97 7 28 42 176 160 64 128 256), losses := [] }

theorem u4179 : Upper (D 8) (R 8) [96,5,24,34,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4180 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 28 42 176 288 193 193 449), lower := (rows 97 7 28 42 176 288 64 128 256), losses := [] }

theorem u4180 : Upper (D 8) (R 8) [96,5,24,34,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4180 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4181 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 42 304 33 192 192 448), lower := (rows 97 7 28 42 304 33 64 128 256), losses := [] }

theorem u4181 : Upper (D 8) (R 8) [96,5,24,34,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4182 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 42 304 96 193 129 385), lower := (rows 97 7 28 42 304 96 64 128 256), losses := [] }

theorem u4182 : Upper (D 8) (R 8) [96,5,24,34,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4183 : Route 9 := (fun mask => (mask,id))

def c4183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4183 : Upper (D 8) (R 8) [96,5,24,34,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,288,128] 13 (by decide) (choices 1) [1,128] r4183 c4183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u587
  · exact u588

def b4184 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 42 400 33 224 224 480), lower := (rows 97 7 28 42 400 33 64 128 256), losses := [] }

theorem u4184 : Upper (D 8) (R 8) [96,5,24,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4185 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 42 400 96 225 161 417), lower := (rows 97 7 28 42 400 96 64 128 256), losses := [] }

theorem u4185 : Upper (D 8) (R 8) [96,5,24,34,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4186 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 42 400 160 97 225 353), lower := (rows 97 7 28 42 400 160 64 128 256), losses := [] }

theorem u4186 : Upper (D 8) (R 8) [96,5,24,34,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4187 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 28 138 304 33 224 224 480), lower := (rows 97 7 28 138 304 33 64 128 256), losses := [] }

theorem u4187 : Upper (D 8) (R 8) [96,5,24,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4188 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 138 304 96 225 161 417), lower := (rows 97 7 28 138 304 96 64 128 256), losses := [] }

theorem u4188 : Upper (D 8) (R 8) [96,5,24,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4189 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 304 160 97 225 353), lower := (rows 97 7 28 138 304 160 64 128 256), losses := [] }

theorem u4189 : Upper (D 8) (R 8) [96,5,24,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4190 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 168 274 33 224 224 480), lower := (rows 97 7 28 168 274 33 64 128 256), losses := [] }

theorem u4190 : Upper (D 8) (R 8) [96,5,24,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4191 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 168 274 96 225 161 417), lower := (rows 97 7 28 168 274 96 64 128 256), losses := [] }

theorem u4191 : Upper (D 8) (R 8) [96,5,24,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4192 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 168 274 160 97 225 353), lower := (rows 97 7 28 168 274 160 64 128 256), losses := [] }

theorem u4192 : Upper (D 8) (R 8) [96,5,24,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4193 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 168 304 33 194 194 450), lower := (rows 97 7 28 168 304 33 64 128 256), losses := [] }

theorem u4193 : Upper (D 8) (R 8) [96,5,24,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4194 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 28 168 304 34 193 193 449), lower := (rows 97 7 28 168 304 34 64 128 256), losses := [] }

theorem u4194 : Upper (D 8) (R 8) [96,5,24,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4194 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4195 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 168 304 96 195 131 387), lower := (rows 97 7 28 168 304 96 64 128 256), losses := [] }

theorem u4195 : Upper (D 8) (R 8) [96,5,24,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4196 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 168 304 160 67 195 323), lower := (rows 97 7 28 168 304 160 64 128 256), losses := [] }

theorem u4196 : Upper (D 8) (R 8) [96,5,24,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4197 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 26 176 33 448 448 448), lower := (rows 97 7 44 26 176 33 64 128 256), losses := [] }

theorem u4197 : Upper (D 8) (R 8) [96,5,40,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4198 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 26 176 96 449 385 385), lower := (rows 97 7 44 26 176 96 64 128 256), losses := [] }

theorem u4198 : Upper (D 8) (R 8) [96,5,40,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4199 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 26 176 160 321 449 321), lower := (rows 97 7 44 26 176 160 64 128 256), losses := [] }

theorem u4199 : Upper (D 8) (R 8) [96,5,40,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4199
end Delivery.IrregularNine14.P08
