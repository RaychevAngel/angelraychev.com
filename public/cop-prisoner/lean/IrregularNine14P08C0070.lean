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

def b4200 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 44 26 176 288 193 193 449), lower := (rows 97 7 44 26 176 288 64 128 256), losses := [] }

theorem u4200 : Upper (D 8) (R 8) [96,5,40,18,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4200 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4201 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 26 304 33 192 192 448), lower := (rows 97 7 44 26 304 33 64 128 256), losses := [] }

theorem u4201 : Upper (D 8) (R 8) [96,5,40,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4202 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 26 304 96 193 129 385), lower := (rows 97 7 44 26 304 96 64 128 256), losses := [] }

theorem u4202 : Upper (D 8) (R 8) [96,5,40,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4203 : Route 9 := (fun mask => (mask,id))

def c4203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4203 : Upper (D 8) (R 8) [96,5,40,18,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,288,128] 13 (by decide) (choices 1) [1,128] r4203 c4203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u589
  · exact u590

def b4204 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 26 400 33 224 224 480), lower := (rows 97 7 44 26 400 33 64 128 256), losses := [] }

theorem u4204 : Upper (D 8) (R 8) [96,5,40,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4205 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 26 400 96 225 161 417), lower := (rows 97 7 44 26 400 96 64 128 256), losses := [] }

theorem u4205 : Upper (D 8) (R 8) [96,5,40,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4206 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 26 400 160 97 225 353), lower := (rows 97 7 44 26 400 160 64 128 256), losses := [] }

theorem u4206 : Upper (D 8) (R 8) [96,5,40,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4207 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 44 138 273 48 224 224 480), lower := (rows 97 7 44 138 273 48 64 128 256), losses := [] }

theorem u4207 : Upper (D 8) (R 8) [96,5,40,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4207 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4208 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 138 273 96 240 176 432), lower := (rows 97 7 44 138 273 96 64 128 256), losses := [] }

theorem u4208 : Upper (D 8) (R 8) [96,5,40,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4209 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 138 273 160 112 240 368), lower := (rows 97 7 44 138 273 160 64 128 256), losses := [] }

theorem u4209 : Upper (D 8) (R 8) [96,5,40,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4210 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 138 304 33 208 208 464), lower := (rows 97 7 44 138 304 33 64 128 256), losses := [] }

theorem u4210 : Upper (D 8) (R 8) [96,5,40,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4211 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 44 138 304 48 193 193 449), lower := (rows 97 7 44 138 304 48 64 128 256), losses := [] }

theorem u4211 : Upper (D 8) (R 8) [96,5,40,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4211 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4212 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 138 304 96 209 145 401), lower := (rows 97 7 44 138 304 96 64 128 256), losses := [] }

theorem u4212 : Upper (D 8) (R 8) [96,5,40,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4213 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 138 304 160 81 209 337), lower := (rows 97 7 44 138 304 160 64 128 256), losses := [] }

theorem u4213 : Upper (D 8) (R 8) [96,5,40,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4214 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 138 336 33 240 176 432), lower := (rows 97 7 44 138 336 33 64 128 256), losses := [] }

theorem u4214 : Upper (D 8) (R 8) [96,5,40,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4215 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 44 138 336 48 225 161 417), lower := (rows 97 7 44 138 336 48 64 128 256), losses := [] }

theorem u4215 : Upper (D 8) (R 8) [96,5,40,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4215 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4216 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 138 336 160 113 177 305), lower := (rows 97 7 44 138 336 160 64 128 256), losses := [] }

theorem u4216 : Upper (D 8) (R 8) [96,5,40,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4217 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 44 152 273 34 224 224 480), lower := (rows 97 7 44 152 273 34 64 128 256), losses := [] }

theorem u4217 : Upper (D 8) (R 8) [96,5,40,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4217 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4218 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 152 273 96 226 162 418), lower := (rows 97 7 44 152 273 96 64 128 256), losses := [] }

theorem u4218 : Upper (D 8) (R 8) [96,5,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4219 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 273 160 98 226 354), lower := (rows 97 7 44 152 273 160 64 128 256), losses := [] }

theorem u4219 : Upper (D 8) (R 8) [96,5,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4220 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 274 33 224 224 480), lower := (rows 97 7 44 152 274 33 64 128 256), losses := [] }

theorem u4220 : Upper (D 8) (R 8) [96,5,40,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4221 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 152 274 96 225 161 417), lower := (rows 97 7 44 152 274 96 64 128 256), losses := [] }

theorem u4221 : Upper (D 8) (R 8) [96,5,40,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4222 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 274 160 97 225 353), lower := (rows 97 7 44 152 274 160 64 128 256), losses := [] }

theorem u4222 : Upper (D 8) (R 8) [96,5,40,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4223 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 304 33 194 194 450), lower := (rows 97 7 44 152 304 33 64 128 256), losses := [] }

theorem u4223 : Upper (D 8) (R 8) [96,5,40,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4224 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 44 152 304 34 193 193 449), lower := (rows 97 7 44 152 304 34 64 128 256), losses := [] }

theorem u4224 : Upper (D 8) (R 8) [96,5,40,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4224 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4225 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 152 304 96 195 131 387), lower := (rows 97 7 44 152 304 96 64 128 256), losses := [] }

theorem u4225 : Upper (D 8) (R 8) [96,5,40,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4226 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 304 160 67 195 323), lower := (rows 97 7 44 152 304 160 64 128 256), losses := [] }

theorem u4226 : Upper (D 8) (R 8) [96,5,40,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4227 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 336 33 226 162 418), lower := (rows 97 7 44 152 336 33 64 128 256), losses := [] }

theorem u4227 : Upper (D 8) (R 8) [96,5,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4228 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 44 152 336 34 225 161 417), lower := (rows 97 7 44 152 336 34 64 128 256), losses := [] }

theorem u4228 : Upper (D 8) (R 8) [96,5,40,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4228 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4229 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 336 160 99 163 291), lower := (rows 97 7 44 152 336 160 64 128 256), losses := [] }

theorem u4229 : Upper (D 8) (R 8) [96,5,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4230 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 44 266 145 48 224 224 480), lower := (rows 97 7 44 266 145 48 64 128 256), losses := [] }

theorem u4230 : Upper (D 8) (R 8) [96,5,40,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4230 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4231 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 266 145 96 240 176 432), lower := (rows 97 7 44 266 145 96 64 128 256), losses := [] }

theorem u4231 : Upper (D 8) (R 8) [96,5,40,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4232 : Route 9 := (fun mask => (mask,id))

def c4232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4232 : Upper (D 8) (R 8) [96,5,40,258,129,128] 13 := by
  apply FastRouting.sound _ _ [96,5,40,258,129,128] 13 (by decide) (choices 1) [16,32] r4232 c4232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u591
  · exact u592

def b4233 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 266 176 33 208 208 464), lower := (rows 97 7 44 266 176 33 64 128 256), losses := [] }

theorem u4233 : Upper (D 8) (R 8) [96,5,40,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4234 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 44 266 176 48 193 193 449), lower := (rows 97 7 44 266 176 48 64 128 256), losses := [] }

theorem u4234 : Upper (D 8) (R 8) [96,5,40,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4234 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4235 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 266 176 96 209 145 401), lower := (rows 97 7 44 266 176 96 64 128 256), losses := [] }

theorem u4235 : Upper (D 8) (R 8) [96,5,40,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4236 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 266 176 160 81 209 337), lower := (rows 97 7 44 266 176 160 64 128 256), losses := [] }

theorem u4236 : Upper (D 8) (R 8) [96,5,40,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4237 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 266 208 33 240 176 432), lower := (rows 97 7 44 266 208 33 64 128 256), losses := [] }

theorem u4237 : Upper (D 8) (R 8) [96,5,40,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4238 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 44 266 208 48 225 161 417), lower := (rows 97 7 44 266 208 48 64 128 256), losses := [] }

theorem u4238 : Upper (D 8) (R 8) [96,5,40,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4238 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4239 : Route 9 := (fun mask => (mask,id))

def c4239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4239 : Upper (D 8) (R 8) [96,5,40,258,192,128] 13 := by
  apply FastRouting.sound _ _ [96,5,40,258,192,128] 13 (by decide) (choices 1) [1,16,32] r4239 c4239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u593
  · exact u594
  · exact u595

def b4240 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 44 280 145 34 224 224 480), lower := (rows 97 7 44 280 145 34 64 128 256), losses := [] }

theorem u4240 : Upper (D 8) (R 8) [96,5,40,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4240 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4241 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 280 145 96 226 162 418), lower := (rows 97 7 44 280 145 96 64 128 256), losses := [] }

theorem u4241 : Upper (D 8) (R 8) [96,5,40,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4242 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 280 145 160 98 226 354), lower := (rows 97 7 44 280 145 160 64 128 256), losses := [] }

theorem u4242 : Upper (D 8) (R 8) [96,5,40,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4243 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 280 146 33 224 224 480), lower := (rows 97 7 44 280 146 33 64 128 256), losses := [] }

theorem u4243 : Upper (D 8) (R 8) [96,5,40,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4244 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 280 146 96 225 161 417), lower := (rows 97 7 44 280 146 96 64 128 256), losses := [] }

theorem u4244 : Upper (D 8) (R 8) [96,5,40,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4245 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 280 146 160 97 225 353), lower := (rows 97 7 44 280 146 160 64 128 256), losses := [] }

theorem u4245 : Upper (D 8) (R 8) [96,5,40,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4246 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 280 176 33 194 194 450), lower := (rows 97 7 44 280 176 33 64 128 256), losses := [] }

theorem u4246 : Upper (D 8) (R 8) [96,5,40,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4247 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 44 280 176 34 193 193 449), lower := (rows 97 7 44 280 176 34 64 128 256), losses := [] }

theorem u4247 : Upper (D 8) (R 8) [96,5,40,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4247 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4248 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 280 176 96 195 131 387), lower := (rows 97 7 44 280 176 96 64 128 256), losses := [] }

theorem u4248 : Upper (D 8) (R 8) [96,5,40,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4249 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 280 176 160 67 195 323), lower := (rows 97 7 44 280 176 160 64 128 256), losses := [] }

theorem u4249 : Upper (D 8) (R 8) [96,5,40,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4250 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 280 208 33 226 162 418), lower := (rows 97 7 44 280 208 33 64 128 256), losses := [] }

theorem u4250 : Upper (D 8) (R 8) [96,5,40,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4251 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 44 280 208 34 225 161 417), lower := (rows 97 7 44 280 208 34 64 128 256), losses := [] }

theorem u4251 : Upper (D 8) (R 8) [96,5,40,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4251 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4252 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 280 208 160 99 163 291), lower := (rows 97 7 44 280 208 160 64 128 256), losses := [] }

theorem u4252 : Upper (D 8) (R 8) [96,5,40,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4253 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 392 50 33 208 208 464), lower := (rows 97 7 44 392 50 33 64 128 256), losses := [] }

theorem u4253 : Upper (D 8) (R 8) [96,5,40,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4254 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 44 392 50 48 193 193 449), lower := (rows 97 7 44 392 50 48 64 128 256), losses := [] }

theorem u4254 : Upper (D 8) (R 8) [96,5,40,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4254 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4255 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 392 50 96 209 145 401), lower := (rows 97 7 44 392 50 96 64 128 256), losses := [] }

theorem u4255 : Upper (D 8) (R 8) [96,5,40,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4256 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 392 50 160 81 209 337), lower := (rows 97 7 44 392 50 160 64 128 256), losses := [] }

theorem u4256 : Upper (D 8) (R 8) [96,5,40,384,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4257 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 392 82 33 240 176 432), lower := (rows 97 7 44 392 82 33 64 128 256), losses := [] }

theorem u4257 : Upper (D 8) (R 8) [96,5,40,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4258 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 44 392 82 48 225 161 417), lower := (rows 97 7 44 392 82 48 64 128 256), losses := [] }

theorem u4258 : Upper (D 8) (R 8) [96,5,40,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4258 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4259 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 392 82 160 113 177 305), lower := (rows 97 7 44 392 82 160 64 128 256), losses := [] }

theorem u4259 : Upper (D 8) (R 8) [96,5,40,384,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4259
end Delivery.IrregularNine14.P08
