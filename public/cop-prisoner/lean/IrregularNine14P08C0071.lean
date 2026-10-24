import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0009
import IrregularNine14P08C0010

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4260 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 44 392 145 34 112 240 368), lower := (rows 97 7 44 392 145 34 64 128 256), losses := [] }

theorem u4260 : Upper (D 8) (R 8) [96,5,40,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4260 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4261 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 44 392 145 48 98 226 354), lower := (rows 97 7 44 392 145 48 64 128 256), losses := [] }

theorem u4261 : Upper (D 8) (R 8) [96,5,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4261 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4262 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 392 145 96 114 178 306), lower := (rows 97 7 44 392 145 96 64 128 256), losses := [] }

theorem u4262 : Upper (D 8) (R 8) [96,5,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4263 : PairBound 9 := { available := 82, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 392 176 33 82 210 338), lower := (rows 97 7 44 392 176 33 64 128 256), losses := [] }

theorem u4263 : Upper (D 8) (R 8) [96,5,40,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4264 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 44 392 176 34 81 209 337), lower := (rows 97 7 44 392 176 34 64 128 256), losses := [] }

theorem u4264 : Upper (D 8) (R 8) [96,5,40,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4264 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4265 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 7 44 392 176 48 67 195 323), lower := (rows 97 7 44 392 176 48 64 128 256), losses := [] }

theorem u4265 : Upper (D 8) (R 8) [96,5,40,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4265 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4266 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 392 176 96 83 147 275), lower := (rows 97 7 44 392 176 96 64 128 256), losses := [] }

theorem u4266 : Upper (D 8) (R 8) [96,5,40,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4267 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 392 208 33 114 178 306), lower := (rows 97 7 44 392 208 33 64 128 256), losses := [] }

theorem u4267 : Upper (D 8) (R 8) [96,5,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4268 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 44 392 208 34 113 177 305), lower := (rows 97 7 44 392 208 34 64 128 256), losses := [] }

theorem u4268 : Upper (D 8) (R 8) [96,5,40,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4268 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4269 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 44 392 208 48 99 163 291), lower := (rows 97 7 44 392 208 48 64 128 256), losses := [] }

theorem u4269 : Upper (D 8) (R 8) [96,5,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4269 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4270 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 280 33 224 224 480), lower := (rows 97 7 134 56 280 33 64 128 256), losses := [] }

theorem u4270 : Upper (D 8) (R 8) [96,5,130,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4271 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 56 280 96 225 161 417), lower := (rows 97 7 134 56 280 96 64 128 256), losses := [] }

theorem u4271 : Upper (D 8) (R 8) [96,5,130,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4272 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 280 160 97 225 353), lower := (rows 97 7 134 56 280 160 64 128 256), losses := [] }

theorem u4272 : Upper (D 8) (R 8) [96,5,130,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4273 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 336 33 232 168 424), lower := (rows 97 7 134 56 336 33 64 128 256), losses := [] }

theorem u4273 : Upper (D 8) (R 8) [96,5,130,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4274 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 134 56 336 40 225 161 417), lower := (rows 97 7 134 56 336 40 64 128 256), losses := [] }

theorem u4274 : Upper (D 8) (R 8) [96,5,130,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4274 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4275 : PairBound 9 := { available := 41, camps := [{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 336 160 105 169 297), lower := (rows 97 7 134 56 336 160 64 128 256), losses := [] }

theorem u4275 : Upper (D 8) (R 8) [96,5,130,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4276 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 88 304 33 232 168 424), lower := (rows 97 7 134 88 304 33 64 128 256), losses := [] }

theorem u4276 : Upper (D 8) (R 8) [96,5,130,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4277 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 134 88 304 40 225 161 417), lower := (rows 97 7 134 88 304 40 64 128 256), losses := [] }

theorem u4277 : Upper (D 8) (R 8) [96,5,130,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4277 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4278 : PairBound 9 := { available := 41, camps := [{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 88 304 160 105 169 297), lower := (rows 97 7 134 88 304 160 64 128 256), losses := [] }

theorem u4278 : Upper (D 8) (R 8) [96,5,130,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4279 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 26 304 33 224 224 480), lower := (rows 97 7 140 26 304 33 64 128 256), losses := [] }

theorem u4279 : Upper (D 8) (R 8) [96,5,136,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4280 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 26 304 96 225 161 417), lower := (rows 97 7 140 26 304 96 64 128 256), losses := [] }

theorem u4280 : Upper (D 8) (R 8) [96,5,136,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4281 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 304 160 97 225 353), lower := (rows 97 7 140 26 304 160 64 128 256), losses := [] }

theorem u4281 : Upper (D 8) (R 8) [96,5,136,18,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4282 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 140 42 273 48 224 224 480), lower := (rows 97 7 140 42 273 48 64 128 256), losses := [] }

theorem u4282 : Upper (D 8) (R 8) [96,5,136,34,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4282 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4283 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 42 273 96 240 176 432), lower := (rows 97 7 140 42 273 96 64 128 256), losses := [] }

theorem u4283 : Upper (D 8) (R 8) [96,5,136,34,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4284 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 42 273 160 112 240 368), lower := (rows 97 7 140 42 273 160 64 128 256), losses := [] }

theorem u4284 : Upper (D 8) (R 8) [96,5,136,34,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4285 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 42 304 33 208 208 464), lower := (rows 97 7 140 42 304 33 64 128 256), losses := [] }

theorem u4285 : Upper (D 8) (R 8) [96,5,136,34,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4286 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 140 42 304 48 193 193 449), lower := (rows 97 7 140 42 304 48 64 128 256), losses := [] }

theorem u4286 : Upper (D 8) (R 8) [96,5,136,34,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4286 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4287 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 42 304 96 209 145 401), lower := (rows 97 7 140 42 304 96 64 128 256), losses := [] }

theorem u4287 : Upper (D 8) (R 8) [96,5,136,34,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4288 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 42 304 160 81 209 337), lower := (rows 97 7 140 42 304 160 64 128 256), losses := [] }

theorem u4288 : Upper (D 8) (R 8) [96,5,136,34,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4289 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 140 42 336 33 240 176 432), lower := (rows 97 7 140 42 336 33 64 128 256), losses := [] }

theorem u4289 : Upper (D 8) (R 8) [96,5,136,34,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4290 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 140 42 336 48 225 161 417), lower := (rows 97 7 140 42 336 48 64 128 256), losses := [] }

theorem u4290 : Upper (D 8) (R 8) [96,5,136,34,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4290 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4291 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 42 336 160 113 177 305), lower := (rows 97 7 140 42 336 160 64 128 256), losses := [] }

theorem u4291 : Upper (D 8) (R 8) [96,5,136,34,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4292 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 140 56 273 34 224 224 480), lower := (rows 97 7 140 56 273 34 64 128 256), losses := [] }

theorem u4292 : Upper (D 8) (R 8) [96,5,136,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4292 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4293 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 56 273 96 226 162 418), lower := (rows 97 7 140 56 273 96 64 128 256), losses := [] }

theorem u4293 : Upper (D 8) (R 8) [96,5,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4294 : Route 9 := (fun mask => (mask,id))

def c4294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4294 : Upper (D 8) (R 8) [96,5,136,48,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,257,128] 13 (by decide) (choices 1) [2,32] r4294 c4294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u596
  · exact u597

def b4295 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 140 56 274 33 224 224 480), lower := (rows 97 7 140 56 274 33 64 128 256), losses := [] }

theorem u4295 : Upper (D 8) (R 8) [96,5,136,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4296 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 56 274 96 225 161 417), lower := (rows 97 7 140 56 274 96 64 128 256), losses := [] }

theorem u4296 : Upper (D 8) (R 8) [96,5,136,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4297 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 274 160 97 225 353), lower := (rows 97 7 140 56 274 160 64 128 256), losses := [] }

theorem u4297 : Upper (D 8) (R 8) [96,5,136,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4298 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 336 33 226 162 418), lower := (rows 97 7 140 56 336 33 64 128 256), losses := [] }

theorem u4298 : Upper (D 8) (R 8) [96,5,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4299 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 140 56 336 34 225 161 417), lower := (rows 97 7 140 56 336 34 64 128 256), losses := [] }

theorem u4299 : Upper (D 8) (R 8) [96,5,136,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4299 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4300 : Route 9 := (fun mask => (mask,id))

def c4300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4300 : Upper (D 8) (R 8) [96,5,136,48,320,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,320,128] 13 (by decide) (choices 1) [1,2,32] r4300 c4300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u598
  · exact u599
  · exact u600

def b4301 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 280 50 33 224 224 480), lower := (rows 97 7 140 280 50 33 64 128 256), losses := [] }

theorem u4301 : Upper (D 8) (R 8) [96,5,136,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4302 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 280 50 96 225 161 417), lower := (rows 97 7 140 280 50 96 64 128 256), losses := [] }

theorem u4302 : Upper (D 8) (R 8) [96,5,136,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4303 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 50 160 97 225 353), lower := (rows 97 7 140 280 50 160 64 128 256), losses := [] }

theorem u4303 : Upper (D 8) (R 8) [96,5,136,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4304 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 296 50 33 208 208 464), lower := (rows 97 7 140 296 50 33 64 128 256), losses := [] }

theorem u4304 : Upper (D 8) (R 8) [96,5,136,288,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4305 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 140 296 50 48 193 193 449), lower := (rows 97 7 140 296 50 48 64 128 256), losses := [] }

theorem u4305 : Upper (D 8) (R 8) [96,5,136,288,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4305 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4306 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 296 50 96 209 145 401), lower := (rows 97 7 140 296 50 96 64 128 256), losses := [] }

theorem u4306 : Upper (D 8) (R 8) [96,5,136,288,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4307 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 296 50 160 81 209 337), lower := (rows 97 7 140 296 50 160 64 128 256), losses := [] }

theorem u4307 : Upper (D 8) (R 8) [96,5,136,288,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4308 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 296 82 33 240 176 432), lower := (rows 97 7 140 296 82 33 64 128 256), losses := [] }

theorem u4308 : Upper (D 8) (R 8) [96,5,136,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4309 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 140 296 82 48 225 161 417), lower := (rows 97 7 140 296 82 48 64 128 256), losses := [] }

theorem u4309 : Upper (D 8) (R 8) [96,5,136,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4309 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4310 : Route 9 := (fun mask => (mask,id))

def c4310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4310 : Upper (D 8) (R 8) [96,5,136,288,66,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,66,128] 13 (by decide) (choices 1) [1,16,32] r4310 c4310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u601
  · exact u602
  · exact u603

def b4311 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 140 296 145 34 112 240 368), lower := (rows 97 7 140 296 145 34 64 128 256), losses := [] }

theorem u4311 : Upper (D 8) (R 8) [96,5,136,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4311 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4312 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 140 296 145 48 98 226 354), lower := (rows 97 7 140 296 145 48 64 128 256), losses := [] }

theorem u4312 : Upper (D 8) (R 8) [96,5,136,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4312 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4313 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 296 145 96 114 178 306), lower := (rows 97 7 140 296 145 96 64 128 256), losses := [] }

theorem u4313 : Upper (D 8) (R 8) [96,5,136,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4314 : PairBound 9 := { available := 82, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 296 176 33 82 210 338), lower := (rows 97 7 140 296 176 33 64 128 256), losses := [] }

theorem u4314 : Upper (D 8) (R 8) [96,5,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4315 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 140 296 176 34 81 209 337), lower := (rows 97 7 140 296 176 34 64 128 256), losses := [] }

theorem u4315 : Upper (D 8) (R 8) [96,5,136,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4315 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4316 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 7 140 296 176 48 67 195 323), lower := (rows 97 7 140 296 176 48 64 128 256), losses := [] }

theorem u4316 : Upper (D 8) (R 8) [96,5,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4316 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4317 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 296 176 96 83 147 275), lower := (rows 97 7 140 296 176 96 64 128 256), losses := [] }

theorem u4317 : Upper (D 8) (R 8) [96,5,136,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4318 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 296 208 33 114 178 306), lower := (rows 97 7 140 296 208 33 64 128 256), losses := [] }

theorem u4318 : Upper (D 8) (R 8) [96,5,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4319 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 140 296 208 34 113 177 305), lower := (rows 97 7 140 296 208 34 64 128 256), losses := [] }

theorem u4319 : Upper (D 8) (R 8) [96,5,136,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4319 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4319
end Delivery.IrregularNine14.P08
