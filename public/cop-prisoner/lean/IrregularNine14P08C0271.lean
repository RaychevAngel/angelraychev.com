import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0097

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16260 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 104 208 165 229 165 421), lower := (rows 259 35 28 104 208 32 64 128 256), losses := [] }

theorem u16260 : Upper (D 8) (R 8) [258,33,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16261 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 200 208 37 101 165 293), lower := (rows 259 35 28 200 208 32 64 128 256), losses := [] }

theorem u16261 : Upper (D 8) (R 8) [258,33,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16262 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 44 88 240 208 208 464), lower := (rows 259 35 37 44 88 32 64 128 256), losses := [] }

theorem u16262 : Upper (D 8) (R 8) [258,33,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16263 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 44 208 248 216 216 472), lower := (rows 259 35 37 44 208 32 64 128 256), losses := [] }

theorem u16263 : Upper (D 8) (R 8) [258,33,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16264 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 56 84 232 200 200 456), lower := (rows 259 35 37 56 84 32 64 128 256), losses := [] }

theorem u16264 : Upper (D 8) (R 8) [258,33,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16265 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 56 88 228 196 196 452), lower := (rows 259 35 37 56 88 32 64 128 256), losses := [] }

theorem u16265 : Upper (D 8) (R 8) [258,33,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16266 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 56 208 236 204 204 460), lower := (rows 259 35 37 56 208 32 64 128 256), losses := [] }

theorem u16266 : Upper (D 8) (R 8) [258,33,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16267 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 112 184 216 152 408), lower := (rows 259 35 37 76 112 32 64 128 256), losses := [] }

theorem u16267 : Upper (D 8) (R 8) [258,33,33,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16268 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 152 240 240 240 496), lower := (rows 259 35 37 76 152 32 64 128 256), losses := [] }

theorem u16268 : Upper (D 8) (R 8) [258,33,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16269 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 176 248 216 216 472), lower := (rows 259 35 37 76 176 32 64 128 256), losses := [] }

theorem u16269 : Upper (D 8) (R 8) [258,33,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16270 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 208 184 248 184 440), lower := (rows 259 35 37 76 208 32 64 128 256), losses := [] }

theorem u16270 : Upper (D 8) (R 8) [258,33,33,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16271 : PairBound 9 := { available := 228, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 88 152 228 228 228 484), lower := (rows 259 35 37 88 152 32 64 128 256), losses := [] }

theorem u16271 : Upper (D 8) (R 8) [258,33,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16272 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 88 176 236 204 204 460), lower := (rows 259 35 37 88 176 32 64 128 256), losses := [] }

theorem u16272 : Upper (D 8) (R 8) [258,33,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16273 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 104 208 188 220 156 412), lower := (rows 259 35 37 104 208 32 64 128 256), losses := [] }

theorem u16273 : Upper (D 8) (R 8) [258,33,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16274 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 44 208 241 209 209 465), lower := (rows 259 35 44 44 208 32 64 128 256), losses := [] }

theorem u16274 : Upper (D 8) (R 8) [258,33,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16275 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 56 84 225 193 193 449), lower := (rows 259 35 44 56 84 32 64 128 256), losses := [] }

theorem u16275 : Upper (D 8) (R 8) [258,33,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16276 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 56 208 229 197 197 453), lower := (rows 259 35 44 56 208 32 64 128 256), losses := [] }

theorem u16276 : Upper (D 8) (R 8) [258,33,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16277 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 73 84 176 240 176 432), lower := (rows 259 35 44 73 84 32 64 128 256), losses := [] }

theorem u16277 : Upper (D 8) (R 8) [258,33,40,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16278 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 73 112 180 212 148 404), lower := (rows 259 35 44 73 112 32 64 128 256), losses := [] }

theorem u16278 : Upper (D 8) (R 8) [258,33,40,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16279 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 73 148 240 240 240 496), lower := (rows 259 35 44 73 148 32 64 128 256), losses := [] }

theorem u16279 : Upper (D 8) (R 8) [258,33,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16280 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 73 176 244 212 212 468), lower := (rows 259 35 44 73 176 32 64 128 256), losses := [] }

theorem u16280 : Upper (D 8) (R 8) [258,33,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16281 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 73 208 180 244 180 436), lower := (rows 259 35 44 73 208 32 64 128 256), losses := [] }

theorem u16281 : Upper (D 8) (R 8) [258,33,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16282 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 76 81 176 240 176 432), lower := (rows 259 35 44 76 81 32 64 128 256), losses := [] }

theorem u16282 : Upper (D 8) (R 8) [258,33,40,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16283 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 76 112 177 209 145 401), lower := (rows 259 35 44 76 112 32 64 128 256), losses := [] }

theorem u16283 : Upper (D 8) (R 8) [258,33,40,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16284 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 76 145 240 240 240 496), lower := (rows 259 35 44 76 145 32 64 128 256), losses := [] }

theorem u16284 : Upper (D 8) (R 8) [258,33,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16285 : Route 9 := (fun mask => (mask,id))

def c16285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16285 : Upper (D 8) (R 8) [258,33,40,68,160] 13 := by
  apply FastRouting.sound _ _ [258,33,40,68,160] 13 (by decide) (choices 1) [1,16,64,128] r16285 c16285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5846
  · exact u5847
  · exact u5848
  · exact u5849

def b16286 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 76 208 177 241 177 433), lower := (rows 259 35 44 76 208 32 64 128 256), losses := [] }

theorem u16286 : Upper (D 8) (R 8) [258,33,40,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16287 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 81 164 228 164 420), lower := (rows 259 35 44 88 81 32 64 128 256), losses := [] }

theorem u16287 : Upper (D 8) (R 8) [258,33,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16288 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 84 161 225 161 417), lower := (rows 259 35 44 88 84 32 64 128 256), losses := [] }

theorem u16288 : Upper (D 8) (R 8) [258,33,40,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16289 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 88 112 165 197 133 389), lower := (rows 259 35 44 88 112 32 64 128 256), losses := [] }

theorem u16289 : Upper (D 8) (R 8) [258,33,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16290 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 88 145 228 228 228 484), lower := (rows 259 35 44 88 145 32 64 128 256), losses := [] }

theorem u16290 : Upper (D 8) (R 8) [258,33,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16291 : Route 9 := (fun mask => (mask,id))

def c16291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16291 : Upper (D 8) (R 8) [258,33,40,80,132] 13 := by
  apply FastRouting.sound _ _ [258,33,40,80,132] 13 (by decide) (choices 1) [1,64,128] r16291 c16291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5850
  · exact u5851
  · exact u5852

def r16292 : Route 9 := (fun mask => (mask,id))

def c16292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16292 : Upper (D 8) (R 8) [258,33,40,80,160] 13 := by
  apply FastRouting.sound _ _ [258,33,40,80,160] 13 (by decide) (choices 1) [1,4,64,128] r16292 c16292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5853
  · exact u5854
  · exact u5855
  · exact u5856

def b16293 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 208 165 229 165 421), lower := (rows 259 35 44 88 208 32 64 128 256), losses := [] }

theorem u16293 : Upper (D 8) (R 8) [258,33,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16294 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 104 84 177 209 145 401), lower := (rows 259 35 44 104 84 32 64 128 256), losses := [] }

theorem u16294 : Upper (D 8) (R 8) [258,33,40,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16295 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 104 148 241 209 209 465), lower := (rows 259 35 44 104 148 32 64 128 256), losses := [] }

theorem u16295 : Upper (D 8) (R 8) [258,33,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16296 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 104 208 181 213 149 405), lower := (rows 259 35 44 104 208 32 64 128 256), losses := [] }

theorem u16296 : Upper (D 8) (R 8) [258,33,40,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16297 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 200 81 180 244 180 436), lower := (rows 259 35 44 200 81 32 64 128 256), losses := [] }

theorem u16297 : Upper (D 8) (R 8) [258,33,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16298 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 200 84 177 241 177 433), lower := (rows 259 35 44 200 84 32 64 128 256), losses := [] }

theorem u16298 : Upper (D 8) (R 8) [258,33,40,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16299 : Route 9 := (fun mask => (mask,id))

def c16299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16299 : Upper (D 8) (R 8) [258,33,40,192,96] 13 := by
  apply FastRouting.sound _ _ [258,33,40,192,96] 13 (by decide) (choices 1) [1,4,16,128] r16299 c16299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5857
  · exact u5858
  · exact u5859
  · exact u5860

def b16300 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 35 44 200 208 53 117 181 309), lower := (rows 259 35 44 200 208 32 64 128 256), losses := [] }

theorem u16300 : Upper (D 8) (R 8) [258,33,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16301 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 76 152 176 240 176 432), lower := (rows 259 35 69 76 152 32 64 128 256), losses := [] }

theorem u16301 : Upper (D 8) (R 8) [258,33,65,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16302 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 76 176 184 248 184 440), lower := (rows 259 35 69 76 176 32 64 128 256), losses := [] }

theorem u16302 : Upper (D 8) (R 8) [258,33,65,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16303 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 88 148 168 232 168 424), lower := (rows 259 35 69 88 148 32 64 128 256), losses := [] }

theorem u16303 : Upper (D 8) (R 8) [258,33,65,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16304 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 88 152 164 228 164 420), lower := (rows 259 35 69 88 152 32 64 128 256), losses := [] }

theorem u16304 : Upper (D 8) (R 8) [258,33,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16305 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 88 176 172 236 172 428), lower := (rows 259 35 69 88 176 32 64 128 256), losses := [] }

theorem u16305 : Upper (D 8) (R 8) [258,33,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16306 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 104 148 184 248 184 440), lower := (rows 259 35 69 104 148 32 64 128 256), losses := [] }

theorem u16306 : Upper (D 8) (R 8) [258,33,65,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16307 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 104 152 180 244 180 436), lower := (rows 259 35 69 104 152 32 64 128 256), losses := [] }

theorem u16307 : Upper (D 8) (R 8) [258,33,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16308 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 104 176 188 220 156 412), lower := (rows 259 35 69 104 176 32 64 128 256), losses := [] }

theorem u16308 : Upper (D 8) (R 8) [258,33,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16309 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 140 176 120 120 248 376), lower := (rows 259 35 69 140 176 32 64 128 256), losses := [] }

theorem u16309 : Upper (D 8) (R 8) [258,33,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16310 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 140 208 56 120 184 312), lower := (rows 259 35 69 140 208 32 64 128 256), losses := [] }

theorem u16310 : Upper (D 8) (R 8) [258,33,65,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16311 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 168 208 60 124 188 316), lower := (rows 259 35 69 168 208 32 64 128 256), losses := [] }

theorem u16311 : Upper (D 8) (R 8) [258,33,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16312 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 76 176 177 241 177 433), lower := (rows 259 35 76 76 176 32 64 128 256), losses := [] }

theorem u16312 : Upper (D 8) (R 8) [258,33,72,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16313 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 88 148 161 225 161 417), lower := (rows 259 35 76 88 148 32 64 128 256), losses := [] }

theorem u16313 : Upper (D 8) (R 8) [258,33,72,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16314 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 88 176 165 229 165 421), lower := (rows 259 35 76 88 176 32 64 128 256), losses := [] }

theorem u16314 : Upper (D 8) (R 8) [258,33,72,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16315 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 104 148 177 241 177 433), lower := (rows 259 35 76 104 148 32 64 128 256), losses := [] }

theorem u16315 : Upper (D 8) (R 8) [258,33,72,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16316 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 104 176 181 213 149 405), lower := (rows 259 35 76 104 176 32 64 128 256), losses := [] }

theorem u16316 : Upper (D 8) (R 8) [258,33,72,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16317 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 140 112 177 241 177 433), lower := (rows 259 35 76 140 112 32 64 128 256), losses := [] }

theorem u16317 : Upper (D 8) (R 8) [258,33,72,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16318 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 140 208 49 113 177 305), lower := (rows 259 35 76 140 208 32 64 128 256), losses := [] }

theorem u16318 : Upper (D 8) (R 8) [258,33,72,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16319 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 152 112 165 229 165 421), lower := (rows 259 35 76 152 112 32 64 128 256), losses := [] }

theorem u16319 : Upper (D 8) (R 8) [258,33,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16319
end Delivery.IrregularNine14.P08
