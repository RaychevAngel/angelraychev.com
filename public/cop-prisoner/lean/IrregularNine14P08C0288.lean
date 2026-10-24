import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0105

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17280 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 74 145 176 240 176 432), lower := (rows 289 7 76 74 145 32 64 128 256), losses := [] }

theorem u17280 : Upper (D 8) (R 8) [288,5,72,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17281 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 74 176 177 241 177 433), lower := (rows 289 7 76 74 176 32 64 128 256), losses := [] }

theorem u17281 : Upper (D 8) (R 8) [288,5,72,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17282 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 50 161 225 161 417), lower := (rows 289 7 76 88 50 32 64 128 256), losses := [] }

theorem u17282 : Upper (D 8) (R 8) [288,5,72,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17283 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 145 162 226 162 418), lower := (rows 289 7 76 88 145 32 64 128 256), losses := [] }

theorem u17283 : Upper (D 8) (R 8) [288,5,72,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17284 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 146 161 225 161 417), lower := (rows 289 7 76 88 146 32 64 128 256), losses := [] }

theorem u17284 : Upper (D 8) (R 8) [288,5,72,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17285 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 176 163 227 163 419), lower := (rows 289 7 76 88 176 32 64 128 256), losses := [] }

theorem u17285 : Upper (D 8) (R 8) [288,5,72,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17286 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 104 50 177 209 145 401), lower := (rows 289 7 76 104 50 32 64 128 256), losses := [] }

theorem u17286 : Upper (D 8) (R 8) [288,5,72,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17287 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 104 145 178 242 178 434), lower := (rows 289 7 76 104 145 32 64 128 256), losses := [] }

theorem u17287 : Upper (D 8) (R 8) [288,5,72,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17288 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 104 146 177 241 177 433), lower := (rows 289 7 76 104 146 32 64 128 256), losses := [] }

theorem u17288 : Upper (D 8) (R 8) [288,5,72,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17289 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 104 176 179 211 147 403), lower := (rows 289 7 76 104 176 32 64 128 256), losses := [] }

theorem u17289 : Upper (D 8) (R 8) [288,5,72,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17290 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 137 50 240 240 240 496), lower := (rows 289 7 76 137 50 32 64 128 256), losses := [] }

theorem u17290 : Upper (D 8) (R 8) [288,5,72,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17291 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 137 82 176 240 176 432), lower := (rows 289 7 76 137 82 32 64 128 256), losses := [] }

theorem u17291 : Upper (D 8) (R 8) [288,5,72,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17292 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 137 112 178 242 178 434), lower := (rows 289 7 76 137 112 32 64 128 256), losses := [] }

theorem u17292 : Upper (D 8) (R 8) [288,5,72,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17293 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 137 146 112 112 240 368), lower := (rows 289 7 76 137 146 32 64 128 256), losses := [] }

theorem u17293 : Upper (D 8) (R 8) [288,5,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17294 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 137 176 114 114 242 370), lower := (rows 289 7 76 137 176 32 64 128 256), losses := [] }

theorem u17294 : Upper (D 8) (R 8) [288,5,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17295 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 137 208 50 114 178 306), lower := (rows 289 7 76 137 208 32 64 128 256), losses := [] }

theorem u17295 : Upper (D 8) (R 8) [288,5,72,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17296 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 138 49 240 240 240 496), lower := (rows 289 7 76 138 49 32 64 128 256), losses := [] }

theorem u17296 : Upper (D 8) (R 8) [288,5,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17297 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 138 81 176 240 176 432), lower := (rows 289 7 76 138 81 32 64 128 256), losses := [] }

theorem u17297 : Upper (D 8) (R 8) [288,5,72,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17298 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 138 112 177 241 177 433), lower := (rows 289 7 76 138 112 32 64 128 256), losses := [] }

theorem u17298 : Upper (D 8) (R 8) [288,5,72,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17299 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 138 145 112 112 240 368), lower := (rows 289 7 76 138 145 32 64 128 256), losses := [] }

theorem u17299 : Upper (D 8) (R 8) [288,5,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17300 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 138 176 113 113 241 369), lower := (rows 289 7 76 138 176 32 64 128 256), losses := [] }

theorem u17300 : Upper (D 8) (R 8) [288,5,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17301 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 138 208 49 113 177 305), lower := (rows 289 7 76 138 208 32 64 128 256), losses := [] }

theorem u17301 : Upper (D 8) (R 8) [288,5,72,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17302 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 152 49 226 226 226 482), lower := (rows 289 7 76 152 49 32 64 128 256), losses := [] }

theorem u17302 : Upper (D 8) (R 8) [288,5,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17303 : Route 9 := (fun mask => (mask,id))

def c17303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17303 : Upper (D 8) (R 8) [288,5,72,144,34] 13 := by
  apply FastRouting.sound _ _ [288,5,72,144,34] 13 (by decide) (choices 1) [1,64,128] r17303 c17303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6302
  · exact u6303
  · exact u6304

def b17304 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 152 81 162 226 162 418), lower := (rows 289 7 76 152 81 32 64 128 256), losses := [] }

theorem u17304 : Upper (D 8) (R 8) [288,5,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17305 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 152 82 161 225 161 417), lower := (rows 289 7 76 152 82 32 64 128 256), losses := [] }

theorem u17305 : Upper (D 8) (R 8) [288,5,72,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17306 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 152 112 163 227 163 419), lower := (rows 289 7 76 152 112 32 64 128 256), losses := [] }

theorem u17306 : Upper (D 8) (R 8) [288,5,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17307 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 152 145 98 98 226 354), lower := (rows 289 7 76 152 145 32 64 128 256), losses := [] }

theorem u17307 : Upper (D 8) (R 8) [288,5,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17308 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 152 146 97 97 225 353), lower := (rows 289 7 76 152 146 32 64 128 256), losses := [] }

theorem u17308 : Upper (D 8) (R 8) [288,5,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17309 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 152 176 99 99 227 355), lower := (rows 289 7 76 152 176 32 64 128 256), losses := [] }

theorem u17309 : Upper (D 8) (R 8) [288,5,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17310 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 76 152 208 35 99 163 291), lower := (rows 289 7 76 152 208 32 64 128 256), losses := [] }

theorem u17310 : Upper (D 8) (R 8) [288,5,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17311 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 168 49 242 210 210 466), lower := (rows 289 7 76 168 49 32 64 128 256), losses := [] }

theorem u17311 : Upper (D 8) (R 8) [288,5,72,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17312 : Route 9 := (fun mask => (mask,id))

def c17312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17312 : Upper (D 8) (R 8) [288,5,72,160,34] 13 := by
  apply FastRouting.sound _ _ [288,5,72,160,34] 13 (by decide) (choices 1) [1,16,64,128] r17312 c17312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6305
  · exact u6306
  · exact u6307
  · exact u6308

def r17313 : Route 9 := (fun mask => (mask,id))

def c17313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17313 : Upper (D 8) (R 8) [288,5,72,160,65] 13 := by
  apply FastRouting.sound _ _ [288,5,72,160,65] 13 (by decide) (choices 1) [2,16,128] r17313 c17313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6309
  · exact u6310
  · exact u6311

def b17314 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 168 82 177 241 177 433), lower := (rows 289 7 76 168 82 32 64 128 256), losses := [] }

theorem u17314 : Upper (D 8) (R 8) [288,5,72,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17315 : Route 9 := (fun mask => (mask,id))

def c17315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17315 : Upper (D 8) (R 8) [288,5,72,160,96] 13 := by
  apply FastRouting.sound _ _ [288,5,72,160,96] 13 (by decide) (choices 1) [1,2,16,128] r17315 c17315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6312
  · exact u6313
  · exact u6314
  · exact u6315

def r17316 : Route 9 := (fun mask => (mask,id))

def c17316 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17316 : Upper (D 8) (R 8) [288,5,72,160,129] 13 := by
  apply FastRouting.sound _ _ [288,5,72,160,129] 13 (by decide) (choices 1) [2,16,64] r17316 c17316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6316
  · exact u6317
  · exact u6318

def b17317 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 168 146 113 113 241 369), lower := (rows 289 7 76 168 146 32 64 128 256), losses := [] }

theorem u17317 : Upper (D 8) (R 8) [288,5,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17318 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 76 168 176 115 83 211 339), lower := (rows 289 7 76 168 176 32 64 128 256), losses := [] }

theorem u17318 : Upper (D 8) (R 8) [288,5,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17319 : Route 9 := (fun mask => (mask,id))

def c17319 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17319 : Upper (D 8) (R 8) [288,5,72,160,192] 13 := by
  apply FastRouting.sound _ _ [288,5,72,160,192] 13 (by decide) (choices 1) [1,2,16] r17319 c17319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6319
  · exact u6320
  · exact u6321

def b17320 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 50 177 241 177 433), lower := (rows 289 7 76 200 50 32 64 128 256), losses := [] }

theorem u17320 : Upper (D 8) (R 8) [288,5,72,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17321 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 145 50 114 178 306), lower := (rows 289 7 76 200 145 32 64 128 256), losses := [] }

theorem u17321 : Upper (D 8) (R 8) [288,5,72,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17322 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 146 49 113 177 305), lower := (rows 289 7 76 200 146 32 64 128 256), losses := [] }

theorem u17322 : Upper (D 8) (R 8) [288,5,72,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17323 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 176 51 115 179 307), lower := (rows 289 7 76 200 176 32 64 128 256), losses := [] }

theorem u17323 : Upper (D 8) (R 8) [288,5,72,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17324 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 100 25 112 170 202 138 394), lower := (rows 289 7 100 25 112 32 64 128 256), losses := [] }

theorem u17324 : Upper (D 8) (R 8) [288,5,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17325_8 : Upper (D 8) (R 8) [288,5,96,17,160,8] 13 :=
  permutation_upper _ _ _ [288,5,96,17,160,2] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6322

theorem m17325_128 : Upper (D 8) (R 8) [288,5,96,17,160,128] 13 :=
  permutation_upper _ _ _ [288,5,96,17,160,64] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6323

def r17325 : Route 9 := (fun mask => (mask,id))

def c17325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17325 : Upper (D 8) (R 8) [288,5,96,17,160] 13 := by
  apply FastRouting.sound _ _ [288,5,96,17,160] 13 (by decide) (choices 1) [2,8,64,128] r17325 c17325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6322
  · exact m17325_8
  · exact u6323
  · exact m17325_128

def r17326 : Route 9 := (fun mask => (mask,id))

def c17326 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17326 : Upper (D 8) (R 8) [288,5,96,17,192] 13 := by
  apply FastRouting.sound _ _ [288,5,96,17,192] 13 (by decide) (choices 1) [2,8,128] r17326 c17326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6324
  · exact u6325
  · exact u6326

def b17327 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 100 26 49 232 200 200 456), lower := (rows 289 7 100 26 49 32 64 128 256), losses := [] }

theorem u17327 : Upper (D 8) (R 8) [288,5,96,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17328 : Route 9 := (fun mask => (mask,id))

def c17328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17328 : Upper (D 8) (R 8) [288,5,96,18,40] 13 := by
  apply FastRouting.sound _ _ [288,5,96,18,40] 13 (by decide) (choices 1) [1,64,128] r17328 c17328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6327
  · exact u6328
  · exact u6329

def b17329 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 100 26 81 168 232 168 424), lower := (rows 289 7 100 26 81 32 64 128 256), losses := [] }

theorem u17329 : Upper (D 8) (R 8) [288,5,96,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17330 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 26 88 161 225 161 417), lower := (rows 289 7 100 26 88 32 64 128 256), losses := [] }

theorem u17330 : Upper (D 8) (R 8) [288,5,96,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17331 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 100 26 112 169 201 137 393), lower := (rows 289 7 100 26 112 32 64 128 256), losses := [] }

theorem u17331 : Upper (D 8) (R 8) [288,5,96,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17332 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 100 26 145 232 232 232 488), lower := (rows 289 7 100 26 145 32 64 128 256), losses := [] }

theorem u17332 : Upper (D 8) (R 8) [288,5,96,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17333 : Route 9 := (fun mask => (mask,id))

def c17333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17333 : Upper (D 8) (R 8) [288,5,96,18,136] 13 := by
  apply FastRouting.sound _ _ [288,5,96,18,136] 13 (by decide) (choices 1) [1,64,128] r17333 c17333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6330
  · exact u6331
  · exact u6332

def r17334 : Route 9 := (fun mask => (mask,id))

def c17334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17334 : Upper (D 8) (R 8) [288,5,96,18,160] 13 := by
  apply FastRouting.sound _ _ [288,5,96,18,160] 13 (by decide) (choices 1) [1,8,64,128] r17334 c17334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6333
  · exact u6334
  · exact u6335
  · exact u6336

def b17335 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 26 208 169 233 169 425), lower := (rows 289 7 100 26 208 32 64 128 256), losses := [] }

theorem u17335 : Upper (D 8) (R 8) [288,5,96,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17336 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 100 41 88 178 210 146 402), lower := (rows 289 7 100 41 88 32 64 128 256), losses := [] }

theorem u17336 : Upper (D 8) (R 8) [288,5,96,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17337 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 100 41 146 248 216 216 472), lower := (rows 289 7 100 41 146 32 64 128 256), losses := [] }

theorem u17337 : Upper (D 8) (R 8) [288,5,96,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17338 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 100 41 152 242 210 210 466), lower := (rows 289 7 100 41 152 32 64 128 256), losses := [] }

theorem u17338 : Upper (D 8) (R 8) [288,5,96,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17339 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 100 41 208 186 218 154 410), lower := (rows 289 7 100 41 208 32 64 128 256), losses := [] }

theorem u17339 : Upper (D 8) (R 8) [288,5,96,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17339
end Delivery.IrregularNine14.P08
