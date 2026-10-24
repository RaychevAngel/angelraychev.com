import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0153
import IrregularNine14P06C0154

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28080 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(3,5),(4,0)], upper := (rows 7 26 37 137 304 102 70 198 326), lower := (rows 7 26 37 137 304 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 29 33 65 129 257), good := (rows 502 26 500 506 304 32 64 128 256) }] }

theorem u28080 : Upper (D 6) (R 6) [6,24,33,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28081 : Route 9 := (fun mask => (mask,id))

def c28081 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28081 : Upper (D 6) (R 6) [6,24,33,129,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,129,320] 13 (by decide) (choices 1) [2,4,64] r28081 c28081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9237
  · exact u9238
  · exact u9239

def b28082 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 232, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 37 138 276 97 97 225 353), lower := (rows 7 26 37 138 276 32 64 128 256), losses := [] }

theorem u28082 : Upper (D 6) (R 6) [6,24,33,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28083 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 37 138 304 101 69 197 325), lower := (rows 7 26 37 138 304 32 64 128 256), losses := [] }

theorem u28083 : Upper (D 6) (R 6) [6,24,33,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28084 : Route 9 := (fun mask => (mask,id))

def c28084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28084 : Upper (D 6) (R 6) [6,24,33,130,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,130,320] 13 (by decide) (choices 1) [1,4,64] r28084 c28084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9240
  · exact u9241
  · exact u9242

def b28085 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,2),(3,5),(4,2)], upper := (rows 7 26 37 140 304 99 67 195 323), lower := (rows 7 26 37 140 304 32 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 21 33 65 129 257), good := (rows 499 26 497 154 304 32 64 128 256) }] }

theorem u28085 : Upper (D 6) (R 6) [6,24,33,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28086 : Route 9 := (fun mask => (mask,id))

def c28086 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28086 : Upper (D 6) (R 6) [6,24,33,132,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,132,320] 13 (by decide) (choices 1) [1,2,64] r28086 c28086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9243
  · exact u9244
  · exact u9245

def r28087 : Route 9 := (fun mask => (mask,id))

def c28087 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28087 : Upper (D 6) (R 6) [6,24,33,160,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,160,320] 13 (by decide) (choices 1) [1,2,4,64] r28087 c28087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9246
  · exact u9247
  · exact u9248
  · exact u9249

def r28088 : Route 9 := (fun mask => (mask,id))

def c28088 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28088 : Upper (D 6) (R 6) [6,24,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,320] 13 (by decide) (choices 1) [1,2,4] r28088 c28088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9250
  · exact u9251
  · exact u9252

def b28089 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 26 100 11 49 484 452 452 452), lower := (rows 7 26 100 11 49 32 64 128 256), losses := [] }

theorem u28089 : Upper (D 6) (R 6) [6,24,96,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28090 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 26 100 11 145 356 356 484 356), lower := (rows 7 26 100 11 145 32 64 128 256), losses := [] }

theorem u28090 : Upper (D 6) (R 6) [6,24,96,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28091 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 100 11 148 353 353 481 353), lower := (rows 7 26 100 11 148 32 64 128 256), losses := [] }

theorem u28091 : Upper (D 6) (R 6) [6,24,96,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28092 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 100 11 176 357 325 453 325), lower := (rows 7 26 100 11 176 32 64 128 256), losses := [] }

theorem u28092 : Upper (D 6) (R 6) [6,24,96,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28093 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 26 100 11 400 101 101 229 357), lower := (rows 7 26 100 11 400 32 64 128 256), losses := [] }

theorem u28093 : Upper (D 6) (R 6) [6,24,96,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28094 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 13 49 482 450 450 450), lower := (rows 7 26 100 13 49 32 64 128 256), losses := [] }

theorem u28094 : Upper (D 6) (R 6) [6,24,96,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28095 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 100 13 145 354 354 482 354), lower := (rows 7 26 100 13 145 32 64 128 256), losses := [] }

theorem u28095 : Upper (D 6) (R 6) [6,24,96,5,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28096 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 7 26 100 13 146 353 353 481 353), lower := (rows 7 26 100 13 146 32 64 128 256), losses := [] }

theorem u28096 : Upper (D 6) (R 6) [6,24,96,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28097 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 3, region := 498, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 26 100 13 176 355 323 451 323), lower := (rows 7 26 100 13 176 32 64 128 256), losses := [] }

theorem u28097 : Upper (D 6) (R 6) [6,24,96,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28098 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 100 13 400 99 99 227 355), lower := (rows 7 26 100 13 400 32 64 128 256), losses := [] }

theorem u28098 : Upper (D 6) (R 6) [6,24,96,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28099 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 14 49 481 449 449 449), lower := (rows 7 26 100 14 49 32 64 128 256), losses := [] }

theorem u28099 : Upper (D 6) (R 6) [6,24,96,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28100 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 100 14 145 353 353 481 353), lower := (rows 7 26 100 14 145 32 64 128 256), losses := [] }

theorem u28100 : Upper (D 6) (R 6) [6,24,96,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28101 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 26 100 14 176 353 321 449 321), lower := (rows 7 26 100 14 176 32 64 128 256), losses := [] }

theorem u28101 : Upper (D 6) (R 6) [6,24,96,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28102 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 100 14 400 97 97 225 353), lower := (rows 7 26 100 14 400 32 64 128 256), losses := [] }

theorem u28102 : Upper (D 6) (R 6) [6,24,96,6,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28103 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(2,0),(3,6),(4,5)], upper := (rows 7 26 100 41 81 422 454 390 390), lower := (rows 7 26 100 41 81 32 64 128 256), losses := [] }

theorem u28103 : Upper (D 6) (R 6) [6,24,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28104 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 100 41 82 421 453 389 389), lower := (rows 7 26 100 41 82 32 64 128 256), losses := [] }

theorem u28104 : Upper (D 6) (R 6) [6,24,96,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28105 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 26 100 41 84 419 451 387 387), lower := (rows 7 26 100 41 84 32 64 128 256), losses := [] }

theorem u28105 : Upper (D 6) (R 6) [6,24,96,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28106 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 356, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 7 26 100 41 145 358 326 454 326), lower := (rows 7 26 100 41 145 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 65 129 257), good := (rows 471 26 68 475 465 0 64 128 256) }] }

theorem u28106 : Upper (D 6) (R 6) [6,24,96,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28107 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 100 41 146 357 325 453 325), lower := (rows 7 26 100 41 146 32 64 128 256), losses := [] }

theorem u28107 : Upper (D 6) (R 6) [6,24,96,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28108 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 360, targets := 4 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,5),(3,2),(4,5)], upper := (rows 7 26 100 41 148 355 323 451 323), lower := (rows 7 26 100 41 148 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 17 0 73 137 265), good := (rows 471 474 68 475 148 0 64 128 256) }] }

theorem u28108 : Upper (D 6) (R 6) [6,24,96,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28109 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 296, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 7 26 100 41 208 295 327 391 263), lower := (rows 7 26 100 41 208 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 65 129 257), good := (rows 471 26 68 475 208 0 64 128 256) }] }

theorem u28109 : Upper (D 6) (R 6) [6,24,96,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28110 : Route 9 := (fun mask => (mask,id))

def c28110 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28110 : Upper (D 6) (R 6) [6,24,96,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,384] 13 (by decide) (choices 1) [1,2,4,64] r28110 c28110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9253
  · exact u9254
  · exact u9255
  · exact u9256

def b28111 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 26 100 42 145 357 325 453 325), lower := (rows 7 26 100 42 145 32 64 128 256), losses := [] }

theorem u28111 : Upper (D 6) (R 6) [6,24,96,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28112 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 360, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 100 42 148 353 321 449 321), lower := (rows 7 26 100 42 148 32 64 128 256), losses := [] }

theorem u28112 : Upper (D 6) (R 6) [6,24,96,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28113 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 26 100 42 208 293 325 389 261), lower := (rows 7 26 100 42 208 32 64 128 256), losses := [] }

theorem u28113 : Upper (D 6) (R 6) [6,24,96,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28114 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 26 100 42 400 101 69 197 325), lower := (rows 7 26 100 42 400 32 64 128 256), losses := [] }

theorem u28114 : Upper (D 6) (R 6) [6,24,96,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28115 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 100 44 145 355 323 451 323), lower := (rows 7 26 100 44 145 32 64 128 256), losses := [] }

theorem u28115 : Upper (D 6) (R 6) [6,24,96,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28116 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 100 44 146 353 321 449 321), lower := (rows 7 26 100 44 146 32 64 128 256), losses := [] }

theorem u28116 : Upper (D 6) (R 6) [6,24,96,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28117 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 100 44 208 291 323 387 259), lower := (rows 7 26 100 44 208 32 64 128 256), losses := [] }

theorem u28117 : Upper (D 6) (R 6) [6,24,96,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28118 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 100 44 400 99 67 195 323), lower := (rows 7 26 100 44 400 32 64 128 256), losses := [] }

theorem u28118 : Upper (D 6) (R 6) [6,24,96,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28119 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 26 100 104 145 295 327 391 263), lower := (rows 7 26 100 104 145 32 64 128 256), losses := [] }

theorem u28119 : Upper (D 6) (R 6) [6,24,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28120 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 400, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 100 104 146 293 325 389 261), lower := (rows 7 26 100 104 146 32 64 128 256), losses := [] }

theorem u28120 : Upper (D 6) (R 6) [6,24,96,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28121 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 26 100 104 148 291 323 387 259), lower := (rows 7 26 100 104 148 32 64 128 256), losses := [] }

theorem u28121 : Upper (D 6) (R 6) [6,24,96,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28122 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 26 100 104 400 39 71 135 263), lower := (rows 7 26 100 104 400 32 64 128 256), losses := [] }

theorem u28122 : Upper (D 6) (R 6) [6,24,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28123 : Route 9 := (fun mask => (mask,id))

def c28123 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28123 : Upper (D 6) (R 6) [6,24,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257] 13 (by decide) (choices 1) [2,4,64] r28123 c28123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9257
  · exact u9258
  · exact u9259

def r28124 : Route 9 := (fun mask => (mask,id))

def c28124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28124 : Upper (D 6) (R 6) [6,24,96,129,258] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,258] 13 (by decide) (choices 1) [1,4,64] r28124 c28124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9260
  · exact u9261
  · exact u9262

def r28125 : Route 9 := (fun mask => (mask,id))

def c28125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28125 : Upper (D 6) (R 6) [6,24,96,129,260] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260] 13 (by decide) (choices 1) [1,2,64] r28125 c28125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9263
  · exact u9264
  · exact u9265

def r28126 : Route 9 := (fun mask => (mask,id))

def c28126 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28126 : Upper (D 6) (R 6) [6,24,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288] 13 (by decide) (choices 1) [1,2,4,64] r28126 c28126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9266
  · exact u9267
  · exact u9268
  · exact u9269

def b28127 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 232, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 100 138 276 97 97 225 353), lower := (rows 7 26 100 138 276 32 64 128 256), losses := [] }

theorem u28127 : Upper (D 6) (R 6) [6,24,96,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28128 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 100 138 304 101 69 197 325), lower := (rows 7 26 100 138 304 32 64 128 256), losses := [] }

theorem u28128 : Upper (D 6) (R 6) [6,24,96,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28129 : Route 9 := (fun mask => (mask,id))

def c28129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28129 : Upper (D 6) (R 6) [6,24,96,132,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,288] 13 (by decide) (choices 1) [1,2,64] r28129 c28129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9270
  · exact u9271
  · exact u9272

def r28130 : Route 9 := (fun mask => (mask,id))

def c28130 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28130 : Upper (D 6) (R 6) [6,24,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,320] 13 (by decide) (choices 1) [1,2,4] r28130 c28130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9273
  · exact u9274
  · exact u9275

def b28131 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 133 11 52 352 352 480 352), lower := (rows 7 26 133 11 52 32 64 128 256), losses := [] }

theorem u28131 : Upper (D 6) (R 6) [6,24,129,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28132 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 26 133 11 112 356 356 484 356), lower := (rows 7 26 133 11 112 32 64 128 256), losses := [] }

theorem u28132 : Upper (D 6) (R 6) [6,24,129,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28133 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 133 11 276 96 96 224 352), lower := (rows 7 26 133 11 276 32 64 128 256), losses := [] }

theorem u28133 : Upper (D 6) (R 6) [6,24,129,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28134 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 26 133 11 304 100 100 228 356), lower := (rows 7 26 133 11 304 32 64 128 256), losses := [] }

theorem u28134 : Upper (D 6) (R 6) [6,24,129,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28135 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 13 50 352 352 480 352), lower := (rows 7 26 133 13 50 32 64 128 256), losses := [] }

theorem u28135 : Upper (D 6) (R 6) [6,24,129,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28136 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 13 112 354 354 482 354), lower := (rows 7 26 133 13 112 32 64 128 256), losses := [] }

theorem u28136 : Upper (D 6) (R 6) [6,24,129,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28137 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 13 274 96 96 224 352), lower := (rows 7 26 133 13 274 32 64 128 256), losses := [] }

theorem u28137 : Upper (D 6) (R 6) [6,24,129,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28138 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 13 304 98 98 226 354), lower := (rows 7 26 133 13 304 32 64 128 256), losses := [] }

theorem u28138 : Upper (D 6) (R 6) [6,24,129,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28139 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 133 14 49 352 352 480 352), lower := (rows 7 26 133 14 49 32 64 128 256), losses := [] }

theorem u28139 : Upper (D 6) (R 6) [6,24,129,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28139
end Delivery.IrregularNine14.P06
