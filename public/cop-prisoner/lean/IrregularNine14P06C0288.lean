import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0076
import IrregularNine14P06C0077

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17280 : Route 9 := (fun mask => (mask,id))

def c17280 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17280 : Upper (D 6) (R 6) [10,160,65,20,320,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,320,1] 13 (by decide) (choices 1) [2,4,32] r17280 c17280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4610
  · exact u4611
  · exact u4612

def b17281 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 28 336 34 101 165 293), lower := (rows 11 162 69 28 336 34 64 128 256), losses := [] }

theorem u17281 : Upper (D 6) (R 6) [10,160,65,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17282 : Route 9 := (fun mask => (mask,id))

def c17282 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17282 : Upper (D 6) (R 6) [10,160,65,20,320,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,320,4] 13 (by decide) (choices 1) [1,2,32] r17282 c17282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4613
  · exact u4614
  · exact u4615

def b17283 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 69 44 22 33 336 464 336), lower := (rows 11 162 69 44 22 33 64 128 256), losses := [] }

theorem u17283 : Upper (D 6) (R 6) [10,160,65,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17284 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 44 22 48 321 449 321), lower := (rows 11 162 69 44 22 48 64 128 256), losses := [] }

theorem u17284 : Upper (D 6) (R 6) [10,160,65,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17284 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17285 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 69 44 22 96 337 401 273), lower := (rows 11 162 69 44 22 96 64 128 256), losses := [] }

theorem u17285 : Upper (D 6) (R 6) [10,160,65,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17286 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 44 22 288 81 209 337), lower := (rows 11 162 69 44 22 288 64 128 256), losses := [] }

theorem u17286 : Upper (D 6) (R 6) [10,160,65,36,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17286 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17287 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 69 44 82 33 340 404 276), lower := (rows 11 162 69 44 82 33 64 128 256), losses := [] }

theorem u17287 : Upper (D 6) (R 6) [10,160,65,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17288 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 69 44 82 36 337 401 273), lower := (rows 11 162 69 44 82 36 64 128 256), losses := [] }

theorem u17288 : Upper (D 6) (R 6) [10,160,65,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17289 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 44 82 48 325 389 261), lower := (rows 11 162 69 44 82 48 64 128 256), losses := [] }

theorem u17289 : Upper (D 6) (R 6) [10,160,65,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17289 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17290 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 44 82 288 85 149 277), lower := (rows 11 162 69 44 82 288 64 128 256), losses := [] }

theorem u17290 : Upper (D 6) (R 6) [10,160,65,36,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17290 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17291 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 69 44 273 34 84 212 340), lower := (rows 11 162 69 44 273 34 64 128 256), losses := [] }

theorem u17291 : Upper (D 6) (R 6) [10,160,65,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17292 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 69 44 273 36 82 210 338), lower := (rows 11 162 69 44 273 36 64 128 256), losses := [] }

theorem u17292 : Upper (D 6) (R 6) [10,160,65,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17293 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 44 273 48 70 198 326), lower := (rows 11 162 69 44 273 48 64 128 256), losses := [] }

theorem u17293 : Upper (D 6) (R 6) [10,160,65,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17293 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17294 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 69 44 273 96 86 150 278), lower := (rows 11 162 69 44 273 96 64 128 256), losses := [] }

theorem u17294 : Upper (D 6) (R 6) [10,160,65,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17295 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 69 44 274 33 84 212 340), lower := (rows 11 162 69 44 274 33 64 128 256), losses := [] }

theorem u17295 : Upper (D 6) (R 6) [10,160,65,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17296 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 69 44 274 36 81 209 337), lower := (rows 11 162 69 44 274 36 64 128 256), losses := [] }

theorem u17296 : Upper (D 6) (R 6) [10,160,65,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17297 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 44 274 48 69 197 325), lower := (rows 11 162 69 44 274 48 64 128 256), losses := [] }

theorem u17297 : Upper (D 6) (R 6) [10,160,65,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17297 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17298 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 69 44 274 96 85 149 277), lower := (rows 11 162 69 44 274 96 64 128 256), losses := [] }

theorem u17298 : Upper (D 6) (R 6) [10,160,65,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17299 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 69 44 276 33 82 210 338), lower := (rows 11 162 69 44 276 33 64 128 256), losses := [] }

theorem u17299 : Upper (D 6) (R 6) [10,160,65,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17300 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 69 44 276 34 81 209 337), lower := (rows 11 162 69 44 276 34 64 128 256), losses := [] }

theorem u17300 : Upper (D 6) (R 6) [10,160,65,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17301 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 69 44 276 48 67 195 323), lower := (rows 11 162 69 44 276 48 64 128 256), losses := [] }

theorem u17301 : Upper (D 6) (R 6) [10,160,65,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17301 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17302 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 69 44 276 96 83 147 275), lower := (rows 11 162 69 44 276 96 64 128 256), losses := [] }

theorem u17302 : Upper (D 6) (R 6) [10,160,65,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17303 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 69 44 336 33 86 150 278), lower := (rows 11 162 69 44 336 33 64 128 256), losses := [] }

theorem u17303 : Upper (D 6) (R 6) [10,160,65,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17304 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 69 44 336 34 85 149 277), lower := (rows 11 162 69 44 336 34 64 128 256), losses := [] }

theorem u17304 : Upper (D 6) (R 6) [10,160,65,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17305 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 69 44 336 36 83 147 275), lower := (rows 11 162 69 44 336 36 64 128 256), losses := [] }

theorem u17305 : Upper (D 6) (R 6) [10,160,65,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17306 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 44 336 48 71 135 263), lower := (rows 11 162 69 44 336 48 64 128 256), losses := [] }

theorem u17306 : Upper (D 6) (R 6) [10,160,65,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17306 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17307 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 69 56 276 33 70 198 326), lower := (rows 11 162 69 56 276 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 41 160 101 56 316 33 64 128 256) }] }

theorem u17307 : Upper (D 6) (R 6) [10,160,65,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17308 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 69 56 276 34 69 197 325), lower := (rows 11 162 69 56 276 34 64 128 256), losses := [] }

theorem u17308 : Upper (D 6) (R 6) [10,160,65,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17309 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 69 56 276 36 67 195 323), lower := (rows 11 162 69 56 276 36 64 128 256), losses := [] }

theorem u17309 : Upper (D 6) (R 6) [10,160,65,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17310 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 69 56 276 96 71 135 263), lower := (rows 11 162 69 56 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 10 162 100 56 316 96 96 128 256) }] }

theorem u17310 : Upper (D 6) (R 6) [10,160,65,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17311 : Route 9 := (fun mask => (mask,id))

def c17311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17311 : Upper (D 6) (R 6) [10,160,65,257,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257,6,4] 13 (by decide) (choices 1) [16,32] r17311 c17311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4616
  · exact u4617

def b17312 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 178, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 69 265 22 48 100 228 356), lower := (rows 11 162 69 265 22 48 64 128 256), losses := [] }

theorem u17312 : Upper (D 6) (R 6) [10,160,65,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17312 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17313 : Route 9 := (fun mask => (mask,id))

def c17313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17313 : Upper (D 6) (R 6) [10,160,65,257,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257,6,64] 13 (by decide) (choices 1) [4,16,32] r17313 c17313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4618
  · exact u4619
  · exact u4620

def b17314 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 265 52 34 84 212 340), lower := (rows 11 162 69 265 52 34 64 128 256), losses := [] }

theorem u17314 : Upper (D 6) (R 6) [10,160,65,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17315 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 69 265 52 36 82 210 338), lower := (rows 11 162 69 265 52 36 64 128 256), losses := [] }

theorem u17315 : Upper (D 6) (R 6) [10,160,65,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17316 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 69 265 52 48 70 198 326), lower := (rows 11 162 69 265 52 48 64 128 256), losses := [] }

theorem u17316 : Upper (D 6) (R 6) [10,160,65,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17316 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17317 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 69 265 52 96 86 150 278), lower := (rows 11 162 69 265 52 96 64 128 256), losses := [] }

theorem u17317 : Upper (D 6) (R 6) [10,160,65,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17318 : Route 9 := (fun mask => (mask,id))

def c17318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17318 : Upper (D 6) (R 6) [10,160,65,257,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257,66,4] 13 (by decide) (choices 1) [4,16,32] r17318 c17318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4621
  · exact u4622
  · exact u4623

def b17319 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 178, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 69 265 82 48 100 164 292), lower := (rows 11 162 69 265 82 48 64 128 256), losses := [] }

theorem u17319 : Upper (D 6) (R 6) [10,160,65,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17319 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17320 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 265 112 34 84 148 276), lower := (rows 11 162 69 265 112 34 64 128 256), losses := [] }

theorem u17320 : Upper (D 6) (R 6) [10,160,65,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17321 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 178, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 162 69 265 112 36 86 150 278), lower := (rows 11 162 69 265 112 36 64 128 256), losses := [] }

theorem u17321 : Upper (D 6) (R 6) [10,160,65,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17322 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 69 265 112 48 70 134 262), lower := (rows 11 162 69 265 112 48 64 128 256), losses := [] }

theorem u17322 : Upper (D 6) (R 6) [10,160,65,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17322 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17323 : Route 9 := (fun mask => (mask,id))

def c17323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17323 : Upper (D 6) (R 6) [10,160,65,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,6,1] 13 (by decide) (choices 1) [16,32] r17323 c17323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4624
  · exact u4625

def r17324 : Route 9 := (fun mask => (mask,id))

def c17324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17324 : Upper (D 6) (R 6) [10,160,65,260,6,16] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,6,16] 13 (by decide) (choices 1) [1,32] r17324 c17324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4626
  · exact u4627

def r17325 : Route 9 := (fun mask => (mask,id))

def c17325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17325 : Upper (D 6) (R 6) [10,160,65,260,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,6,64] 13 (by decide) (choices 1) [1,16,32] r17325 c17325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4628
  · exact u4629
  · exact u4630

def b17326 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 69 268 49 34 84 212 340), lower := (rows 11 162 69 268 49 34 64 128 256), losses := [] }

theorem u17326 : Upper (D 6) (R 6) [10,160,65,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17327 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 69 268 49 36 82 210 338), lower := (rows 11 162 69 268 49 36 64 128 256), losses := [] }

theorem u17327 : Upper (D 6) (R 6) [10,160,65,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17328 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 69 268 49 48 70 198 326), lower := (rows 11 162 69 268 49 48 64 128 256), losses := [] }

theorem u17328 : Upper (D 6) (R 6) [10,160,65,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17328 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17329 : Route 9 := (fun mask => (mask,id))

def c17329 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17329 : Upper (D 6) (R 6) [10,160,65,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,33,64] 13 (by decide) (choices 1) [2,4,16] r17329 c17329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4631
  · exact u4632
  · exact u4633

def b17330 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 69 268 52 33 82 210 338), lower := (rows 11 162 69 268 52 33 64 128 256), losses := [] }

theorem u17330 : Upper (D 6) (R 6) [10,160,65,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17331 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 268 52 34 81 209 337), lower := (rows 11 162 69 268 52 34 64 128 256), losses := [] }

theorem u17331 : Upper (D 6) (R 6) [10,160,65,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17332 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 69 268 52 48 67 195 323), lower := (rows 11 162 69 268 52 48 64 128 256), losses := [] }

theorem u17332 : Upper (D 6) (R 6) [10,160,65,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17332 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17333 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 69 268 52 96 83 147 275), lower := (rows 11 162 69 268 52 96 64 128 256), losses := [] }

theorem u17333 : Upper (D 6) (R 6) [10,160,65,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17334 : Route 9 := (fun mask => (mask,id))

def c17334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17334 : Upper (D 6) (R 6) [10,160,65,260,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,66,1] 13 (by decide) (choices 1) [4,16,32] r17334 c17334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4634
  · exact u4635
  · exact u4636

def r17335 : Route 9 := (fun mask => (mask,id))

def c17335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17335 : Upper (D 6) (R 6) [10,160,65,260,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,66,4] 13 (by decide) (choices 1) [1,16,32] r17335 c17335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4637
  · exact u4638
  · exact u4639

def r17336 : Route 9 := (fun mask => (mask,id))

def c17336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17336 : Upper (D 6) (R 6) [10,160,65,260,66,16] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,66,16] 13 (by decide) (choices 1) [1,4,32] r17336 c17336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4640
  · exact u4641
  · exact u4642

def r17337 : Route 9 := (fun mask => (mask,id))

def c17337 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17337 : Upper (D 6) (R 6) [10,160,65,260,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,96,1] 13 (by decide) (choices 1) [2,4,16] r17337 c17337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4643
  · exact u4644
  · exact u4645

def b17338 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 268 112 34 85 149 277), lower := (rows 11 162 69 268 112 34 64 128 256), losses := [] }

theorem u17338 : Upper (D 6) (R 6) [10,160,65,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17339 : Route 9 := (fun mask => (mask,id))

def c17339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17339 : Upper (D 6) (R 6) [10,160,65,260,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,96,4] 13 (by decide) (choices 1) [1,2,16] r17339 c17339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4646
  · exact u4647
  · exact u4648

#print axioms u17339
end Delivery.IrregularNine14.P06
