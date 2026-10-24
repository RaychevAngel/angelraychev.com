import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0167

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27300 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 14 25 176 34 193 193 449), lower := (rows 37 322 14 25 176 34 64 128 256), losses := [] }

theorem u27300 : Upper (D 7) (R 7) [36,320,10,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27301 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 37 322 14 25 176 96 195 131 387), lower := (rows 37 322 14 25 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 352 45 25 176 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 16 98 64 0 256), good := (rows 37 354 47 25 48 96 96 0 256) }] }

theorem u27301 : Upper (D 7) (R 7) [36,320,10,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27302 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 14 25 176 160 67 195 323), lower := (rows 37 322 14 25 176 160 64 128 256), losses := [] }

theorem u27302 : Upper (D 7) (R 7) [36,320,10,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27303 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 37 322 14 25 208 33 226 162 418), lower := (rows 37 322 14 25 208 33 64 128 256), losses := [] }

theorem u27303 : Upper (D 7) (R 7) [36,320,10,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27304 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 14 25 208 34 225 161 417), lower := (rows 37 322 14 25 208 34 64 128 256), losses := [] }

theorem u27304 : Upper (D 7) (R 7) [36,320,10,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27305 : Route 9 := (fun mask => (mask,id))

def c27305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27305 : Upper (D 7) (R 7) [36,320,10,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,320,10,17,192,128] 13 (by decide) (choices 1) [1,2,32] r27305 c27305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10030
  · exact u10031
  · exact u10032

def b27306 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 14 56 145 33 194 194 450), lower := (rows 37 322 14 56 145 33 64 128 256), losses := [] }

theorem u27306 : Upper (D 7) (R 7) [36,320,10,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27307 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 322 14 56 145 34 193 193 449), lower := (rows 37 322 14 56 145 34 64 128 256), losses := [] }

theorem u27307 : Upper (D 7) (R 7) [36,320,10,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27308 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,5),(4,5)], upper := (rows 37 322 14 56 145 96 195 131 387), lower := (rows 37 322 14 56 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 352 45 56 145 96 96 128 256) },{ target := 5, region := (rows 1 27 12 8 17 0 81 145 273), good := (rows 471 322 14 478 467 64 64 128 256) }] }

theorem u27308 : Upper (D 7) (R 7) [36,320,10,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27309 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 322 14 56 145 160 67 195 323), lower := (rows 37 322 14 56 145 160 64 128 256), losses := [] }

theorem u27309 : Upper (D 7) (R 7) [36,320,10,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27310 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 14 56 146 33 193 193 449), lower := (rows 37 322 14 56 146 33 64 128 256), losses := [] }

theorem u27310 : Upper (D 7) (R 7) [36,320,10,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27311 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,0),(4,5)], upper := (rows 37 322 14 56 146 96 193 129 385), lower := (rows 37 322 14 56 146 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 98 64 128 256), good := (rows 36 354 46 60 190 96 96 128 256) }] }

theorem u27311 : Upper (D 7) (R 7) [36,320,10,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27312 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 322 14 56 146 160 65 193 321), lower := (rows 37 322 14 56 146 160 64 128 256), losses := [] }

theorem u27312 : Upper (D 7) (R 7) [36,320,10,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27313 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 37 322 14 56 208 33 195 131 387), lower := (rows 37 322 14 56 208 33 64 128 256), losses := [] }

theorem u27313 : Upper (D 7) (R 7) [36,320,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27314 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 322 14 56 208 34 193 129 385), lower := (rows 37 322 14 56 208 34 64 128 256), losses := [] }

theorem u27314 : Upper (D 7) (R 7) [36,320,10,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27315 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 322 14 56 208 160 67 131 259), lower := (rows 37 322 14 56 208 160 64 128 256), losses := [] }

theorem u27315 : Upper (D 7) (R 7) [36,320,10,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27316 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 14 73 50 33 208 144 400), lower := (rows 37 322 14 73 50 33 64 128 256), losses := [] }

theorem u27316 : Upper (D 7) (R 7) [36,320,10,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27317 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 14 73 50 48 193 129 385), lower := (rows 37 322 14 73 50 48 64 128 256), losses := [] }

theorem u27317 : Upper (D 7) (R 7) [36,320,10,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27317 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27318 : Route 9 := (fun mask => (mask,id))

def c27318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27318 : Upper (D 7) (R 7) [36,320,10,65,34,128] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65,34,128] 13 (by decide) (choices 1) [1,16,128] r27318 c27318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10033
  · exact u10034
  · exact u10035

def b27319 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 37 322 14 73 145 34 240 176 432), lower := (rows 37 322 14 73 145 34 64 128 256), losses := [] }

theorem u27319 : Upper (D 7) (R 7) [36,320,10,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27320 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 322 14 73 145 48 226 162 418), lower := (rows 37 322 14 73 145 48 64 128 256), losses := [] }

theorem u27320 : Upper (D 7) (R 7) [36,320,10,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27320 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27321 : Route 9 := (fun mask => (mask,id))

def c27321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27321 : Upper (D 7) (R 7) [36,320,10,65,129,128] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65,129,128] 13 (by decide) (choices 1) [2,16,32] r27321 c27321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10036
  · exact u10037
  · exact u10038

def b27322 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 14 73 146 33 240 176 432), lower := (rows 37 322 14 73 146 33 64 128 256), losses := [] }

theorem u27322 : Upper (D 7) (R 7) [36,320,10,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27323 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 37 322 14 73 146 48 225 161 417), lower := (rows 37 322 14 73 146 48 64 128 256), losses := [] }

theorem u27323 : Upper (D 7) (R 7) [36,320,10,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27323 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27324 : Route 9 := (fun mask => (mask,id))

def c27324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27324 : Upper (D 7) (R 7) [36,320,10,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,10,65,130,128] 13 (by decide) (choices 1) [1,16,32] r27324 c27324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10039
  · exact u10040
  · exact u10041

def b27325 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 14 73 176 33 210 146 402), lower := (rows 37 322 14 73 176 33 64 128 256), losses := [] }

theorem u27325 : Upper (D 7) (R 7) [36,320,10,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27326 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 37 322 14 73 176 34 209 145 401), lower := (rows 37 322 14 73 176 34 64 128 256), losses := [] }

theorem u27326 : Upper (D 7) (R 7) [36,320,10,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27327 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 14 73 176 48 195 131 387), lower := (rows 37 322 14 73 176 48 64 128 256), losses := [] }

theorem u27327 : Upper (D 7) (R 7) [36,320,10,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27327 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27328 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 14 73 176 160 83 147 275), lower := (rows 37 322 14 73 176 160 64 128 256), losses := [] }

theorem u27328 : Upper (D 7) (R 7) [36,320,10,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27329 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 14 88 145 33 226 162 418), lower := (rows 37 322 14 88 145 33 64 128 256), losses := [] }

theorem u27329 : Upper (D 7) (R 7) [36,320,10,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27330 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 14 88 145 34 225 161 417), lower := (rows 37 322 14 88 145 34 64 128 256), losses := [] }

theorem u27330 : Upper (D 7) (R 7) [36,320,10,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27331 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(2,7),(4,6)], upper := (rows 37 322 14 88 145 160 99 163 291), lower := (rows 37 322 14 88 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 19 28 24 16 32 65 0 257), good := (rows 359 322 14 94 351 32 64 0 256) }] }

theorem u27331 : Upper (D 7) (R 7) [36,320,10,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27332 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 14 88 146 33 225 161 417), lower := (rows 37 322 14 88 146 33 64 128 256), losses := [] }

theorem u27332 : Upper (D 7) (R 7) [36,320,10,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27333 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,6)], upper := (rows 37 322 14 88 146 160 97 161 289), lower := (rows 37 322 14 88 146 160 64 128 256), losses := [] }

theorem u27333 : Upper (D 7) (R 7) [36,320,10,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27334 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 322 14 88 176 33 195 131 387), lower := (rows 37 322 14 88 176 33 64 128 256), losses := [] }

theorem u27334 : Upper (D 7) (R 7) [36,320,10,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27335 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 14 88 176 34 193 129 385), lower := (rows 37 322 14 88 176 34 64 128 256), losses := [] }

theorem u27335 : Upper (D 7) (R 7) [36,320,10,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27336 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 14 88 176 160 67 131 259), lower := (rows 37 322 14 88 176 160 64 128 256), losses := [] }

theorem u27336 : Upper (D 7) (R 7) [36,320,10,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27337 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 322 14 137 19 48 224 224 480), lower := (rows 37 322 14 137 19 48 64 128 256), losses := [] }

theorem u27337 : Upper (D 7) (R 7) [36,320,10,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27337 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27338 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(3,1)], upper := (rows 37 322 14 137 19 96 240 176 432), lower := (rows 37 322 14 137 19 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 114 80 144 272), good := (rows 37 352 45 137 505 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 20 98 64 0 256), good := (rows 53 354 63 9 51 96 96 0 256) }] }

theorem u27338 : Upper (D 7) (R 7) [36,320,10,129,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27339 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(1,0),(1,7),(3,1),(4,7)], upper := (rows 37 322 14 137 19 160 112 240 368), lower := (rows 37 322 14 137 19 160 64 128 256), losses := [] }

theorem u27339 : Upper (D 7) (R 7) [36,320,10,129,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27340 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 322 14 137 50 33 208 208 464), lower := (rows 37 322 14 137 50 33 64 128 256), losses := [] }

theorem u27340 : Upper (D 7) (R 7) [36,320,10,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27341 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 322 14 137 50 48 193 193 449), lower := (rows 37 322 14 137 50 48 64 128 256), losses := [] }

theorem u27341 : Upper (D 7) (R 7) [36,320,10,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27341 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27342 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 14 137 50 96 209 145 401), lower := (rows 37 322 14 137 50 96 64 128 256), losses := [] }

theorem u27342 : Upper (D 7) (R 7) [36,320,10,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27343 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,7),(4,0),(4,7)], upper := (rows 37 322 14 137 50 160 81 209 337), lower := (rows 37 322 14 137 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 52 322 62 168 50 160 64 160 256) },{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 320 45 169 48 160 64 160 256) }] }

theorem u27343 : Upper (D 7) (R 7) [36,320,10,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27344 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 14 137 81 34 240 176 432), lower := (rows 37 322 14 137 81 34 64 128 256), losses := [] }

theorem u27344 : Upper (D 7) (R 7) [36,320,10,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27345 : Route 9 := (fun mask => (mask,id))

def c27345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27345 : Upper (D 7) (R 7) [36,320,10,129,65,16] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,65,16] 13 (by decide) (choices 1) [2,32,128] r27345 c27345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10042
  · exact u10043
  · exact u10044

def b27346 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 322 14 137 81 160 114 178 306), lower := (rows 37 322 14 137 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 320 45 169 81 160 64 160 256) }] }

theorem u27346 : Upper (D 7) (R 7) [36,320,10,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27347 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 14 137 112 33 210 146 402), lower := (rows 37 322 14 137 112 33 64 128 256), losses := [] }

theorem u27347 : Upper (D 7) (R 7) [36,320,10,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27348 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 322 14 137 112 34 209 145 401), lower := (rows 37 322 14 137 112 34 64 128 256), losses := [] }

theorem u27348 : Upper (D 7) (R 7) [36,320,10,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27349 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 14 137 112 48 195 131 387), lower := (rows 37 322 14 137 112 48 64 128 256), losses := [] }

theorem u27349 : Upper (D 7) (R 7) [36,320,10,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27349 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27350 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 322 14 137 112 160 83 147 275), lower := (rows 37 322 14 137 112 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 320 45 169 112 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 258 47 169 48 160 0 160 256) }] }

theorem u27350 : Upper (D 7) (R 7) [36,320,10,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27351 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 14 137 146 33 112 240 368), lower := (rows 37 322 14 137 146 33 64 128 256), losses := [] }

theorem u27351 : Upper (D 7) (R 7) [36,320,10,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27352 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 14 137 146 48 97 225 353), lower := (rows 37 322 14 137 146 48 64 128 256), losses := [] }

theorem u27352 : Upper (D 7) (R 7) [36,320,10,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27352 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27353 : Route 9 := (fun mask => (mask,id))

def c27353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27353 : Upper (D 7) (R 7) [36,320,10,129,130,64] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,130,64] 13 (by decide) (choices 1) [1,16,32] r27353 c27353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10045
  · exact u10046
  · exact u10047

def b27354 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 14 137 176 33 82 210 338), lower := (rows 37 322 14 137 176 33 64 128 256), losses := [] }

theorem u27354 : Upper (D 7) (R 7) [36,320,10,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27355 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 14 137 176 34 81 209 337), lower := (rows 37 322 14 137 176 34 64 128 256), losses := [] }

theorem u27355 : Upper (D 7) (R 7) [36,320,10,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27356 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 14 137 176 48 67 195 323), lower := (rows 37 322 14 137 176 48 64 128 256), losses := [] }

theorem u27356 : Upper (D 7) (R 7) [36,320,10,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27356 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27357 : Route 9 := (fun mask => (mask,id))

def c27357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27357 : Upper (D 7) (R 7) [36,320,10,129,160,64] 13 := by
  apply FastRouting.sound _ _ [36,320,10,129,160,64] 13 (by decide) (choices 1) [1,2,16] r27357 c27357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10048
  · exact u10049
  · exact u10050

def b27358 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 14 137 208 33 114 178 306), lower := (rows 37 322 14 137 208 33 64 128 256), losses := [] }

theorem u27358 : Upper (D 7) (R 7) [36,320,10,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27359 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 14 137 208 34 113 177 305), lower := (rows 37 322 14 137 208 34 64 128 256), losses := [] }

theorem u27359 : Upper (D 7) (R 7) [36,320,10,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27359
end Delivery.IrregularNine14.P07
