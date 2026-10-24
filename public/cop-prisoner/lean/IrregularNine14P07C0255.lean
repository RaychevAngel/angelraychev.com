import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0051
import IrregularNine14P07C0052

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15300 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,5)], upper := (rows 7 290 76 41 145 160 82 210 338), lower := (rows 7 290 76 41 145 160 64 128 256), losses := [] }

theorem u15300 : Upper (D 7) (R 7) [6,288,72,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15301 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 290 76 41 146 33 208 208 464), lower := (rows 7 290 76 41 146 33 64 128 256), losses := [] }

theorem u15301 : Upper (D 7) (R 7) [6,288,72,33,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15302 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 196, targets := 34 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 7 290 76 41 146 48 193 193 449), lower := (rows 7 290 76 41 146 48 64 128 256), losses := [] }

theorem u15302 : Upper (D 7) (R 7) [6,288,72,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15302 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15303 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 402, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,6),(3,1),(4,5),(4,6)], upper := (rows 7 290 76 41 146 96 209 145 401), lower := (rows 7 290 76 41 146 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 100 64 128 256), good := (rows 45 288 108 41 144 96 96 128 256) }] }

theorem u15303 : Upper (D 7) (R 7) [6,288,72,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15304 : Route 9 := (fun mask => (mask,id))

def c15304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15304 : Upper (D 7) (R 7) [6,288,72,33,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,130,128] 13 (by decide) (choices 1) [1,16] r15304 c15304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3061
  · exact u3062

def b15305 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 290 76 41 208 33 210 146 402), lower := (rows 7 290 76 41 208 33 64 128 256), losses := [] }

theorem u15305 : Upper (D 7) (R 7) [6,288,72,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15306 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 76 41 208 34 209 145 401), lower := (rows 7 290 76 41 208 34 64 128 256), losses := [] }

theorem u15306 : Upper (D 7) (R 7) [6,288,72,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15307 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 386, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 7 290 76 41 208 48 195 131 387), lower := (rows 7 290 76 41 208 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 258 92 477 208 16 64 128 256) }] }

theorem u15307 : Upper (D 7) (R 7) [6,288,72,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15307 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15308 : Route 9 := (fun mask => (mask,id))

def c15308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15308 : Upper (D 7) (R 7) [6,288,72,33,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,192,128] 13 (by decide) (choices 1) [1,2,16] r15308 c15308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3063
  · exact u3064
  · exact u3065

def b15309 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 7 290 76 56 82 33 193 129 385), lower := (rows 7 290 76 56 82 33 64 128 256), losses := [] }

theorem u15309 : Upper (D 7) (R 7) [6,288,72,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15310 : Route 9 := (fun mask => (mask,id))

def c15310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15310 : Upper (D 7) (R 7) [6,288,72,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,66,128] 13 (by decide) (choices 1) [1,128] r15310 c15310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3066
  · exact u3067

def b15311 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 290 76 56 145 33 194 194 450), lower := (rows 7 290 76 56 145 33 64 128 256), losses := [] }

theorem u15311 : Upper (D 7) (R 7) [6,288,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15312 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 76 56 145 34 193 193 449), lower := (rows 7 290 76 56 145 34 64 128 256), losses := [] }

theorem u15312 : Upper (D 7) (R 7) [6,288,72,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15313 : Route 9 := (fun mask => (mask,id))

def c15313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15313 : Upper (D 7) (R 7) [6,288,72,48,129,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,129,64] 13 (by decide) (choices 1) [1,2,128] r15313 c15313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3068
  · exact u3069
  · exact u3070

def b15314 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 76 56 145 160 67 195 323), lower := (rows 7 290 76 56 145 160 64 128 256), losses := [] }

theorem u15314 : Upper (D 7) (R 7) [6,288,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15315 : Route 9 := (fun mask => (mask,id))

def c15315 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15315 : Upper (D 7) (R 7) [6,288,72,48,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,130,1] 13 (by decide) (choices 1) [1,128] r15315 c15315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3071
  · exact u3072

def r15316 : Route 9 := (fun mask => (mask,id))

def c15316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15316 : Upper (D 7) (R 7) [6,288,72,48,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,130,64] 13 (by decide) (choices 1) [1,128] r15316 c15316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3073
  · exact u3074

def b15317 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 76 56 146 160 65 193 321), lower := (rows 7 290 76 56 146 160 64 128 256), losses := [] }

theorem u15317 : Upper (D 7) (R 7) [6,288,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15318 : Route 9 := (fun mask => (mask,id))

def c15318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15318 : Upper (D 7) (R 7) [6,288,72,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,192,1] 13 (by decide) (choices 1) [1,2,128] r15318 c15318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3075
  · exact u3076
  · exact u3077

def b15319 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 76 56 208 34 193 129 385), lower := (rows 7 290 76 56 208 34 64 128 256), losses := [] }

theorem u15319 : Upper (D 7) (R 7) [6,288,72,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15320 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 290 76 56 208 160 67 131 259), lower := (rows 7 290 76 56 208 160 64 128 256), losses := [] }

theorem u15320 : Upper (D 7) (R 7) [6,288,72,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15321 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 290 76 137 49 34 208 208 464), lower := (rows 7 290 76 137 49 34 64 128 256), losses := [] }

theorem u15321 : Upper (D 7) (R 7) [6,288,72,129,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15322 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 290 76 137 49 48 194 194 450), lower := (rows 7 290 76 137 49 48 64 128 256), losses := [] }

theorem u15322 : Upper (D 7) (R 7) [6,288,72,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15322 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15323 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 394, targets := 64 },{ cop := 4, region := 386, targets := 1 }], pairs := [(1,0),(1,6),(3,6),(4,1)], upper := (rows 7 290 76 137 49 96 210 146 402), lower := (rows 7 290 76 137 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 53 288 108 153 49 96 96 128 256) }] }

theorem u15323 : Upper (D 7) (R 7) [6,288,72,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15324 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 322, targets := 1 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 7 290 76 137 49 160 82 210 338), lower := (rows 7 290 76 137 49 160 64 128 256), losses := [] }

theorem u15324 : Upper (D 7) (R 7) [6,288,72,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15325 : PairBound 9 := { available := 176, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 7 290 76 137 81 34 240 176 432), lower := (rows 7 290 76 137 81 34 64 128 256), losses := [] }

theorem u15325 : Upper (D 7) (R 7) [6,288,72,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15326 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(1,6),(3,6)], upper := (rows 7 290 76 137 81 48 226 162 418), lower := (rows 7 290 76 137 81 48 64 128 256), losses := [] }

theorem u15326 : Upper (D 7) (R 7) [6,288,72,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15326 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15327 : Route 9 := (fun mask => (mask,id))

def c15327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15327 : Upper (D 7) (R 7) [6,288,72,129,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,65,128] 13 (by decide) (choices 1) [2,16,32] r15327 c15327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3078
  · exact u3079
  · exact u3080

def r15328 : Route 9 := (fun mask => (mask,id))

def c15328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u15328 : Upper (D 7) (R 7) [6,288,72,129,66,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,66,1] 13 (by decide) (choices 1) [16,32,128] r15328 c15328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3081
  · exact u3082
  · exact u3083

def r15329 : Route 9 := (fun mask => (mask,id))

def c15329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15329 : Upper (D 7) (R 7) [6,288,72,129,66,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,66,16] 13 (by decide) (choices 1) [1,32,128] r15329 c15329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3084
  · exact u3085
  · exact u3086

def r15330 : Route 9 := (fun mask => (mask,id))

def c15330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15330 : Upper (D 7) (R 7) [6,288,72,129,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,66,128] 13 (by decide) (choices 1) [1,16,32] r15330 c15330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3087
  · exact u3088
  · exact u3089

def b15331 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 466, targets := 1 },{ cop := 4, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(4,0)], upper := (rows 7 290 76 137 112 33 210 146 402), lower := (rows 7 290 76 137 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 12 8 50 32 115 179 307), good := (rows 470 498 76 460 498 498 64 128 256) }] }

theorem u15331 : Upper (D 7) (R 7) [6,288,72,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15332 : Route 9 := (fun mask => (mask,id))

def c15332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15332 : Upper (D 7) (R 7) [6,288,72,129,96,2] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,96,2] 13 (by decide) (choices 1) [1,16,128] r15332 c15332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3090
  · exact u3091
  · exact u3092

def b15333 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 76 137 112 48 195 131 387), lower := (rows 7 290 76 137 112 48 64 128 256), losses := [] }

theorem u15333 : Upper (D 7) (R 7) [6,288,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15333 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15334 : Route 9 := (fun mask => (mask,id))

def c15334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15334 : Upper (D 7) (R 7) [6,288,72,129,96,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,96,128] 13 (by decide) (choices 1) [1,2,16] r15334 c15334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3093
  · exact u3094
  · exact u3095

def r15335 : Route 9 := (fun mask => (mask,id))

def c15335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15335 : Upper (D 7) (R 7) [6,288,72,129,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,130,1] 13 (by decide) (choices 1) [16,32] r15335 c15335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3096
  · exact u3097

def r15336 : Route 9 := (fun mask => (mask,id))

def c15336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15336 : Upper (D 7) (R 7) [6,288,72,129,130,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,130,16] 13 (by decide) (choices 1) [1,32] r15336 c15336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3098
  · exact u3099

def r15337 : Route 9 := (fun mask => (mask,id))

def c15337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15337 : Upper (D 7) (R 7) [6,288,72,129,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,130,64] 13 (by decide) (choices 1) [1,16,32] r15337 c15337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3100
  · exact u3101
  · exact u3102

def b15338 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0),(4,0),(4,1),(4,6)], upper := (rows 7 290 76 137 176 33 82 210 338), lower := (rows 7 290 76 137 176 33 64 128 256), losses := [] }

theorem u15338 : Upper (D 7) (R 7) [6,288,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15339 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 290 76 137 176 34 81 209 337), lower := (rows 7 290 76 137 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 258 4 8 24 291 64 128 256), good := (rows 38 290 92 184 176 34 64 128 290) }] }

theorem u15339 : Upper (D 7) (R 7) [6,288,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15340 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 76 137 176 48 67 195 323), lower := (rows 7 290 76 137 176 48 64 128 256), losses := [] }

theorem u15340 : Upper (D 7) (R 7) [6,288,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15341 : Route 9 := (fun mask => (mask,id))

def c15341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15341 : Upper (D 7) (R 7) [6,288,72,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,160,64] 13 (by decide) (choices 1) [1,2,16] r15341 c15341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3103
  · exact u3104
  · exact u3105

def r15342 : Route 9 := (fun mask => (mask,id))

def c15342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15342 : Upper (D 7) (R 7) [6,288,72,129,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,192,1] 13 (by decide) (choices 1) [2,16,32] r15342 c15342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3106
  · exact u3107
  · exact u3108

def r15343 : Route 9 := (fun mask => (mask,id))

def c15343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15343 : Upper (D 7) (R 7) [6,288,72,129,192,2] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,192,2] 13 (by decide) (choices 1) [1,16,32] r15343 c15343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3109
  · exact u3110
  · exact u3111

def r15344 : Route 9 := (fun mask => (mask,id))

def c15344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15344 : Upper (D 7) (R 7) [6,288,72,129,192,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,192,16] 13 (by decide) (choices 1) [1,2,32] r15344 c15344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3112
  · exact u3113
  · exact u3114

def b15345 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 64 }], pairs := [(1,0),(2,0),(3,0),(4,6)], upper := (rows 7 290 76 138 49 33 208 208 464), lower := (rows 7 290 76 138 49 33 64 128 256), losses := [] }

theorem u15345 : Upper (D 7) (R 7) [6,288,72,130,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15346 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 76 138 49 48 193 193 449), lower := (rows 7 290 76 138 49 48 64 128 256), losses := [] }

theorem u15346 : Upper (D 7) (R 7) [6,288,72,130,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15346 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15347 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 394, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,6),(3,6),(4,1),(4,7)], upper := (rows 7 290 76 138 49 96 209 145 401), lower := (rows 7 290 76 138 49 96 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 17 100 64 0 256), good := (rows 55 290 108 10 49 96 96 0 256) }] }

theorem u15347 : Upper (D 7) (R 7) [6,288,72,130,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15348 : Route 9 := (fun mask => (mask,id))

def c15348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15348 : Upper (D 7) (R 7) [6,288,72,130,33,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,33,128] 13 (by decide) (choices 1) [1,16] r15348 c15348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3115
  · exact u3116

def b15349 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 290 76 138 81 33 240 176 432), lower := (rows 7 290 76 138 81 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 49 49 115 179 307), good := (rows 501 496 76 460 497 497 64 128 256) }] }

theorem u15349 : Upper (D 7) (R 7) [6,288,72,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15350 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,6),(3,6),(4,1)], upper := (rows 7 290 76 138 81 48 225 161 417), lower := (rows 7 290 76 138 81 48 64 128 256), losses := [] }

theorem u15350 : Upper (D 7) (R 7) [6,288,72,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15350 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15351 : Route 9 := (fun mask => (mask,id))

def c15351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15351 : Upper (D 7) (R 7) [6,288,72,130,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,65,128] 13 (by decide) (choices 1) [1,16,32] r15351 c15351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3117
  · exact u3118
  · exact u3119

def r15352 : Route 9 := (fun mask => (mask,id))

def c15352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15352 : Upper (D 7) (R 7) [6,288,72,130,96,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,96,1] 13 (by decide) (choices 1) [1,16,128] r15352 c15352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3120
  · exact u3121
  · exact u3122

def b15353 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 76 138 112 48 193 129 385), lower := (rows 7 290 76 138 112 48 64 128 256), losses := [] }

theorem u15353 : Upper (D 7) (R 7) [6,288,72,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15353 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15354 : Route 9 := (fun mask => (mask,id))

def c15354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15354 : Upper (D 7) (R 7) [6,288,72,130,96,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,96,128] 13 (by decide) (choices 1) [1,16] r15354 c15354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3123
  · exact u3124

def r15355 : Route 9 := (fun mask => (mask,id))

def c15355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15355 : Upper (D 7) (R 7) [6,288,72,130,129,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,129,1] 13 (by decide) (choices 1) [16,32] r15355 c15355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3125
  · exact u3126

def r15356 : Route 9 := (fun mask => (mask,id))

def c15356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15356 : Upper (D 7) (R 7) [6,288,72,130,129,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,129,16] 13 (by decide) (choices 1) [1,32] r15356 c15356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3127
  · exact u3128

def r15357 : Route 9 := (fun mask => (mask,id))

def c15357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15357 : Upper (D 7) (R 7) [6,288,72,130,129,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,129,64] 13 (by decide) (choices 1) [1,16,32] r15357 c15357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3129
  · exact u3130
  · exact u3131

def r15358 : Route 9 := (fun mask => (mask,id))

def c15358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15358 : Upper (D 7) (R 7) [6,288,72,130,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,160,1] 13 (by decide) (choices 1) [1,16] r15358 c15358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3132
  · exact u3133

def b15359 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 76 138 176 48 65 193 321), lower := (rows 7 290 76 138 176 48 64 128 256), losses := [] }

theorem u15359 : Upper (D 7) (R 7) [6,288,72,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15359 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15359
end Delivery.IrregularNine14.P07
