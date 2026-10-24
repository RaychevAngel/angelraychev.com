import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0067
import IrregularNine14P08C0068

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12300 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 290 44 137 145 116 116 244 372), lower := (rows 67 290 44 137 145 32 64 128 256), losses := [] }

theorem u12300 : Upper (D 8) (R 8) [66,288,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12301 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 137 148 113 113 241 369), lower := (rows 67 290 44 137 148 32 64 128 256), losses := [] }

theorem u12301 : Upper (D 8) (R 8) [66,288,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12302 : Route 9 := (fun mask => (mask,id))

def c12302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12302 : Upper (D 8) (R 8) [66,288,40,129,160] 13 := by
  apply FastRouting.sound _ _ [66,288,40,129,160] 13 (by decide) (choices 1) [1,4,16,64] r12302 c12302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4059
  · exact u4060
  · exact u4061
  · exact u4062

def r12303 : Route 9 := (fun mask => (mask,id))

def c12303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12303 : Upper (D 8) (R 8) [66,288,40,129,192] 13 := by
  apply FastRouting.sound _ _ [66,288,40,129,192] 13 (by decide) (choices 1) [1,4,16] r12303 c12303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4063
  · exact u4064
  · exact u4065

def b12304 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 140 81 177 241 177 433), lower := (rows 67 290 44 140 81 32 64 128 256), losses := [] }

theorem u12304 : Upper (D 8) (R 8) [66,288,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12305 : Route 9 := (fun mask => (mask,id))

def c12305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12305 : Upper (D 8) (R 8) [66,288,40,132,96] 13 := by
  apply FastRouting.sound _ _ [66,288,40,132,96] 13 (by decide) (choices 1) [1,16,128] r12305 c12305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4066
  · exact u4067
  · exact u4068

def b12306 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 140 145 113 113 241 369), lower := (rows 67 290 44 140 145 32 64 128 256), losses := [] }

theorem u12306 : Upper (D 8) (R 8) [66,288,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12307 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 140 176 113 81 209 337), lower := (rows 67 290 44 140 176 32 64 128 256), losses := [] }

theorem u12307 : Upper (D 8) (R 8) [66,288,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12308 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 140 208 49 113 177 305), lower := (rows 67 290 44 140 208 32 64 128 256), losses := [] }

theorem u12308 : Upper (D 8) (R 8) [66,288,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12309 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 152 81 165 229 165 421), lower := (rows 67 290 44 152 81 32 64 128 256), losses := [] }

theorem u12309 : Upper (D 8) (R 8) [66,288,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12310 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 44 152 84 161 225 161 417), lower := (rows 67 290 44 152 84 32 64 128 256), losses := [] }

theorem u12310 : Upper (D 8) (R 8) [66,288,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12311 : Route 9 := (fun mask => (mask,id))

def c12311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12311 : Upper (D 8) (R 8) [66,288,40,144,96] 13 := by
  apply FastRouting.sound _ _ [66,288,40,144,96] 13 (by decide) (choices 1) [1,4,128] r12311 c12311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4069
  · exact u4070
  · exact u4071

def b12312 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 152 145 101 101 229 357), lower := (rows 67 290 44 152 145 32 64 128 256), losses := [] }

theorem u12312 : Upper (D 8) (R 8) [66,288,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12313 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 152 148 97 97 225 353), lower := (rows 67 290 44 152 148 32 64 128 256), losses := [] }

theorem u12313 : Upper (D 8) (R 8) [66,288,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12314 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 152 176 101 69 197 325), lower := (rows 67 290 44 152 176 32 64 128 256), losses := [] }

theorem u12314 : Upper (D 8) (R 8) [66,288,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12315 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 152 208 37 101 165 293), lower := (rows 67 290 44 152 208 32 64 128 256), losses := [] }

theorem u12315 : Upper (D 8) (R 8) [66,288,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12316 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 168 84 177 209 145 401), lower := (rows 67 290 44 168 84 32 64 128 256), losses := [] }

theorem u12316 : Upper (D 8) (R 8) [66,288,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12317 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 168 145 117 85 213 341), lower := (rows 67 290 44 168 145 32 64 128 256), losses := [] }

theorem u12317 : Upper (D 8) (R 8) [66,288,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12318 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 168 148 113 81 209 337), lower := (rows 67 290 44 168 148 32 64 128 256), losses := [] }

theorem u12318 : Upper (D 8) (R 8) [66,288,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12319 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 290 44 168 208 53 85 149 277), lower := (rows 67 290 44 168 208 32 64 128 256), losses := [] }

theorem u12319 : Upper (D 8) (R 8) [66,288,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12320 : Route 9 := (fun mask => (mask,id))

def c12320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12320 : Upper (D 8) (R 8) [66,288,40,192,129] 13 := by
  apply FastRouting.sound _ _ [66,288,40,192,129] 13 (by decide) (choices 1) [1,4,16] r12320 c12320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4072
  · exact u4073
  · exact u4074

def b12321 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 200 148 49 113 177 305), lower := (rows 67 290 44 200 148 32 64 128 256), losses := [] }

theorem u12321 : Upper (D 8) (R 8) [66,288,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12322 : Route 9 := (fun mask => (mask,id))

def c12322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12322 : Upper (D 8) (R 8) [66,288,40,192,160] 13 := by
  apply FastRouting.sound _ _ [66,288,40,192,160] 13 (by decide) (choices 1) [1,4,16] r12322 c12322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4075
  · exact u4076
  · exact u4077

def b12323 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 69 137 148 56 120 184 312), lower := (rows 67 290 69 137 148 32 64 128 256), losses := [] }

theorem u12323 : Upper (D 8) (R 8) [66,288,65,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12324 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 69 137 176 60 124 188 316), lower := (rows 67 290 69 137 176 32 64 128 256), losses := [] }

theorem u12324 : Upper (D 8) (R 8) [66,288,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12325 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 69 140 176 57 121 185 313), lower := (rows 67 290 69 140 176 32 64 128 256), losses := [] }

theorem u12325 : Upper (D 8) (R 8) [66,288,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12326 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 290 76 137 145 52 116 180 308), lower := (rows 67 290 76 137 145 32 64 128 256), losses := [] }

theorem u12326 : Upper (D 8) (R 8) [66,288,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12327 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 76 137 148 49 113 177 305), lower := (rows 67 290 76 137 148 32 64 128 256), losses := [] }

theorem u12327 : Upper (D 8) (R 8) [66,288,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12328 : Route 9 := (fun mask => (mask,id))

def c12328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12328 : Upper (D 8) (R 8) [66,288,72,129,160] 13 := by
  apply FastRouting.sound _ _ [66,288,72,129,160] 13 (by decide) (choices 1) [1,4,16] r12328 c12328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4078
  · exact u4079
  · exact u4080

def b12329 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 76 140 145 49 113 177 305), lower := (rows 67 290 76 140 145 32 64 128 256), losses := [] }

theorem u12329 : Upper (D 8) (R 8) [66,288,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12330 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 76 140 176 49 113 177 305), lower := (rows 67 290 76 140 176 32 64 128 256), losses := [] }

theorem u12330 : Upper (D 8) (R 8) [66,288,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12331 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 76 152 145 37 101 165 293), lower := (rows 67 290 76 152 145 32 64 128 256), losses := [] }

theorem u12331 : Upper (D 8) (R 8) [66,288,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12332 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 76 152 148 33 97 161 289), lower := (rows 67 290 76 152 148 32 64 128 256), losses := [] }

theorem u12332 : Upper (D 8) (R 8) [66,288,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12333 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 76 152 176 37 101 165 293), lower := (rows 67 290 76 152 176 32 64 128 256), losses := [] }

theorem u12333 : Upper (D 8) (R 8) [66,288,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12334 : Route 9 := (fun mask => (mask,id))

def c12334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12334 : Upper (D 8) (R 8) [66,288,72,160,129] 13 := by
  apply FastRouting.sound _ _ [66,288,72,160,129] 13 (by decide) (choices 1) [1,4,16] r12334 c12334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4081
  · exact u4082
  · exact u4083

def b12335 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 76 168 148 49 113 177 305), lower := (rows 67 290 76 168 148 32 64 128 256), losses := [] }

theorem u12335 : Upper (D 8) (R 8) [66,288,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12336 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 290 76 168 176 53 85 149 277), lower := (rows 67 290 76 168 176 32 64 128 256), losses := [] }

theorem u12336 : Upper (D 8) (R 8) [66,288,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12337 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 290 100 137 145 60 124 188 316), lower := (rows 67 290 100 137 145 32 64 128 256), losses := [] }

theorem u12337 : Upper (D 8) (R 8) [66,288,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12338 : Route 9 := (fun mask => (mask,id))

def c12338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12338 : Upper (D 8) (R 8) [66,288,96,129,132] 13 := by
  apply FastRouting.sound _ _ [66,288,96,129,132] 13 (by decide) (choices 1) [1,8,16] r12338 c12338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4084
  · exact u4085
  · exact u4086

def b12339 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 290 100 137 152 53 117 181 309), lower := (rows 67 290 100 137 152 32 64 128 256), losses := [] }

theorem u12339 : Upper (D 8) (R 8) [66,288,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12340 : Route 9 := (fun mask => (mask,id))

def c12340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12340 : Upper (D 8) (R 8) [66,288,96,129,160] 13 := by
  apply FastRouting.sound _ _ [66,288,96,129,160] 13 (by decide) (choices 1) [1,4,8,16] r12340 c12340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4087
  · exact u4088
  · exact u4089
  · exact u4090

def b12341 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 290 100 140 152 49 113 177 305), lower := (rows 67 290 100 140 152 32 64 128 256), losses := [] }

theorem u12341 : Upper (D 8) (R 8) [66,288,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12342 : Route 9 := (fun mask => (mask,id))

def c12342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12342 : Upper (D 8) (R 8) [66,288,96,132,160] 13 := by
  apply FastRouting.sound _ _ [66,288,96,132,160] 13 (by decide) (choices 1) [1,8,16] r12342 c12342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4091
  · exact u4092
  · exact u4093

def b12343 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 100 152 152 37 101 165 293), lower := (rows 67 290 100 152 152 32 64 128 256), losses := [] }

theorem u12343 : Upper (D 8) (R 8) [66,288,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12344 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 100 152 176 45 77 141 269), lower := (rows 67 290 100 152 176 32 64 128 256), losses := [] }

theorem u12344 : Upper (D 8) (R 8) [66,288,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12345 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 13 112 176 240 176 432), lower := (rows 67 386 13 13 112 32 64 128 256), losses := [] }

theorem u12345 : Upper (D 8) (R 8) [66,384,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12346 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 13 176 112 112 240 368), lower := (rows 67 386 13 13 176 32 64 128 256), losses := [] }

theorem u12346 : Upper (D 8) (R 8) [66,384,9,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12347 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 13 208 48 112 176 304), lower := (rows 67 386 13 13 208 32 64 128 256), losses := [] }

theorem u12347 : Upper (D 8) (R 8) [66,384,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12348 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 25 52 224 224 224 480), lower := (rows 67 386 13 25 52 32 64 128 256), losses := [] }

theorem u12348 : Upper (D 8) (R 8) [66,384,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12349 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 25 84 160 224 160 416), lower := (rows 67 386 13 25 84 32 64 128 256), losses := [] }

theorem u12349 : Upper (D 8) (R 8) [66,384,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12350 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 25 112 164 228 164 420), lower := (rows 67 386 13 25 112 32 64 128 256), losses := [] }

theorem u12350 : Upper (D 8) (R 8) [66,384,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12351 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 25 148 96 96 224 352), lower := (rows 67 386 13 25 148 32 64 128 256), losses := [] }

theorem u12351 : Upper (D 8) (R 8) [66,384,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12352 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 25 176 100 100 228 356), lower := (rows 67 386 13 25 176 32 64 128 256), losses := [] }

theorem u12352 : Upper (D 8) (R 8) [66,384,9,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12353 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 25 208 36 100 164 292), lower := (rows 67 386 13 25 208 32 64 128 256), losses := [] }

theorem u12353 : Upper (D 8) (R 8) [66,384,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12354 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 28 49 224 224 224 480), lower := (rows 67 386 13 28 49 32 64 128 256), losses := [] }

theorem u12354 : Upper (D 8) (R 8) [66,384,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12355 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 28 81 160 224 160 416), lower := (rows 67 386 13 28 81 32 64 128 256), losses := [] }

theorem u12355 : Upper (D 8) (R 8) [66,384,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12356 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 28 112 161 225 161 417), lower := (rows 67 386 13 28 112 32 64 128 256), losses := [] }

theorem u12356 : Upper (D 8) (R 8) [66,384,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12357 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 28 145 96 96 224 352), lower := (rows 67 386 13 28 145 32 64 128 256), losses := [] }

theorem u12357 : Upper (D 8) (R 8) [66,384,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12358 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 13 28 176 97 97 225 353), lower := (rows 67 386 13 28 176 32 64 128 256), losses := [] }

theorem u12358 : Upper (D 8) (R 8) [66,384,9,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12359 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 28 208 33 97 161 289), lower := (rows 67 386 13 28 208 32 64 128 256), losses := [] }

theorem u12359 : Upper (D 8) (R 8) [66,384,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12359
end Delivery.IrregularNine14.P08
