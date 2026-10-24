import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0124

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24240 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 262 73 112 33 84 148 276), lower := (rows 35 138 262 73 112 33 64 128 256), losses := [] }

theorem u24240 : Upper (D 6) (R 6) [34,136,258,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24241 : Route 9 := (fun mask => (mask,id))

def c24241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24241 : Upper (D 6) (R 6) [34,136,258,65,96,4] 13 := by
  apply FastRouting.sound _ _ [34,136,258,65,96,4] 13 (by decide) (choices 1) [1,4,16] r24241 c24241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7485
  · exact u7486
  · exact u7487

def b24242 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 262 73 112 48 69 133 261), lower := (rows 35 138 262 73 112 48 64 128 256), losses := [] }

theorem u24242 : Upper (D 6) (R 6) [34,136,258,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24242 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24243 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 138 262 76 21 33 112 240 368), lower := (rows 35 138 262 76 21 33 64 128 256), losses := [] }

theorem u24243 : Upper (D 6) (R 6) [34,136,258,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24244 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 138 262 76 21 48 97 225 353), lower := (rows 35 138 262 76 21 48 64 128 256), losses := [] }

theorem u24244 : Upper (D 6) (R 6) [34,136,258,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24244 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24245 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 35 138 262 76 21 96 113 177 305), lower := (rows 35 138 262 76 21 96 64 128 256), losses := [] }

theorem u24245 : Upper (D 6) (R 6) [34,136,258,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24246 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 138 262 76 52 33 81 209 337), lower := (rows 35 138 262 76 52 33 64 128 256), losses := [] }

theorem u24246 : Upper (D 6) (R 6) [34,136,258,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24247 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 262 76 52 48 65 193 321), lower := (rows 35 138 262 76 52 48 64 128 256), losses := [] }

theorem u24247 : Upper (D 6) (R 6) [34,136,258,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24247 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24248 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,6),(4,0),(4,6)], upper := (rows 35 138 262 76 52 96 81 145 273), lower := (rows 35 138 262 76 52 96 64 128 256), losses := [] }

theorem u24248 : Upper (D 6) (R 6) [34,136,258,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24249 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 138 262 76 81 33 116 180 308), lower := (rows 35 138 262 76 81 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 63 64 128 256), good := (rows 35 187 291 121 113 33 64 128 256) }] }

theorem u24249 : Upper (D 6) (R 6) [34,136,258,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24250 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 262 76 81 36 113 177 305), lower := (rows 35 138 262 76 81 36 64 128 256), losses := [] }

theorem u24250 : Upper (D 6) (R 6) [34,136,258,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24251 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(0,2),(2,6)], upper := (rows 35 138 262 76 81 48 101 165 293), lower := (rows 35 138 262 76 81 48 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 58 64 128 256), good := (rows 35 187 291 121 113 48 64 128 256) }] }

theorem u24251 : Upper (D 6) (R 6) [34,136,258,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24251 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24252 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 138 262 76 112 33 85 149 277), lower := (rows 35 138 262 76 112 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 47 64 128 256), good := (rows 35 187 291 121 112 33 64 128 256) }] }

theorem u24252 : Upper (D 6) (R 6) [34,136,258,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24253 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 262 76 112 36 81 145 273), lower := (rows 35 138 262 76 112 36 64 128 256), losses := [] }

theorem u24253 : Upper (D 6) (R 6) [34,136,258,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24254 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 262 76 112 48 69 133 261), lower := (rows 35 138 262 76 112 48 64 128 256), losses := [] }

theorem u24254 : Upper (D 6) (R 6) [34,136,258,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24254 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24255 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 262 88 21 33 100 228 356), lower := (rows 35 138 262 88 21 33 64 128 256), losses := [] }

theorem u24255 : Upper (D 6) (R 6) [34,136,258,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24256 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 4, region := 104, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 138 262 88 21 36 97 225 353), lower := (rows 35 138 262 88 21 36 64 128 256), losses := [] }

theorem u24256 : Upper (D 6) (R 6) [34,136,258,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24257 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 35 138 262 88 21 96 101 165 293), lower := (rows 35 138 262 88 21 96 64 128 256), losses := [] }

theorem u24257 : Upper (D 6) (R 6) [34,136,258,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24258 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 138 262 88 52 33 69 197 325), lower := (rows 35 138 262 88 52 33 64 128 256), losses := [] }

theorem u24258 : Upper (D 6) (R 6) [34,136,258,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24259 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 262 88 52 36 65 193 321), lower := (rows 35 138 262 88 52 36 64 128 256), losses := [] }

theorem u24259 : Upper (D 6) (R 6) [34,136,258,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24260 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 0, region := 260, targets := 32 }], pairs := [(2,5),(2,6),(4,6)], upper := (rows 35 138 262 88 52 96 69 133 261), lower := (rows 35 138 262 88 52 96 64 128 256), losses := [] }

theorem u24260 : Upper (D 6) (R 6) [34,136,258,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24261 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 262 104 81 33 84 148 276), lower := (rows 35 138 262 104 81 33 64 128 256), losses := [] }

theorem u24261 : Upper (D 6) (R 6) [34,136,258,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24262 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 262 104 81 36 85 149 277), lower := (rows 35 138 262 104 81 36 64 128 256), losses := [] }

theorem u24262 : Upper (D 6) (R 6) [34,136,258,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24263 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 262 104 81 48 69 133 261), lower := (rows 35 138 262 104 81 48 64 128 256), losses := [] }

theorem u24263 : Upper (D 6) (R 6) [34,136,258,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24263 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24264 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 262 104 84 33 85 149 277), lower := (rows 35 138 262 104 84 33 64 128 256), losses := [] }

theorem u24264 : Upper (D 6) (R 6) [34,136,258,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24265 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 262 104 84 36 81 145 273), lower := (rows 35 138 262 104 84 36 64 128 256), losses := [] }

theorem u24265 : Upper (D 6) (R 6) [34,136,258,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24266 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 262 104 84 48 69 133 261), lower := (rows 35 138 262 104 84 48 64 128 256), losses := [] }

theorem u24266 : Upper (D 6) (R 6) [34,136,258,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24266 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24267 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 13 22 33 96 224 352), lower := (rows 35 138 276 13 22 33 64 128 256), losses := [] }

theorem u24267 : Upper (D 6) (R 6) [34,136,272,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24268 : Route 9 := (fun mask => (mask,id))

def c24268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24268 : Upper (D 6) (R 6) [34,136,272,5,6,64] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,6,64] 13 (by decide) (choices 1) [1,32] r24268 c24268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7488
  · exact u7489

def b24269 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 13 81 34 100 228 356), lower := (rows 35 138 276 13 81 34 64 128 256), losses := [] }

theorem u24269 : Upper (D 6) (R 6) [34,136,272,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24270 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 35 138 276 13 81 36 98 226 354), lower := (rows 35 138 276 13 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 60 75 139 267), good := (rows 482 490 308 494 500 36 64 128 256) }] }

theorem u24270 : Upper (D 6) (R 6) [34,136,272,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24271 : Route 9 := (fun mask => (mask,id))

def c24271 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24271 : Upper (D 6) (R 6) [34,136,272,5,65,64] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,65,64] 13 (by decide) (choices 1) [2,4,32] r24271 c24271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7490
  · exact u7491
  · exact u7492

def b24272 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 13 82 33 100 228 356), lower := (rows 35 138 276 13 82 33 64 128 256), losses := [] }

theorem u24272 : Upper (D 6) (R 6) [34,136,272,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24273 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 35 138 276 13 82 36 97 225 353), lower := (rows 35 138 276 13 82 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 154 272 475 82 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 171 308 45 19 36 0 128 256) }] }

theorem u24273 : Upper (D 6) (R 6) [34,136,272,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24274 : Route 9 := (fun mask => (mask,id))

def c24274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24274 : Upper (D 6) (R 6) [34,136,272,5,66,64] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,66,64] 13 (by decide) (choices 1) [1,4,32] r24274 c24274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7493
  · exact u7494
  · exact u7495

def b24275 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 13 84 33 98 226 354), lower := (rows 35 138 276 13 84 33 64 128 256), losses := [] }

theorem u24275 : Upper (D 6) (R 6) [34,136,272,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24276 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 13 84 34 97 225 353), lower := (rows 35 138 276 13 84 34 64 128 256), losses := [] }

theorem u24276 : Upper (D 6) (R 6) [34,136,272,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24277 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(1,6)], upper := (rows 35 138 276 13 84 96 99 163 291), lower := (rows 35 138 276 13 84 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 32 0 129 257), good := (rows 419 138 276 399 20 32 0 128 256) }] }

theorem u24277 : Upper (D 6) (R 6) [34,136,272,5,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24278 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 13 112 33 70 198 326), lower := (rows 35 138 276 13 112 33 64 128 256), losses := [] }

theorem u24278 : Upper (D 6) (R 6) [34,136,272,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24279 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 13 112 34 69 197 325), lower := (rows 35 138 276 13 112 34 64 128 256), losses := [] }

theorem u24279 : Upper (D 6) (R 6) [34,136,272,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24280 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 194, targets := 36 },{ cop := 0, region := 80, targets := 4 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 276 13 112 36 67 195 323), lower := (rows 35 138 276 13 112 36 64 128 256), losses := [] }

theorem u24280 : Upper (D 6) (R 6) [34,136,272,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24281 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 276 13 112 96 71 135 263), lower := (rows 35 138 276 13 112 96 64 128 256), losses := [] }

theorem u24281 : Upper (D 6) (R 6) [34,136,272,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24282 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 14 81 33 100 228 356), lower := (rows 35 138 276 14 81 33 64 128 256), losses := [] }

theorem u24282 : Upper (D 6) (R 6) [34,136,272,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24283 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 276 14 81 36 97 225 353), lower := (rows 35 138 276 14 81 36 64 128 256), losses := [] }

theorem u24283 : Upper (D 6) (R 6) [34,136,272,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24284 : Route 9 := (fun mask => (mask,id))

def c24284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24284 : Upper (D 6) (R 6) [34,136,272,6,65,64] 13 := by
  apply FastRouting.sound _ _ [34,136,272,6,65,64] 13 (by decide) (choices 1) [1,4,32] r24284 c24284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7496
  · exact u7497
  · exact u7498

def b24285 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 14 112 33 69 197 325), lower := (rows 35 138 276 14 112 33 64 128 256), losses := [] }

theorem u24285 : Upper (D 6) (R 6) [34,136,272,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24286 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 276 14 112 36 65 193 321), lower := (rows 35 138 276 14 112 36 64 128 256), losses := [] }

theorem u24286 : Upper (D 6) (R 6) [34,136,272,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24287 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 276 14 112 96 69 133 261), lower := (rows 35 138 276 14 112 96 64 128 256), losses := [] }

theorem u24287 : Upper (D 6) (R 6) [34,136,272,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24288 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 44 81 33 70 198 326), lower := (rows 35 138 276 44 81 33 64 128 256), losses := [] }

theorem u24288 : Upper (D 6) (R 6) [34,136,272,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24289 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 44 81 34 69 197 325), lower := (rows 35 138 276 44 81 34 64 128 256), losses := [] }

theorem u24289 : Upper (D 6) (R 6) [34,136,272,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24290 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 276 44 81 36 67 195 323), lower := (rows 35 138 276 44 81 36 64 128 256), losses := [] }

theorem u24290 : Upper (D 6) (R 6) [34,136,272,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24291 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 276 44 81 96 71 135 263), lower := (rows 35 138 276 44 81 96 64 128 256), losses := [] }

theorem u24291 : Upper (D 6) (R 6) [34,136,272,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24292 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 44 82 33 69 197 325), lower := (rows 35 138 276 44 82 33 64 128 256), losses := [] }

theorem u24292 : Upper (D 6) (R 6) [34,136,272,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24293 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 276 44 82 36 65 193 321), lower := (rows 35 138 276 44 82 36 64 128 256), losses := [] }

theorem u24293 : Upper (D 6) (R 6) [34,136,272,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24294 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 276 44 82 96 69 133 261), lower := (rows 35 138 276 44 82 96 64 128 256), losses := [] }

theorem u24294 : Upper (D 6) (R 6) [34,136,272,36,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24295 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 73 21 34 100 228 356), lower := (rows 35 138 276 73 21 34 64 128 256), losses := [] }

theorem u24295 : Upper (D 6) (R 6) [34,136,272,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24296 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 73 21 36 98 226 354), lower := (rows 35 138 276 73 21 36 64 128 256), losses := [] }

theorem u24296 : Upper (D 6) (R 6) [34,136,272,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24297 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 276 73 21 96 102 166 294), lower := (rows 35 138 276 73 21 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 272 105 17 96 96 128 256) }] }

theorem u24297 : Upper (D 6) (R 6) [34,136,272,65,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24298 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 73 22 33 100 228 356), lower := (rows 35 138 276 73 22 33 64 128 256), losses := [] }

theorem u24298 : Upper (D 6) (R 6) [34,136,272,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24299 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 73 22 36 97 225 353), lower := (rows 35 138 276 73 22 36 64 128 256), losses := [] }

theorem u24299 : Upper (D 6) (R 6) [34,136,272,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24299
end Delivery.IrregularNine14.P06
