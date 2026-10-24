import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0122
import IrregularNine14P06C0123

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24000 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 138 100 73 21 288 86 150 278), lower := (rows 35 138 100 73 21 288 64 128 256), losses := [] }

theorem u24000 : Upper (D 6) (R 6) [34,136,96,65,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24000 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24001 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 73 22 33 340 404 276), lower := (rows 35 138 100 73 22 33 64 128 256), losses := [] }

theorem u24001 : Upper (D 6) (R 6) [34,136,96,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24002 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 100 73 22 36 337 401 273), lower := (rows 35 138 100 73 22 36 64 128 256), losses := [] }

theorem u24002 : Upper (D 6) (R 6) [34,136,96,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24003 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 100 73 22 48 325 389 261), lower := (rows 35 138 100 73 22 48 64 128 256), losses := [] }

theorem u24003 : Upper (D 6) (R 6) [34,136,96,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24003 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24004 : Route 9 := (fun mask => (mask,id))

def c24004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24004 : Upper (D 6) (R 6) [34,136,96,65,6,256] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,6,256] 13 (by decide) (choices 1) [1,4,16] r24004 c24004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7377
  · exact u7378
  · exact u7379

def b24005 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 73 273 34 84 148 276), lower := (rows 35 138 100 73 273 34 64 128 256), losses := [] }

theorem u24005 : Upper (D 6) (R 6) [34,136,96,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24006 : Route 9 := (fun mask => (mask,id))

def c24006 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24006 : Upper (D 6) (R 6) [34,136,96,65,257,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,257,4] 13 (by decide) (choices 1) [2,4,16] r24006 c24006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7380
  · exact u7381
  · exact u7382

def b24007 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 138 100 73 273 48 70 134 262), lower := (rows 35 138 100 73 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 21 8 16 48 73 137 265), good := (rows 486 458 100 462 500 52 64 128 256) }] }

theorem u24007 : Upper (D 6) (R 6) [34,136,96,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24007 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24008 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 73 274 33 84 148 276), lower := (rows 35 138 100 73 274 33 64 128 256), losses := [] }

theorem u24008 : Upper (D 6) (R 6) [34,136,96,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24009 : Route 9 := (fun mask => (mask,id))

def c24009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24009 : Upper (D 6) (R 6) [34,136,96,65,258,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,258,4] 13 (by decide) (choices 1) [1,4,16] r24009 c24009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7383
  · exact u7384
  · exact u7385

def b24010 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 100 73 274 48 69 133 261), lower := (rows 35 138 100 73 274 48 64 128 256), losses := [] }

theorem u24010 : Upper (D 6) (R 6) [34,136,96,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24010 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24011 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 73 276 33 86 150 278), lower := (rows 35 138 100 73 276 33 64 128 256), losses := [] }

theorem u24011 : Upper (D 6) (R 6) [34,136,96,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24012 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 73 276 34 85 149 277), lower := (rows 35 138 100 73 276 34 64 128 256), losses := [] }

theorem u24012 : Upper (D 6) (R 6) [34,136,96,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24013 : Route 9 := (fun mask => (mask,id))

def c24013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24013 : Upper (D 6) (R 6) [34,136,96,65,260,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,260,4] 13 (by decide) (choices 1) [1,2,16] r24013 c24013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7386
  · exact u7387
  · exact u7388

def r24014 : Route 9 := (fun mask => (mask,id))

def c24014 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24014 : Upper (D 6) (R 6) [34,136,96,65,260,16] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,260,16] 13 (by decide) (choices 1) [1,2,4] r24014 c24014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7389
  · exact u7390
  · exact u7391

def b24015 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 74 273 33 84 148 276), lower := (rows 35 138 100 74 273 33 64 128 256), losses := [] }

theorem u24015 : Upper (D 6) (R 6) [34,136,96,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24016 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 100 74 273 36 85 149 277), lower := (rows 35 138 100 74 273 36 64 128 256), losses := [] }

theorem u24016 : Upper (D 6) (R 6) [34,136,96,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24017 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 100 74 273 48 69 133 261), lower := (rows 35 138 100 74 273 48 64 128 256), losses := [] }

theorem u24017 : Upper (D 6) (R 6) [34,136,96,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24017 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24018 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 74 276 33 85 149 277), lower := (rows 35 138 100 74 276 33 64 128 256), losses := [] }

theorem u24018 : Upper (D 6) (R 6) [34,136,96,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24019 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 100 74 276 36 81 145 273), lower := (rows 35 138 100 74 276 36 64 128 256), losses := [] }

theorem u24019 : Upper (D 6) (R 6) [34,136,96,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24020 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 100 74 276 48 69 133 261), lower := (rows 35 138 100 74 276 48 64 128 256), losses := [] }

theorem u24020 : Upper (D 6) (R 6) [34,136,96,66,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24020 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24021 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 88 21 33 326 390 262), lower := (rows 35 138 100 88 21 33 64 128 256), losses := [] }

theorem u24021 : Upper (D 6) (R 6) [34,136,96,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24022 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 88 21 34 325 389 261), lower := (rows 35 138 100 88 21 34 64 128 256), losses := [] }

theorem u24022 : Upper (D 6) (R 6) [34,136,96,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24023 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 100 88 21 36 323 387 259), lower := (rows 35 138 100 88 21 36 64 128 256), losses := [] }

theorem u24023 : Upper (D 6) (R 6) [34,136,96,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24024 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 138 100 88 21 288 71 135 263), lower := (rows 35 138 100 88 21 288 64 128 256), losses := [] }

theorem u24024 : Upper (D 6) (R 6) [34,136,96,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24024 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24025 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 100 88 273 33 70 134 262), lower := (rows 35 138 100 88 273 33 64 128 256), losses := [] }

theorem u24025 : Upper (D 6) (R 6) [34,136,96,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24026 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 88 273 34 69 133 261), lower := (rows 35 138 100 88 273 34 64 128 256), losses := [] }

theorem u24026 : Upper (D 6) (R 6) [34,136,96,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24027 : Route 9 := (fun mask => (mask,id))

def c24027 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24027 : Upper (D 6) (R 6) [34,136,96,80,257,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,257,4] 13 (by decide) (choices 1) [1,2,4] r24027 c24027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7392
  · exact u7393
  · exact u7394

def b24028 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 100 88 274 33 69 133 261), lower := (rows 35 138 100 88 274 33 64 128 256), losses := [] }

theorem u24028 : Upper (D 6) (R 6) [34,136,96,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24029 : Route 9 := (fun mask => (mask,id))

def c24029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24029 : Upper (D 6) (R 6) [34,136,96,80,258,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,258,4] 13 (by decide) (choices 1) [1,4] r24029 c24029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7395
  · exact u7396

def r24030 : Route 9 := (fun mask => (mask,id))

def c24030 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24030 : Upper (D 6) (R 6) [34,136,96,80,260,1] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,260,1] 13 (by decide) (choices 1) [1,2,4] r24030 c24030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7397
  · exact u7398
  · exact u7399

def b24031 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 88 276 34 69 133 261), lower := (rows 35 138 100 88 276 34 64 128 256), losses := [] }

theorem u24031 : Upper (D 6) (R 6) [34,136,96,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24032 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 100 88 276 36 67 131 259), lower := (rows 35 138 100 88 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 10 4 8 16 52 0 139 267), good := (rows 419 395 36 443 308 36 0 128 256) }] }

theorem u24032 : Upper (D 6) (R 6) [34,136,96,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24033 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 265 21 34 84 212 340), lower := (rows 35 138 100 265 21 34 64 128 256), losses := [] }

theorem u24033 : Upper (D 6) (R 6) [34,136,96,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24034 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 100 265 21 36 82 210 338), lower := (rows 35 138 100 265 21 36 64 128 256), losses := [] }

theorem u24034 : Upper (D 6) (R 6) [34,136,96,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24035 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 138 100 265 21 48 70 198 326), lower := (rows 35 138 100 265 21 48 64 128 256), losses := [] }

theorem u24035 : Upper (D 6) (R 6) [34,136,96,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24035 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24036 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 265 21 96 86 150 278), lower := (rows 35 138 100 265 21 96 64 128 256), losses := [] }

theorem u24036 : Upper (D 6) (R 6) [34,136,96,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24037 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 265 22 33 84 212 340), lower := (rows 35 138 100 265 22 33 64 128 256), losses := [] }

theorem u24037 : Upper (D 6) (R 6) [34,136,96,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24038 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 100 265 22 36 81 209 337), lower := (rows 35 138 100 265 22 36 64 128 256), losses := [] }

theorem u24038 : Upper (D 6) (R 6) [34,136,96,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24039 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 100 265 22 48 69 197 325), lower := (rows 35 138 100 265 22 48 64 128 256), losses := [] }

theorem u24039 : Upper (D 6) (R 6) [34,136,96,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24039 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24040 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 265 22 96 85 149 277), lower := (rows 35 138 100 265 22 96 64 128 256), losses := [] }

theorem u24040 : Upper (D 6) (R 6) [34,136,96,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24041 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 265 81 34 84 148 276), lower := (rows 35 138 100 265 81 34 64 128 256), losses := [] }

theorem u24041 : Upper (D 6) (R 6) [34,136,96,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24042 : Route 9 := (fun mask => (mask,id))

def c24042 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24042 : Upper (D 6) (R 6) [34,136,96,257,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,257,65,4] 13 (by decide) (choices 1) [2,4,16] r24042 c24042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7400
  · exact u7401
  · exact u7402

def b24043 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 265 81 48 70 134 262), lower := (rows 35 138 100 265 81 48 64 128 256), losses := [] }

theorem u24043 : Upper (D 6) (R 6) [34,136,96,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24043 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24044 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 265 82 33 84 148 276), lower := (rows 35 138 100 265 82 33 64 128 256), losses := [] }

theorem u24044 : Upper (D 6) (R 6) [34,136,96,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24045 : Route 9 := (fun mask => (mask,id))

def c24045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24045 : Upper (D 6) (R 6) [34,136,96,257,66,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,257,66,4] 13 (by decide) (choices 1) [1,4,16] r24045 c24045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7403
  · exact u7404
  · exact u7405

def b24046 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 265 82 48 69 133 261), lower := (rows 35 138 100 265 82 48 64 128 256), losses := [] }

theorem u24046 : Upper (D 6) (R 6) [34,136,96,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24046 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24047 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 266 81 33 84 148 276), lower := (rows 35 138 100 266 81 33 64 128 256), losses := [] }

theorem u24047 : Upper (D 6) (R 6) [34,136,96,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24048 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 100 266 81 36 85 149 277), lower := (rows 35 138 100 266 81 36 64 128 256), losses := [] }

theorem u24048 : Upper (D 6) (R 6) [34,136,96,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24049 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 266 81 48 69 133 261), lower := (rows 35 138 100 266 81 48 64 128 256), losses := [] }

theorem u24049 : Upper (D 6) (R 6) [34,136,96,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24049 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24050 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 100 268 21 33 82 210 338), lower := (rows 35 138 100 268 21 33 64 128 256), losses := [] }

theorem u24050 : Upper (D 6) (R 6) [34,136,96,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24051 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 268 21 34 81 209 337), lower := (rows 35 138 100 268 21 34 64 128 256), losses := [] }

theorem u24051 : Upper (D 6) (R 6) [34,136,96,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24052 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 138 100 268 21 48 67 195 323), lower := (rows 35 138 100 268 21 48 64 128 256), losses := [] }

theorem u24052 : Upper (D 6) (R 6) [34,136,96,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24052 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24053 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 268 21 96 83 147 275), lower := (rows 35 138 100 268 21 96 64 128 256), losses := [] }

theorem u24053 : Upper (D 6) (R 6) [34,136,96,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24054 : Route 9 := (fun mask => (mask,id))

def c24054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24054 : Upper (D 6) (R 6) [34,136,96,260,6,1] 13 := by
  apply FastRouting.sound _ _ [34,136,96,260,6,1] 13 (by decide) (choices 1) [1,16] r24054 c24054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7406
  · exact u7407

def b24055 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 100 268 22 48 65 193 321), lower := (rows 35 138 100 268 22 48 64 128 256), losses := [] }

theorem u24055 : Upper (D 6) (R 6) [34,136,96,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24055 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24056 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 268 22 96 81 145 273), lower := (rows 35 138 100 268 22 96 64 128 256), losses := [] }

theorem u24056 : Upper (D 6) (R 6) [34,136,96,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24057 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 36, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 100 268 81 33 86 150 278), lower := (rows 35 138 100 268 81 33 64 128 256), losses := [] }

theorem u24057 : Upper (D 6) (R 6) [34,136,96,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24058 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 268 81 34 85 149 277), lower := (rows 35 138 100 268 81 34 64 128 256), losses := [] }

theorem u24058 : Upper (D 6) (R 6) [34,136,96,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24059 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 100 268 81 36 83 147 275), lower := (rows 35 138 100 268 81 36 64 128 256), losses := [] }

theorem u24059 : Upper (D 6) (R 6) [34,136,96,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24059
end Delivery.IrregularNine14.P06
