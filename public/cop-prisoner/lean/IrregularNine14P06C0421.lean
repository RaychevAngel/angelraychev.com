import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0130

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25260 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 386 70 25 52 36 73 201 329), lower := (rows 35 386 70 25 52 36 64 128 256), losses := [] }

theorem u25260 : Upper (D 6) (R 6) [34,384,66,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25261 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 386 70 25 52 40 69 197 325), lower := (rows 35 386 70 25 52 40 64 128 256), losses := [] }

theorem u25261 : Upper (D 6) (R 6) [34,384,66,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25261 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25262 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 70 25 52 96 77 141 269), lower := (rows 35 386 70 25 52 96 64 128 256), losses := [] }

theorem u25262 : Upper (D 6) (R 6) [34,384,66,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25263 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 386 70 25 88 33 100 164 292), lower := (rows 35 386 70 25 88 33 64 128 256), losses := [] }

theorem u25263 : Upper (D 6) (R 6) [34,384,66,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25264 : Route 9 := (fun mask => (mask,id))

def c25264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25264 : Upper (D 6) (R 6) [34,384,66,17,72,4] 13 := by
  apply FastRouting.sound _ _ [34,384,66,17,72,4] 13 (by decide) (choices 1) [1,4,32] r25264 c25264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7826
  · exact u7827
  · exact u7828

def b25265 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 386 70 25 112 33 76 140 268), lower := (rows 35 386 70 25 112 33 64 128 256), losses := [] }

theorem u25265 : Upper (D 6) (R 6) [34,384,66,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25266 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 386 70 25 112 36 77 141 269), lower := (rows 35 386 70 25 112 36 64 128 256), losses := [] }

theorem u25266 : Upper (D 6) (R 6) [34,384,66,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25267 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 386 70 25 112 40 69 133 261), lower := (rows 35 386 70 25 112 40 64 128 256), losses := [] }

theorem u25267 : Upper (D 6) (R 6) [34,384,66,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25267 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25268 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 386 70 44 81 33 92 156 284), lower := (rows 35 386 70 44 81 33 64 128 256), losses := [] }

theorem u25268 : Upper (D 6) (R 6) [34,384,66,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25269 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 386 70 44 81 36 89 153 281), lower := (rows 35 386 70 44 81 36 64 128 256), losses := [] }

theorem u25269 : Upper (D 6) (R 6) [34,384,66,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25270 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 70 44 81 40 85 149 277), lower := (rows 35 386 70 44 81 40 64 128 256), losses := [] }

theorem u25270 : Upper (D 6) (R 6) [34,384,66,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25270 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25271 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 386 70 44 81 48 77 141 269), lower := (rows 35 386 70 44 81 48 64 128 256), losses := [] }

theorem u25271 : Upper (D 6) (R 6) [34,384,66,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25271 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25272 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 386 70 44 88 33 85 149 277), lower := (rows 35 386 70 44 88 33 64 128 256), losses := [] }

theorem u25272 : Upper (D 6) (R 6) [34,384,66,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25273 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 386 70 44 88 36 81 145 273), lower := (rows 35 386 70 44 88 36 64 128 256), losses := [] }

theorem u25273 : Upper (D 6) (R 6) [34,384,66,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25274 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 386 70 44 88 48 69 133 261), lower := (rows 35 386 70 44 88 48 64 128 256), losses := [] }

theorem u25274 : Upper (D 6) (R 6) [34,384,66,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25274 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25275 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 76 13 22 33 112 240 368), lower := (rows 35 386 76 13 22 33 64 128 256), losses := [] }

theorem u25275 : Upper (D 6) (R 6) [34,384,72,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25276 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 76 13 22 48 97 225 353), lower := (rows 35 386 76 13 22 48 64 128 256), losses := [] }

theorem u25276 : Upper (D 6) (R 6) [34,384,72,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25276 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25277 : Route 9 := (fun mask => (mask,id))

def c25277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25277 : Upper (D 6) (R 6) [34,384,72,5,6,64] 13 := by
  apply FastRouting.sound _ _ [34,384,72,5,6,64] 13 (by decide) (choices 1) [1,16,32] r25277 c25277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7829
  · exact u7830
  · exact u7831

def b25278 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 48, targets := 2 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 386 76 13 52 33 82 210 338), lower := (rows 35 386 76 13 52 33 64 128 256), losses := [] }

theorem u25278 : Upper (D 6) (R 6) [34,384,72,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25279 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 76 13 52 34 81 209 337), lower := (rows 35 386 76 13 52 34 64 128 256), losses := [] }

theorem u25279 : Upper (D 6) (R 6) [34,384,72,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25280 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 76 13 52 48 67 195 323), lower := (rows 35 386 76 13 52 48 64 128 256), losses := [] }

theorem u25280 : Upper (D 6) (R 6) [34,384,72,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25280 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25281 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 76 13 52 96 83 147 275), lower := (rows 35 386 76 13 52 96 64 128 256), losses := [] }

theorem u25281 : Upper (D 6) (R 6) [34,384,72,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25282 : Route 9 := (fun mask => (mask,id))

def c25282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25282 : Upper (D 6) (R 6) [34,384,72,5,66,1] 13 := by
  apply FastRouting.sound _ _ [34,384,72,5,66,1] 13 (by decide) (choices 1) [4,16,32] r25282 c25282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7832
  · exact u7833
  · exact u7834

def b25283 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 386 76 13 82 36 113 177 305), lower := (rows 35 386 76 13 82 36 64 128 256), losses := [] }

theorem u25283 : Upper (D 6) (R 6) [34,384,72,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25284 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 76 13 82 48 101 165 293), lower := (rows 35 386 76 13 82 48 64 128 256), losses := [] }

theorem u25284 : Upper (D 6) (R 6) [34,384,72,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25284 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25285 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 386 76 13 112 33 86 150 278), lower := (rows 35 386 76 13 112 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 41 64 128 256), good := (rows 33 384 124 61 112 33 64 128 256) }] }

theorem u25285 : Upper (D 6) (R 6) [34,384,72,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25286 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 76 13 112 34 85 149 277), lower := (rows 35 386 76 13 112 34 64 128 256), losses := [] }

theorem u25286 : Upper (D 6) (R 6) [34,384,72,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25287 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 386 76 13 112 36 83 147 275), lower := (rows 35 386 76 13 112 36 64 128 256), losses := [] }

theorem u25287 : Upper (D 6) (R 6) [34,384,72,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25288 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 76 13 112 48 71 135 263), lower := (rows 35 386 76 13 112 48 64 128 256), losses := [] }

theorem u25288 : Upper (D 6) (R 6) [34,384,72,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25288 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25289 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 386 76 14 21 33 112 240 368), lower := (rows 35 386 76 14 21 33 64 128 256), losses := [] }

theorem u25289 : Upper (D 6) (R 6) [34,384,72,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25290 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 386 76 14 21 48 97 225 353), lower := (rows 35 386 76 14 21 48 64 128 256), losses := [] }

theorem u25290 : Upper (D 6) (R 6) [34,384,72,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25290 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25291 : Route 9 := (fun mask => (mask,id))

def c25291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25291 : Upper (D 6) (R 6) [34,384,72,6,5,64] 13 := by
  apply FastRouting.sound _ _ [34,384,72,6,5,64] 13 (by decide) (choices 1) [1,16,32] r25291 c25291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7835
  · exact u7836
  · exact u7837

def b25292 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 386 76 14 52 33 81 209 337), lower := (rows 35 386 76 14 52 33 64 128 256), losses := [] }

theorem u25292 : Upper (D 6) (R 6) [34,384,72,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25293 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 76 14 52 48 65 193 321), lower := (rows 35 386 76 14 52 48 64 128 256), losses := [] }

theorem u25293 : Upper (D 6) (R 6) [34,384,72,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25293 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25294 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 76 14 52 96 81 145 273), lower := (rows 35 386 76 14 52 96 64 128 256), losses := [] }

theorem u25294 : Upper (D 6) (R 6) [34,384,72,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25295 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 386 76 14 81 33 116 180 308), lower := (rows 35 386 76 14 81 33 64 128 256), losses := [{ target := 2, region := (rows 11 2 0 8 20 63 64 128 256), good := (rows 35 419 121 59 113 33 64 128 256) }] }

theorem u25295 : Upper (D 6) (R 6) [34,384,72,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25296 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 386 76 14 81 36 113 177 305), lower := (rows 35 386 76 14 81 36 64 128 256), losses := [] }

theorem u25296 : Upper (D 6) (R 6) [34,384,72,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25297 : PairBound 9 := { available := 37, camps := [], pairs := [(0,2),(4,2)], upper := (rows 35 386 76 14 81 48 101 165 293), lower := (rows 35 386 76 14 81 48 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 20 60 64 128 256), good := (rows 35 386 121 59 113 48 64 128 256) }] }

theorem u25297 : Upper (D 6) (R 6) [34,384,72,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25297 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25298 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 386 76 14 112 33 85 149 277), lower := (rows 35 386 76 14 112 33 64 128 256), losses := [{ target := 2, region := (rows 11 2 0 8 20 47 64 128 256), good := (rows 35 419 121 59 112 33 64 128 256) }] }

theorem u25298 : Upper (D 6) (R 6) [34,384,72,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25299 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 386 76 14 112 36 81 145 273), lower := (rows 35 386 76 14 112 36 64 128 256), losses := [] }

theorem u25299 : Upper (D 6) (R 6) [34,384,72,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25300 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 76 14 112 48 69 133 261), lower := (rows 35 386 76 14 112 48 64 128 256), losses := [] }

theorem u25300 : Upper (D 6) (R 6) [34,384,72,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25300 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25301 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 386 76 25 22 33 100 228 356), lower := (rows 35 386 76 25 22 33 64 128 256), losses := [] }

theorem u25301 : Upper (D 6) (R 6) [34,384,72,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25302 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 5, region := 451, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 386 76 25 22 36 97 225 353), lower := (rows 35 386 76 25 22 36 64 128 256), losses := [] }

theorem u25302 : Upper (D 6) (R 6) [34,384,72,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25303 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 100, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 386 76 25 22 96 101 165 293), lower := (rows 35 386 76 25 22 96 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 100 64 128 256), good := (rows 35 386 104 25 59 96 96 128 256) }] }

theorem u25303 : Upper (D 6) (R 6) [34,384,72,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25304 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 386 76 25 52 33 70 198 326), lower := (rows 35 386 76 25 52 33 64 128 256), losses := [] }

theorem u25304 : Upper (D 6) (R 6) [34,384,72,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25305 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 76 25 52 34 69 197 325), lower := (rows 35 386 76 25 52 34 64 128 256), losses := [] }

theorem u25305 : Upper (D 6) (R 6) [34,384,72,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25306 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 386 76 25 52 36 67 195 323), lower := (rows 35 386 76 25 52 36 64 128 256), losses := [] }

theorem u25306 : Upper (D 6) (R 6) [34,384,72,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25307 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 76 25 52 96 71 135 263), lower := (rows 35 386 76 25 52 96 64 128 256), losses := [] }

theorem u25307 : Upper (D 6) (R 6) [34,384,72,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25308 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 386 76 26 21 33 100 228 356), lower := (rows 35 386 76 26 21 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 88 152 280), good := (rows 33 384 460 508 501 33 64 128 256) }] }

theorem u25308 : Upper (D 6) (R 6) [34,384,72,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25309 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 451, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 386 76 26 21 36 97 225 353), lower := (rows 35 386 76 26 21 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 60 81 145 273), good := (rows 481 384 108 508 501 36 64 128 256) }] }

theorem u25309 : Upper (D 6) (R 6) [34,384,72,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25310 : Route 9 := (fun mask => (mask,id))

def c25310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25310 : Upper (D 6) (R 6) [34,384,72,18,5,64] 13 := by
  apply FastRouting.sound _ _ [34,384,72,18,5,64] 13 (by decide) (choices 1) [1,4,32] r25310 c25310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7838
  · exact u7839
  · exact u7840

def b25311 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 386 76 26 52 33 69 197 325), lower := (rows 35 386 76 26 52 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 128 256), good := (rows 35 419 61 59 52 33 0 128 256) }] }

theorem u25311 : Upper (D 6) (R 6) [34,384,72,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25312 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 386 76 26 52 36 65 193 321), lower := (rows 35 386 76 26 52 36 64 128 256), losses := [] }

theorem u25312 : Upper (D 6) (R 6) [34,384,72,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25313 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 76 26 52 96 69 133 261), lower := (rows 35 386 76 26 52 96 64 128 256), losses := [] }

theorem u25313 : Upper (D 6) (R 6) [34,384,72,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25314 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 386 76 26 81 33 100 164 292), lower := (rows 35 386 76 26 81 33 64 128 256), losses := [] }

theorem u25314 : Upper (D 6) (R 6) [34,384,72,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25315 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 76 26 81 36 101 165 293), lower := (rows 35 386 76 26 81 36 64 128 256), losses := [{ target := 6, region := (rows 37 39 4 24 16 36 0 164 292), good := (rows 419 386 431 26 27 423 0 128 256) }] }

theorem u25315 : Upper (D 6) (R 6) [34,384,72,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25316 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 386 76 26 112 33 69 133 261), lower := (rows 35 386 76 26 112 33 64 128 256), losses := [] }

theorem u25316 : Upper (D 6) (R 6) [34,384,72,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25317 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 386 76 26 112 36 69 133 261), lower := (rows 35 386 76 26 112 36 64 128 256), losses := [] }

theorem u25317 : Upper (D 6) (R 6) [34,384,72,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25318 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 76 44 22 33 81 209 337), lower := (rows 35 386 76 44 22 33 64 128 256), losses := [] }

theorem u25318 : Upper (D 6) (R 6) [34,384,72,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25319 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 76 44 22 48 65 193 321), lower := (rows 35 386 76 44 22 48 64 128 256), losses := [] }

theorem u25319 : Upper (D 6) (R 6) [34,384,72,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25319 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25319
end Delivery.IrregularNine14.P06
