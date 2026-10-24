import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0037
import IrregularNine14P07C0038

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14100 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 152 280 96 99 163 291), lower := (rows 7 98 133 152 280 96 64 128 256), losses := [] }

theorem u14100 : Upper (D 7) (R 7) [6,96,129,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14101 : Route 9 := (fun mask => (mask,id))

def c14101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14101 : Upper (D 7) (R 7) [6,96,129,144,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,288,1] 13 (by decide) (choices 1) [2,8] r14101 c14101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2261
  · exact u2262

def r14102 : Route 9 := (fun mask => (mask,id))

def c14102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14102 : Upper (D 7) (R 7) [6,96,129,144,288,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,288,2] 13 (by decide) (choices 1) [1,8] r14102 c14102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2263
  · exact u2264

def r14103 : Route 9 := (fun mask => (mask,id))

def c14103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14103 : Upper (D 7) (R 7) [6,96,129,144,288,8] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,288,8] 13 (by decide) (choices 1) [1,2] r14103 c14103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2265
  · exact u2266

def b14104 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 152 304 96 75 139 267), lower := (rows 7 98 133 152 304 96 64 128 256), losses := [] }

theorem u14104 : Upper (D 7) (R 7) [6,96,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14105 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(3,6)], upper := (rows 7 98 133 168 273 34 88 216 344), lower := (rows 7 98 133 168 273 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 16 35 0 128 256), good := (rows 47 34 173 168 305 34 0 128 256) }] }

theorem u14105 : Upper (D 7) (R 7) [6,96,129,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14106 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 168 273 40 82 210 338), lower := (rows 7 98 133 168 273 40 64 128 256), losses := [] }

theorem u14106 : Upper (D 7) (R 7) [6,96,129,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14106 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14107 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 133 168 273 48 74 202 330), lower := (rows 7 98 133 168 273 48 64 128 256), losses := [] }

theorem u14107 : Upper (D 7) (R 7) [6,96,129,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14107 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14108 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 168 273 96 90 154 282), lower := (rows 7 98 133 168 273 96 64 128 256), losses := [] }

theorem u14108 : Upper (D 7) (R 7) [6,96,129,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14109 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 168 274 33 88 216 344), lower := (rows 7 98 133 168 274 33 64 128 256), losses := [] }

theorem u14109 : Upper (D 7) (R 7) [6,96,129,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14110 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 168 274 40 81 209 337), lower := (rows 7 98 133 168 274 40 64 128 256), losses := [] }

theorem u14110 : Upper (D 7) (R 7) [6,96,129,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14110 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14111 : Route 9 := (fun mask => (mask,id))

def c14111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14111 : Upper (D 7) (R 7) [6,96,129,160,258,16] 13 := by
  apply FastRouting.sound _ _ [6,96,129,160,258,16] 13 (by decide) (choices 1) [1,8] r14111 c14111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2267
  · exact u2268

def b14112 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 168 274 96 89 153 281), lower := (rows 7 98 133 168 274 96 64 128 256), losses := [] }

theorem u14112 : Upper (D 7) (R 7) [6,96,129,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14113 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 168 280 33 82 210 338), lower := (rows 7 98 133 168 280 33 64 128 256), losses := [] }

theorem u14113 : Upper (D 7) (R 7) [6,96,129,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14114 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,6)], upper := (rows 7 98 133 168 280 34 81 209 337), lower := (rows 7 98 133 168 280 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 4 12 16 99 64 128 256), good := (rows 46 98 172 168 280 34 98 128 256) },{ target := 6, region := (rows 1 2 4 12 16 35 0 128 256), good := (rows 47 34 173 168 280 34 0 128 256) }] }

theorem u14114 : Upper (D 7) (R 7) [6,96,129,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14115 : Route 9 := (fun mask => (mask,id))

def c14115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14115 : Upper (D 7) (R 7) [6,96,129,160,264,16] 13 := by
  apply FastRouting.sound _ _ [6,96,129,160,264,16] 13 (by decide) (choices 1) [1,2] r14115 c14115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2269
  · exact u2270

def b14116 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 168 280 96 83 147 275), lower := (rows 7 98 133 168 280 96 64 128 256), losses := [] }

theorem u14116 : Upper (D 7) (R 7) [6,96,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14117 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 168 336 33 90 154 282), lower := (rows 7 98 133 168 336 33 64 128 256), losses := [] }

theorem u14117 : Upper (D 7) (R 7) [6,96,129,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14118 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,6)], upper := (rows 7 98 133 168 336 34 89 153 281), lower := (rows 7 98 133 168 336 34 64 128 256), losses := [{ target := 0, region := (rows 0 82 4 12 16 115 64 128 256), good := (rows 46 98 172 168 370 34 98 128 256) },{ target := 6, region := (rows 1 2 4 12 16 35 0 128 256), good := (rows 47 34 173 168 272 34 0 128 256) }] }

theorem u14118 : Upper (D 7) (R 7) [6,96,129,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14119 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 168 336 40 83 147 275), lower := (rows 7 98 133 168 336 40 64 128 256), losses := [] }

theorem u14119 : Upper (D 7) (R 7) [6,96,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14119 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14120 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 168 336 48 75 139 267), lower := (rows 7 98 133 168 336 48 64 128 256), losses := [] }

theorem u14120 : Upper (D 7) (R 7) [6,96,129,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14120 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14121 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 7 98 140 25 176 33 322 450 322), lower := (rows 7 98 140 25 176 33 64 128 256), losses := [] }

theorem u14121 : Upper (D 7) (R 7) [6,96,136,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14122 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 452, targets := 34 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 7 98 140 25 176 34 321 449 321), lower := (rows 7 98 140 25 176 34 64 128 256), losses := [] }

theorem u14122 : Upper (D 7) (R 7) [6,96,136,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14123 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 25 176 96 323 387 259), lower := (rows 7 98 140 25 176 96 64 128 256), losses := [] }

theorem u14123 : Upper (D 7) (R 7) [6,96,136,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14124 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,5)], upper := (rows 7 98 140 25 176 288 67 195 323), lower := (rows 7 98 140 25 176 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 65 129 257), good := (rows 455 66 140 477 144 256 64 128 256) }] }

theorem u14124 : Upper (D 7) (R 7) [6,96,136,17,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14124 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14125 : Route 9 := (fun mask => (mask,id))

def c14125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14125 : Upper (D 7) (R 7) [6,96,136,17,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,258,1] 13 (by decide) (choices 1) [32,128] r14125 c14125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2271
  · exact u2272

def b14126 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 25 274 96 225 161 417), lower := (rows 7 98 140 25 274 96 64 128 256), losses := [] }

theorem u14126 : Upper (D 7) (R 7) [6,96,136,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14127_1 : Upper (D 7) (R 7) [6,96,136,17,258,128,1] 13 :=
  permutation_upper _ _ _ [6,96,136,17,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2272

theorem m14127_32 : Upper (D 7) (R 7) [6,96,136,17,258,128,32] 13 :=
  permutation_upper _ _ _ [6,96,136,17,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2273

def r14127 : Route 9 := (fun mask => (mask,id))

def c14127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14127 : Upper (D 7) (R 7) [6,96,136,17,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,258,128] 13 (by decide) (choices 1) [1,32] r14127 c14127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14127_1
  · exact m14127_32

def b14128 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(4,0)], upper := (rows 7 98 140 25 304 33 194 194 450), lower := (rows 7 98 140 25 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 12 8 50 32 123 187 315), good := (rows 470 498 460 478 498 498 64 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 67 131 259), good := (rows 455 450 140 477 272 449 64 128 256) }] }

theorem u14128 : Upper (D 7) (R 7) [6,96,136,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14129 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 7 98 140 25 304 34 193 193 449), lower := (rows 7 98 140 25 304 34 64 128 256), losses := [] }

theorem u14129 : Upper (D 7) (R 7) [6,96,136,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14130 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 25 304 96 195 131 387), lower := (rows 7 98 140 25 304 96 64 128 256), losses := [] }

theorem u14130 : Upper (D 7) (R 7) [6,96,136,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14131 : Route 9 := (fun mask => (mask,id))

def c14131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14131 : Upper (D 7) (R 7) [6,96,136,17,288,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,288,128] 13 (by decide) (choices 1) [1,2] r14131 c14131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2274
  · exact u2275

def b14132 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 7 98 140 25 400 33 98 226 354), lower := (rows 7 98 140 25 400 33 64 128 256), losses := [] }

theorem u14132 : Upper (D 7) (R 7) [6,96,136,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14133_1 : Upper (D 7) (R 7) [6,96,136,17,384,2,1] 13 :=
  permutation_upper _ _ _ [6,96,136,17,384,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2276

def r14133 : Route 9 := (fun mask => (mask,id))

def c14133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14133 : Upper (D 7) (R 7) [6,96,136,17,384,2] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,384,2] 13 (by decide) (choices 1) [1,32] r14133 c14133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14133_1
  · exact u2277

def b14134 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 25 400 96 99 163 291), lower := (rows 7 98 140 25 400 96 64 128 256), losses := [] }

theorem u14134 : Upper (D 7) (R 7) [6,96,136,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14135 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(4,1)], upper := (rows 7 98 140 26 273 33 224 224 480), lower := (rows 7 98 140 26 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 16 32 98 162 290), good := (rows 454 482 140 478 272 482 64 128 256) },{ target := 1, region := (rows 1 0 12 8 49 49 123 187 315), good := (rows 501 496 460 508 497 497 64 128 256) }] }

theorem u14135 : Upper (D 7) (R 7) [6,96,136,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14136 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 26 273 96 225 161 417), lower := (rows 7 98 140 26 273 96 64 128 256), losses := [] }

theorem u14136 : Upper (D 7) (R 7) [6,96,136,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14137_1 : Upper (D 7) (R 7) [6,96,136,18,257,128,1] 13 :=
  permutation_upper _ _ _ [6,96,136,18,257,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2278

theorem m14137_32 : Upper (D 7) (R 7) [6,96,136,18,257,128,32] 13 :=
  permutation_upper _ _ _ [6,96,136,18,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2279

def r14137 : Route 9 := (fun mask => (mask,id))

def c14137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14137 : Upper (D 7) (R 7) [6,96,136,18,257,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,257,128] 13 (by decide) (choices 1) [1,32] r14137 c14137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14137_1
  · exact m14137_32

def r14138 : Route 9 := (fun mask => (mask,id))

def c14138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14138 : Upper (D 7) (R 7) [6,96,136,18,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,288,1] 13 (by decide) (choices 1) [1,128] r14138 c14138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2280
  · exact u2281

def b14139 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 26 304 96 193 129 385), lower := (rows 7 98 140 26 304 96 64 128 256), losses := [] }

theorem u14139 : Upper (D 7) (R 7) [6,96,136,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14140 : Route 9 := (fun mask => (mask,id))

def c14140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14140 : Upper (D 7) (R 7) [6,96,136,18,288,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,288,128] 13 (by decide) (choices 1) [1] r14140 c14140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u2282

def r14141 : Route 9 := (fun mask => (mask,id))

def c14141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14141 : Upper (D 7) (R 7) [6,96,136,18,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,384,1] 13 (by decide) (choices 1) [1,32] r14141 c14141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2283
  · exact u2284

def b14142 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 26 400 96 97 161 289), lower := (rows 7 98 140 26 400 96 64 128 256), losses := [] }

theorem u14142 : Upper (D 7) (R 7) [6,96,136,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14143 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 140 41 81 34 464 400 400), lower := (rows 7 98 140 41 81 34 64 128 256), losses := [] }

theorem u14143 : Upper (D 7) (R 7) [6,96,136,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14144 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 41 81 48 450 386 386), lower := (rows 7 98 140 41 81 48 64 128 256), losses := [] }

theorem u14144 : Upper (D 7) (R 7) [6,96,136,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14144 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14145 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 128 },{ cop := 0, region := 336, targets := 32 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(1,7),(4,5),(4,7)], upper := (rows 7 98 140 41 81 160 338 402 274), lower := (rows 7 98 140 41 81 160 64 128 256), losses := [] }

theorem u14145 : Upper (D 7) (R 7) [6,96,136,33,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14146 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 7 98 140 41 81 288 210 146 402), lower := (rows 7 98 140 41 81 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 66 156 477 465 256 64 128 256) }] }

theorem u14146 : Upper (D 7) (R 7) [6,96,136,33,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14146 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14147 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 140 41 146 33 336 464 336), lower := (rows 7 98 140 41 146 33 64 128 256), losses := [] }

theorem u14147 : Upper (D 7) (R 7) [6,96,136,33,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14148 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 41 146 48 321 449 321), lower := (rows 7 98 140 41 146 48 64 128 256), losses := [] }

theorem u14148 : Upper (D 7) (R 7) [6,96,136,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14148 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14149 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 41 146 96 337 401 273), lower := (rows 7 98 140 41 146 96 64 128 256), losses := [] }

theorem u14149 : Upper (D 7) (R 7) [6,96,136,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14150 : Route 9 := (fun mask => (mask,id))

def c14150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14150 : Upper (D 7) (R 7) [6,96,136,33,130,256] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,130,256] 13 (by decide) (choices 1) [1,16] r14150 c14150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2285
  · exact u2286

def b14151 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 140 41 208 33 338 402 274), lower := (rows 7 98 140 41 208 33 64 128 256), losses := [] }

theorem u14151 : Upper (D 7) (R 7) [6,96,136,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14152 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 140 41 208 34 337 401 273), lower := (rows 7 98 140 41 208 34 64 128 256), losses := [] }

theorem u14152 : Upper (D 7) (R 7) [6,96,136,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14153 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 41 208 48 323 387 259), lower := (rows 7 98 140 41 208 48 64 128 256), losses := [] }

theorem u14153 : Upper (D 7) (R 7) [6,96,136,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14153 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14154 : Route 9 := (fun mask => (mask,id))

def c14154 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14154 : Upper (D 7) (R 7) [6,96,136,33,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,192,256] 13 (by decide) (choices 1) [1,2,16] r14154 c14154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2287
  · exact u2288
  · exact u2289

def b14155 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 140 41 273 34 208 208 464), lower := (rows 7 98 140 41 273 34 64 128 256), losses := [] }

theorem u14155 : Upper (D 7) (R 7) [6,96,136,33,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14156 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 140 41 273 48 194 194 450), lower := (rows 7 98 140 41 273 48 64 128 256), losses := [] }

theorem u14156 : Upper (D 7) (R 7) [6,96,136,33,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14156 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14157 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 41 273 96 210 146 402), lower := (rows 7 98 140 41 273 96 64 128 256), losses := [] }

theorem u14157 : Upper (D 7) (R 7) [6,96,136,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14158 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 128 },{ cop := 0, region := 336, targets := 32 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(1,7),(4,5),(4,7)], upper := (rows 7 98 140 41 273 160 82 210 338), lower := (rows 7 98 140 41 273 160 64 128 256), losses := [] }

theorem u14158 : Upper (D 7) (R 7) [6,96,136,33,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14159 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 140 41 274 33 208 208 464), lower := (rows 7 98 140 41 274 33 64 128 256), losses := [] }

theorem u14159 : Upper (D 7) (R 7) [6,96,136,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14159
end Delivery.IrregularNine14.P07
