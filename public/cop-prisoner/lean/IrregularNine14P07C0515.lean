import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0218
import IrregularNine14P07C0219
import IrregularNine14P07C0220

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30900 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(3,5),(4,1),(4,6)], upper := (rows 7 42 84 74 49 417 449 385 385), lower := (rows 7 42 84 74 49 32 64 128 256), losses := [] }

theorem u30900 : Upper (D 7) (R 7) [6,40,80,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30901 : Route 9 := (fun mask => (mask,id))

def c30901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30901 : Upper (D 7) (R 7) [6,40,80,66,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,66,129] 13 (by decide) (choices 1) [1,128,256] r30901 c30901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13128
  · exact u13129
  · exact u13130

def b30902 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(3,5),(4,1),(4,6)], upper := (rows 7 42 84 74 176 417 449 385 385), lower := (rows 7 42 84 74 176 32 64 128 256), losses := [] }

theorem u30902 : Upper (D 7) (R 7) [6,40,80,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30903 : Route 9 := (fun mask => (mask,id))

def c30903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30903 : Upper (D 7) (R 7) [6,40,80,66,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,66,257] 13 (by decide) (choices 1) [1,128] r30903 c30903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13131
  · exact u13132

def b30904 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(3,5),(4,1),(4,6)], upper := (rows 7 42 84 74 304 161 193 129 385), lower := (rows 7 42 84 74 304 32 64 128 256), losses := [] }

theorem u30904 : Upper (D 7) (R 7) [6,40,80,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30905 : Route 9 := (fun mask => (mask,id))

def c30905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30905 : Upper (D 7) (R 7) [6,40,80,66,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,66,384] 13 (by decide) (choices 1) [1,128] r30905 c30905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13133
  · exact u13134

def b30906 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 84 137 19 480 480 480 480), lower := (rows 7 42 84 137 19 32 64 128 256), losses := [] }

theorem u30906 : Upper (D 7) (R 7) [6,40,80,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30907 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(3,5)], upper := (rows 7 42 84 137 49 482 450 450 450), lower := (rows 7 42 84 137 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 84 490 500 32 64 128 256) },{ target := 5, region := (rows 1 2 20 25 16 0 67 131 259), good := (rows 463 458 92 457 477 0 64 128 256) }] }

theorem u30907 : Upper (D 7) (R 7) [6,40,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30908 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 84 137 50 481 449 449 449), lower := (rows 7 42 84 137 50 32 64 128 256), losses := [] }

theorem u30908 : Upper (D 7) (R 7) [6,40,80,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30909 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 137 81 418 482 418 418), lower := (rows 7 42 84 137 81 32 64 128 256), losses := [] }

theorem u30909 : Upper (D 7) (R 7) [6,40,80,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30910 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 137 82 417 481 417 417), lower := (rows 7 42 84 137 82 32 64 128 256), losses := [] }

theorem u30910 : Upper (D 7) (R 7) [6,40,80,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30911 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 137 112 419 451 387 387), lower := (rows 7 42 84 137 112 32 64 128 256), losses := [] }

theorem u30911 : Upper (D 7) (R 7) [6,40,80,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30912 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 42 84 137 145 354 354 482 354), lower := (rows 7 42 84 137 145 32 64 128 256), losses := [] }

theorem u30912 : Upper (D 7) (R 7) [6,40,80,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30913 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 488, targets := 2 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 7 42 84 137 146 353 353 481 353), lower := (rows 7 42 84 137 146 32 64 128 256), losses := [] }

theorem u30913 : Upper (D 7) (R 7) [6,40,80,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30914 : Route 9 := (fun mask => (mask,id))

def c30914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30914 : Upper (D 7) (R 7) [6,40,80,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160] 13 (by decide) (choices 1) [1,2,64,256] r30914 c30914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13135
  · exact u13136
  · exact u13137
  · exact u13138

def b30915 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 137 208 291 355 419 291), lower := (rows 7 42 84 137 208 32 64 128 256), losses := [] }

theorem u30915 : Upper (D 7) (R 7) [6,40,80,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30916 : Route 9 := (fun mask => (mask,id))

def c30916 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30916 : Upper (D 7) (R 7) [6,40,80,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257] 13 (by decide) (choices 1) [2,64,128] r30916 c30916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13139
  · exact u13140
  · exact u13141

def r30917 : Route 9 := (fun mask => (mask,id))

def c30917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30917 : Upper (D 7) (R 7) [6,40,80,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,258] 13 (by decide) (choices 1) [1,64,128] r30917 c30917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13142
  · exact u13143
  · exact u13144

def r30918 : Route 9 := (fun mask => (mask,id))

def c30918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30918 : Upper (D 7) (R 7) [6,40,80,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288] 13 (by decide) (choices 1) [1,2,64,128] r30918 c30918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13145
  · exact u13146
  · exact u13147
  · exact u13148

def b30919 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 137 336 163 227 163 419), lower := (rows 7 42 84 137 336 32 64 128 256), losses := [] }

theorem u30919 : Upper (D 7) (R 7) [6,40,80,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30920 : Route 9 := (fun mask => (mask,id))

def c30920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30920 : Upper (D 7) (R 7) [6,40,80,129,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,384] 13 (by decide) (choices 1) [1,2,64] r30920 c30920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13149
  · exact u13150
  · exact u13151

def b30921 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 456, targets := 32 },{ cop := 4, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,5),(4,1)], upper := (rows 7 42 84 138 49 481 449 449 449), lower := (rows 7 42 84 138 49 32 64 128 256), losses := [] }

theorem u30921 : Upper (D 7) (R 7) [6,40,80,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30922 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 42 84 138 81 417 481 417 417), lower := (rows 7 42 84 138 81 32 64 128 256), losses := [] }

theorem u30922 : Upper (D 7) (R 7) [6,40,80,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30923 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 138 112 417 449 385 385), lower := (rows 7 42 84 138 112 32 64 128 256), losses := [] }

theorem u30923 : Upper (D 7) (R 7) [6,40,80,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30924 : Route 9 := (fun mask => (mask,id))

def c30924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30924 : Upper (D 7) (R 7) [6,40,80,130,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,129] 13 (by decide) (choices 1) [1,64,256] r30924 c30924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13152
  · exact u13153
  · exact u13154

def b30925 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 138 176 353 321 449 321), lower := (rows 7 42 84 138 176 32 64 128 256), losses := [] }

theorem u30925 : Upper (D 7) (R 7) [6,40,80,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30926 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 138 208 289 353 417 289), lower := (rows 7 42 84 138 208 32 64 128 256), losses := [] }

theorem u30926 : Upper (D 7) (R 7) [6,40,80,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30927 : Route 9 := (fun mask => (mask,id))

def c30927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30927 : Upper (D 7) (R 7) [6,40,80,130,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,257] 13 (by decide) (choices 1) [1,64,128] r30927 c30927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13155
  · exact u13156
  · exact u13157

def r30928 : Route 9 := (fun mask => (mask,id))

def c30928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30928 : Upper (D 7) (R 7) [6,40,80,130,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,288] 13 (by decide) (choices 1) [1,64,128] r30928 c30928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13158
  · exact u13159
  · exact u13160

def b30929 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 138 336 161 225 161 417), lower := (rows 7 42 84 138 336 32 64 128 256), losses := [] }

theorem u30929 : Upper (D 7) (R 7) [6,40,80,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30930 : Route 9 := (fun mask => (mask,id))

def c30930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30930 : Upper (D 7) (R 7) [6,40,80,130,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,384] 13 (by decide) (choices 1) [1,64] r30930 c30930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13161
  · exact u13162

def b30931 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 84 200 19 417 481 417 417), lower := (rows 7 42 84 200 19 32 64 128 256), losses := [] }

theorem u30931 : Upper (D 7) (R 7) [6,40,80,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30932 : Route 9 := (fun mask => (mask,id))

def c30932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30932 : Upper (D 7) (R 7) [6,40,80,192,33] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,33] 13 (by decide) (choices 1) [1,2,128,256] r30932 c30932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13163
  · exact u13164
  · exact u13165
  · exact u13166

def b30933 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 84 200 50 417 449 385 385), lower := (rows 7 42 84 200 50 32 64 128 256), losses := [] }

theorem u30933 : Upper (D 7) (R 7) [6,40,80,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30934 : Route 9 := (fun mask => (mask,id))

def c30934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30934 : Upper (D 7) (R 7) [6,40,80,192,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,129] 13 (by decide) (choices 1) [1,2,256] r30934 c30934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13167
  · exact u13168
  · exact u13169

def b30935 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 488, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,7),(2,7),(3,1),(4,6)], upper := (rows 7 42 84 200 146 289 353 417 289), lower := (rows 7 42 84 200 146 32 64 128 256), losses := [] }

theorem u30935 : Upper (D 7) (R 7) [6,40,80,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30936 : Route 9 := (fun mask => (mask,id))

def c30936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30936 : Upper (D 7) (R 7) [6,40,80,192,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,160] 13 (by decide) (choices 1) [1,2,256] r30936 c30936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13170
  · exact u13171
  · exact u13172

def r30937 : Route 9 := (fun mask => (mask,id))

def c30937 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30937 : Upper (D 7) (R 7) [6,40,80,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,257] 13 (by decide) (choices 1) [1,2,128] r30937 c30937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13173
  · exact u13174
  · exact u13175

def r30938 : Route 9 := (fun mask => (mask,id))

def c30938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30938 : Upper (D 7) (R 7) [6,40,80,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,258] 13 (by decide) (choices 1) [1,128] r30938 c30938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13176
  · exact u13177

def r30939 : Route 9 := (fun mask => (mask,id))

def c30939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30939 : Upper (D 7) (R 7) [6,40,80,192,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,288] 13 (by decide) (choices 1) [1,2,128] r30939 c30939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13178
  · exact u13179
  · exact u13180

def r30940 : Route 9 := (fun mask => (mask,id))

def c30940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30940 : Upper (D 7) (R 7) [6,40,80,192,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384] 13 (by decide) (choices 1) [1,2] r30940 c30940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13181
  · exact u13182

def b30941 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 42 84 265 19 224 224 224 480), lower := (rows 7 42 84 265 19 32 64 128 256), losses := [] }

theorem u30941 : Upper (D 7) (R 7) [6,40,80,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30942 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(3,5)], upper := (rows 7 42 84 265 49 226 194 194 450), lower := (rows 7 42 84 265 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 84 490 500 32 64 128 256) },{ target := 5, region := (rows 1 2 20 25 16 0 67 131 259), good := (rows 463 458 92 457 477 0 64 128 256) }] }

theorem u30942 : Upper (D 7) (R 7) [6,40,80,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30943 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 84 265 50 225 193 193 449), lower := (rows 7 42 84 265 50 32 64 128 256), losses := [] }

theorem u30943 : Upper (D 7) (R 7) [6,40,80,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30944 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 265 81 162 226 162 418), lower := (rows 7 42 84 265 81 32 64 128 256), losses := [] }

theorem u30944 : Upper (D 7) (R 7) [6,40,80,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30945 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 265 82 161 225 161 417), lower := (rows 7 42 84 265 82 32 64 128 256), losses := [] }

theorem u30945 : Upper (D 7) (R 7) [6,40,80,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30946 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 265 112 163 195 131 387), lower := (rows 7 42 84 265 112 32 64 128 256), losses := [] }

theorem u30946 : Upper (D 7) (R 7) [6,40,80,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30947 : Route 9 := (fun mask => (mask,id))

def c30947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30947 : Upper (D 7) (R 7) [6,40,80,257,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,129] 13 (by decide) (choices 1) [2,64,128] r30947 c30947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13183
  · exact u13184
  · exact u13185

def r30948 : Route 9 := (fun mask => (mask,id))

def c30948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30948 : Upper (D 7) (R 7) [6,40,80,257,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,130] 13 (by decide) (choices 1) [1,64,128] r30948 c30948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13186
  · exact u13187
  · exact u13188

def r30949 : Route 9 := (fun mask => (mask,id))

def c30949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30949 : Upper (D 7) (R 7) [6,40,80,257,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,160] 13 (by decide) (choices 1) [1,2,64,128] r30949 c30949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13189
  · exact u13190
  · exact u13191
  · exact u13192

def b30950 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 265 208 163 227 163 419), lower := (rows 7 42 84 265 208 32 64 128 256), losses := [] }

theorem u30950 : Upper (D 7) (R 7) [6,40,80,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30951 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 456, targets := 32 },{ cop := 4, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,5),(4,1)], upper := (rows 7 42 84 266 49 225 193 193 449), lower := (rows 7 42 84 266 49 32 64 128 256), losses := [] }

theorem u30951 : Upper (D 7) (R 7) [6,40,80,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30952 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 4, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 42 84 266 81 161 225 161 417), lower := (rows 7 42 84 266 81 32 64 128 256), losses := [] }

theorem u30952 : Upper (D 7) (R 7) [6,40,80,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30953 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 266 112 161 193 129 385), lower := (rows 7 42 84 266 112 32 64 128 256), losses := [] }

theorem u30953 : Upper (D 7) (R 7) [6,40,80,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30954 : Route 9 := (fun mask => (mask,id))

def c30954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30954 : Upper (D 7) (R 7) [6,40,80,258,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,258,129] 13 (by decide) (choices 1) [1,64,128] r30954 c30954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13193
  · exact u13194
  · exact u13195

def r30955 : Route 9 := (fun mask => (mask,id))

def c30955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30955 : Upper (D 7) (R 7) [6,40,80,258,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,258,160] 13 (by decide) (choices 1) [1,64,128] r30955 c30955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13196
  · exact u13197
  · exact u13198

def b30956 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 84 266 208 161 225 161 417), lower := (rows 7 42 84 266 208 32 64 128 256), losses := [] }

theorem u30956 : Upper (D 7) (R 7) [6,40,80,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30957 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 84 328 19 161 225 161 417), lower := (rows 7 42 84 328 19 32 64 128 256), losses := [] }

theorem u30957 : Upper (D 7) (R 7) [6,40,80,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30958 : Route 9 := (fun mask => (mask,id))

def c30958 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30958 : Upper (D 7) (R 7) [6,40,80,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320,33] 13 (by decide) (choices 1) [1,2,128] r30958 c30958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13199
  · exact u13200
  · exact u13201

def b30959 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 84 328 50 161 193 129 385), lower := (rows 7 42 84 328 50 32 64 128 256), losses := [] }

theorem u30959 : Upper (D 7) (R 7) [6,40,80,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u30959
end Delivery.IrregularNine14.P07
