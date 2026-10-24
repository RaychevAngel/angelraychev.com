import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0152
import IrregularNine14P07C0153

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r25920 : Route 9 := (fun mask => (mask,id))

def c25920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25920 : Upper (D 7) (R 7) [36,257,66,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129,130,16] 13 (by decide) (choices 1) [8,32] r25920 c25920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9175
  · exact u9176

def b25921 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 137 146 96 120 184 312), lower := (rows 37 259 70 137 146 96 64 128 256), losses := [] }

theorem u25921 : Upper (D 7) (R 7) [36,257,66,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25922 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 137 176 34 88 216 344), lower := (rows 37 259 70 137 176 34 64 128 256), losses := [] }

theorem u25922 : Upper (D 7) (R 7) [36,257,66,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25923 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 259 70 137 176 40 82 210 338), lower := (rows 37 259 70 137 176 40 64 128 256), losses := [] }

theorem u25923 : Upper (D 7) (R 7) [36,257,66,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25923 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25924 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 70 137 176 48 74 202 330), lower := (rows 37 259 70 137 176 48 64 128 256), losses := [] }

theorem u25924 : Upper (D 7) (R 7) [36,257,66,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25924 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25925 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 137 176 96 90 154 282), lower := (rows 37 259 70 137 176 96 64 128 256), losses := [] }

theorem u25925 : Upper (D 7) (R 7) [36,257,66,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25926 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 137 208 34 120 184 312), lower := (rows 37 259 70 137 208 34 64 128 256), losses := [] }

theorem u25926 : Upper (D 7) (R 7) [36,257,66,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25927 : Route 9 := (fun mask => (mask,id))

def c25927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25927 : Upper (D 7) (R 7) [36,257,66,129,192,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129,192,8] 13 (by decide) (choices 1) [2,16,32] r25927 c25927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9177
  · exact u9178
  · exact u9179

def r25928 : Route 9 := (fun mask => (mask,id))

def c25928 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25928 : Upper (D 7) (R 7) [36,257,66,129,192,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,129,192,16] 13 (by decide) (choices 1) [2,8,32] r25928 c25928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9180
  · exact u9181
  · exact u9182

def b25929 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 138 176 33 88 216 344), lower := (rows 37 259 70 138 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 14 14 49 32 67 131 259), good := (rows 508 478 462 462 176 496 64 128 256) }] }

theorem u25929 : Upper (D 7) (R 7) [36,257,66,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25930 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 259 70 138 176 40 81 209 337), lower := (rows 37 259 70 138 176 40 64 128 256), losses := [] }

theorem u25930 : Upper (D 7) (R 7) [36,257,66,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25930 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25931 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 70 138 176 48 73 201 329), lower := (rows 37 259 70 138 176 48 64 128 256), losses := [] }

theorem u25931 : Upper (D 7) (R 7) [36,257,66,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25931 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25932 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 138 176 96 89 153 281), lower := (rows 37 259 70 138 176 96 64 128 256), losses := [] }

theorem u25932 : Upper (D 7) (R 7) [36,257,66,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25933 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 259 70 138 208 33 120 184 312), lower := (rows 37 259 70 138 208 33 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 24 39 72 136 264), good := (rows 37 289 101 504 208 33 64 128 256) }] }

theorem u25933 : Upper (D 7) (R 7) [36,257,66,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25934 : Route 9 := (fun mask => (mask,id))

def c25934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25934 : Upper (D 7) (R 7) [36,257,66,130,192,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,130,192,8] 13 (by decide) (choices 1) [1,16,32] r25934 c25934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9183
  · exact u9184
  · exact u9185

def r25935 : Route 9 := (fun mask => (mask,id))

def c25935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25935 : Upper (D 7) (R 7) [36,257,66,130,192,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,130,192,16] 13 (by decide) (choices 1) [1,8,32] r25935 c25935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9186
  · exact u9187
  · exact u9188

def r25936 : Route 9 := (fun mask => (mask,id))

def c25936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25936 : Upper (D 7) (R 7) [36,257,66,160,192,1] 13 := by
  apply FastRouting.sound _ _ [36,257,66,160,192,1] 13 (by decide) (choices 1) [2,8,16] r25936 c25936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9189
  · exact u9190
  · exact u9191

def b25937 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 168 208 34 89 153 281), lower := (rows 37 259 70 168 208 34 64 128 256), losses := [] }

theorem u25937 : Upper (D 7) (R 7) [36,257,66,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25938 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 70 168 208 40 83 147 275), lower := (rows 37 259 70 168 208 40 64 128 256), losses := [] }

theorem u25938 : Upper (D 7) (R 7) [36,257,66,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25938 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25939 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 70 168 208 48 75 139 267), lower := (rows 37 259 70 168 208 48 64 128 256), losses := [] }

theorem u25939 : Upper (D 7) (R 7) [36,257,66,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25939 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25940 : Route 9 := (fun mask => (mask,id))

def c25940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25940 : Upper (D 7) (R 7) [36,257,72,17,130,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,17,130,2] 13 (by decide) (choices 1) [32,128] r25940 c25940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9192
  · exact u9193

def b25941 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 25 146 96 226 162 418), lower := (rows 37 259 76 25 146 96 64 128 256), losses := [] }

theorem u25941 : Upper (D 7) (R 7) [36,257,72,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25942 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(1,7),(2,0),(2,7),(4,0)], upper := (rows 37 259 76 25 146 160 98 226 354), lower := (rows 37 259 76 25 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 186 82 146 274), good := (rows 36 498 108 508 498 160 64 160 256) },{ target := 7, region := (rows 1 11 12 8 16 32 65 0 257), good := (rows 359 323 78 351 18 32 64 0 256) }] }

theorem u25942 : Upper (D 7) (R 7) [36,257,72,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25943 : Route 9 := (fun mask => (mask,id))

def c25943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25943 : Upper (D 7) (R 7) [36,257,72,17,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,17,160,2] 13 (by decide) (choices 1) [2,128] r25943 c25943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9194
  · exact u9195

def b25944 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 25 176 96 194 130 386), lower := (rows 37 259 76 25 176 96 64 128 256), losses := [] }

theorem u25944 : Upper (D 7) (R 7) [36,257,72,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25945 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 76 25 176 160 66 194 322), lower := (rows 37 259 76 25 176 160 64 128 256), losses := [] }

theorem u25945 : Upper (D 7) (R 7) [36,257,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25946 : Route 9 := (fun mask => (mask,id))

def c25946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25946 : Upper (D 7) (R 7) [36,257,72,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,17,192,2] 13 (by decide) (choices 1) [2,32,128] r25946 c25946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9196
  · exact u9197
  · exact u9198

def b25947 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(3,1)], upper := (rows 37 259 76 25 208 160 98 162 290), lower := (rows 37 259 76 25 208 160 64 128 256), losses := [] }

theorem u25947 : Upper (D 7) (R 7) [36,257,72,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25948 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 3, region := 228, targets := 1 }], pairs := [(0,6),(0,7),(2,0),(4,1)], upper := (rows 37 259 76 26 145 34 224 224 480), lower := (rows 37 259 76 26 145 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 291 45 58 145 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 291 109 58 17 34 64 0 256) }] }

theorem u25948 : Upper (D 7) (R 7) [36,257,72,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25949 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 26 145 96 226 162 418), lower := (rows 37 259 76 26 145 96 64 128 256), losses := [] }

theorem u25949 : Upper (D 7) (R 7) [36,257,72,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25950 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 3, region := 228, targets := 1 }], pairs := [(1,7),(2,0),(2,7),(3,7)], upper := (rows 37 259 76 26 145 160 98 226 354), lower := (rows 37 259 76 26 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 19 20 24 16 32 65 0 257), good := (rows 359 323 76 30 351 32 64 0 256) }] }

theorem u25950 : Upper (D 7) (R 7) [36,257,72,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25951 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 76 26 176 33 194 194 450), lower := (rows 37 259 76 26 176 33 64 128 256), losses := [] }

theorem u25951 : Upper (D 7) (R 7) [36,257,72,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25952 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(2,5),(4,1)], upper := (rows 37 259 76 26 176 34 193 193 449), lower := (rows 37 259 76 26 176 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 49 32 67 131 259), good := (rows 501 465 76 476 176 496 64 128 256) },{ target := 5, region := (rows 1 3 12 8 16 0 67 131 259), good := (rows 455 451 76 478 144 450 64 128 256) }] }

theorem u25952 : Upper (D 7) (R 7) [36,257,72,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25953 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 26 176 96 195 131 387), lower := (rows 37 259 76 26 176 96 64 128 256), losses := [] }

theorem u25953 : Upper (D 7) (R 7) [36,257,72,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25954 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 76 26 176 160 67 195 323), lower := (rows 37 259 76 26 176 160 64 128 256), losses := [] }

theorem u25954 : Upper (D 7) (R 7) [36,257,72,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25955 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 259 76 26 208 33 226 162 418), lower := (rows 37 259 76 26 208 33 64 128 256), losses := [] }

theorem u25955 : Upper (D 7) (R 7) [36,257,72,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25956 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(1,6),(4,1)], upper := (rows 37 259 76 26 208 34 225 161 417), lower := (rows 37 259 76 26 208 34 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 291 109 58 80 34 64 0 256) }] }

theorem u25956 : Upper (D 7) (R 7) [36,257,72,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25957 : Route 9 := (fun mask => (mask,id))

def c25957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25957 : Upper (D 7) (R 7) [36,257,72,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,257,72,18,192,128] 13 (by decide) (choices 1) [1,2,32] r25957 c25957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9199
  · exact u9200
  · exact u9201

def b25958 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 76 42 82 33 208 144 400), lower := (rows 37 259 76 42 82 33 64 128 256), losses := [] }

theorem u25958 : Upper (D 7) (R 7) [36,257,72,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25959 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 76 42 82 48 193 129 385), lower := (rows 37 259 76 42 82 48 64 128 256), losses := [] }

theorem u25959 : Upper (D 7) (R 7) [36,257,72,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25959 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25960 : Route 9 := (fun mask => (mask,id))

def c25960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25960 : Upper (D 7) (R 7) [36,257,72,34,66,128] 13 := by
  apply FastRouting.sound _ _ [36,257,72,34,66,128] 13 (by decide) (choices 1) [1,16,128] r25960 c25960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9202
  · exact u9203
  · exact u9204

def b25961 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 259 76 42 145 34 208 208 464), lower := (rows 37 259 76 42 145 34 64 128 256), losses := [] }

theorem u25961 : Upper (D 7) (R 7) [36,257,72,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25962 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 196, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 37 259 76 42 145 48 194 194 450), lower := (rows 37 259 76 42 145 48 64 128 256), losses := [] }

theorem u25962 : Upper (D 7) (R 7) [36,257,72,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25962 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25963 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 42 145 96 210 146 402), lower := (rows 37 259 76 42 145 96 64 128 256), losses := [] }

theorem u25963 : Upper (D 7) (R 7) [36,257,72,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25964 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5),(4,5)], upper := (rows 37 259 76 42 145 160 82 210 338), lower := (rows 37 259 76 42 145 160 64 128 256), losses := [{ target := 5, region := (rows 1 19 12 8 19 0 91 155 283), good := (rows 471 467 460 478 467 128 64 128 256) }] }

theorem u25964 : Upper (D 7) (R 7) [36,257,72,34,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25965 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 76 42 146 33 208 208 464), lower := (rows 37 259 76 42 146 33 64 128 256), losses := [] }

theorem u25965 : Upper (D 7) (R 7) [36,257,72,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25966 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 259 76 42 146 48 193 193 449), lower := (rows 37 259 76 42 146 48 64 128 256), losses := [] }

theorem u25966 : Upper (D 7) (R 7) [36,257,72,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25966 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25967 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 42 146 96 209 145 401), lower := (rows 37 259 76 42 146 96 64 128 256), losses := [] }

theorem u25967 : Upper (D 7) (R 7) [36,257,72,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25968 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 37 259 76 42 146 160 81 209 337), lower := (rows 37 259 76 42 146 160 64 128 256), losses := [] }

theorem u25968 : Upper (D 7) (R 7) [36,257,72,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25969 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 76 42 208 33 210 146 402), lower := (rows 37 259 76 42 208 33 64 128 256), losses := [] }

theorem u25969 : Upper (D 7) (R 7) [36,257,72,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25970 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 259 76 42 208 34 209 145 401), lower := (rows 37 259 76 42 208 34 64 128 256), losses := [] }

theorem u25970 : Upper (D 7) (R 7) [36,257,72,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25971 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 37 259 76 42 208 48 195 131 387), lower := (rows 37 259 76 42 208 48 64 128 256), losses := [] }

theorem u25971 : Upper (D 7) (R 7) [36,257,72,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25971 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25972 : Route 9 := (fun mask => (mask,id))

def c25972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25972 : Upper (D 7) (R 7) [36,257,72,34,192,128] 13 := by
  apply FastRouting.sound _ _ [36,257,72,34,192,128] 13 (by decide) (choices 1) [1,2,16] r25972 c25972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9205
  · exact u9206
  · exact u9207

def b25973 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(2,5),(4,5)], upper := (rows 37 259 76 56 145 34 194 194 450), lower := (rows 37 259 76 56 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 34 98 162 290), good := (rows 484 482 76 508 144 482 64 128 256) },{ target := 5, region := (rows 1 19 12 8 19 0 123 187 315), good := (rows 471 467 460 478 467 466 64 128 256) }] }

theorem u25973 : Upper (D 7) (R 7) [36,257,72,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25974 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 56 145 96 194 130 386), lower := (rows 37 259 76 56 145 96 64 128 256), losses := [] }

theorem u25974 : Upper (D 7) (R 7) [36,257,72,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25975 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 76 56 145 160 66 194 322), lower := (rows 37 259 76 56 145 160 64 128 256), losses := [] }

theorem u25975 : Upper (D 7) (R 7) [36,257,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25976 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 76 56 146 33 194 194 450), lower := (rows 37 259 76 56 146 33 64 128 256), losses := [] }

theorem u25976 : Upper (D 7) (R 7) [36,257,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25977 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 37 259 76 56 146 34 193 193 449), lower := (rows 37 259 76 56 146 34 64 128 256), losses := [] }

theorem u25977 : Upper (D 7) (R 7) [36,257,72,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25978 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 56 146 96 195 131 387), lower := (rows 37 259 76 56 146 96 64 128 256), losses := [] }

theorem u25978 : Upper (D 7) (R 7) [36,257,72,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25979 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 76 56 146 160 67 195 323), lower := (rows 37 259 76 56 146 160 64 128 256), losses := [] }

theorem u25979 : Upper (D 7) (R 7) [36,257,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25979
end Delivery.IrregularNine14.P07
