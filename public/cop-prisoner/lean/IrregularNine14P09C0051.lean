import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0004
import IrregularNine14P09C0005

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3060 : Route 9 := (fun mask => (mask,id))

def c3060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3060 : Upper (D 9) (R 9) [6,9,96,384,160,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160,256] 13 (by decide) (choices 1) [1,16] r3060 c3060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u261
  · exact u262

def b3061 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 36, targets := 384 },{ cop := 0, region := 456, targets := 32 }], pairs := [(1,0),(2,7),(2,8),(3,5),(4,0)], upper := (rows 7 26 37 73 176 96 448 384 384), lower := (rows 7 26 37 73 176 96 64 128 256), losses := [] }

theorem u3061 : Upper (D 9) (R 9) [6,24,33,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3061 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3062 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 73 176 160 320 448 320), lower := (rows 7 26 37 73 176 160 64 128 256), losses := [] }

theorem u3062 : Upper (D 9) (R 9) [6,24,33,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3062 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3063 : Route 9 := (fun mask => (mask,id))

def c3063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3063 : Upper (D 9) (R 9) [6,24,33,65,160,256] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,160,256] 13 (by decide) (choices 1) [128,256] r3063 c3063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u263
  · exact u264

def b3064 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 26 37 73 208 160 352 416 288), lower := (rows 7 26 37 73 208 160 64 128 256), losses := [] }

theorem u3064 : Upper (D 9) (R 9) [6,24,33,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3064 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3065 : Route 9 := (fun mask => (mask,id))

def c3065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3065 : Upper (D 9) (R 9) [6,24,33,65,192,256] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,192,256] 13 (by decide) (choices 1) [32,128,256] r3065 c3065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u265
  · exact u266
  · exact u267

def b3066 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 36, targets := 384 },{ cop := 2, region := 400, targets := 64 }], pairs := [(1,0),(2,7),(2,8),(4,0),(4,6)], upper := (rows 7 26 37 73 400 96 480 416 416), lower := (rows 7 26 37 73 400 96 64 128 256), losses := [] }

theorem u3066 : Upper (D 9) (R 9) [6,24,33,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3066 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3067 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 2, region := 328, targets := 128 }], pairs := [(0,6),(1,0),(2,6),(3,7),(4,0)], upper := (rows 7 26 37 73 400 160 352 480 352), lower := (rows 7 26 37 73 400 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 176 0 128 256), good := (rows 7 63 37 9 432 160 0 160 256) }] }

theorem u3067 : Upper (D 9) (R 9) [6,24,33,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3067 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3068 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 26 37 104 208 33 448 384 384), lower := (rows 7 26 37 104 208 33 64 128 256), losses := [] }

theorem u3068 : Upper (D 9) (R 9) [6,24,33,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3068 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3069 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 26 37 104 208 160 321 385 257), lower := (rows 7 26 37 104 208 160 64 128 256), losses := [] }

theorem u3069 : Upper (D 9) (R 9) [6,24,33,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3069 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3070 : Route 9 := (fun mask => (mask,id))

def c3070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3070 : Upper (D 9) (R 9) [6,24,33,96,192,256] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,192,256] 13 (by decide) (choices 1) [1,128,256] r3070 c3070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u268
  · exact u269
  · exact u270

def b3071 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 37, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(2,6),(2,7)], upper := (rows 7 26 37 104 400 33 448 448 448), lower := (rows 7 26 37 104 400 33 64 128 256), losses := [] }

theorem u3071 : Upper (D 9) (R 9) [6,24,33,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3071 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3072 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0),(4,6)], upper := (rows 7 26 37 104 400 96 449 385 385), lower := (rows 7 26 37 104 400 96 64 128 256), losses := [] }

theorem u3072 : Upper (D 9) (R 9) [6,24,33,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3072 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3073 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 2, region := 328, targets := 128 }], pairs := [(0,6),(0,8),(2,6),(3,7),(4,5)], upper := (rows 7 26 37 104 400 160 321 449 321), lower := (rows 7 26 37 104 400 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 176 0 128 256), good := (rows 7 63 37 40 432 160 0 160 256) },{ target := 8, region := (rows 3 2 6 8 16 176 64 128 0), good := (rows 7 63 37 104 176 160 64 160 0) }] }

theorem u3073 : Upper (D 9) (R 9) [6,24,33,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3073 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3074 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 2, region := 474, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(2,7),(2,8)], upper := (rows 7 26 37 200 336 33 480 416 416), lower := (rows 7 26 37 200 336 33 64 128 256), losses := [] }

theorem u3074 : Upper (D 9) (R 9) [6,24,33,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3074 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3075 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(2,6),(2,8),(4,7)], upper := (rows 7 26 37 200 336 160 353 417 289), lower := (rows 7 26 37 200 336 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 6 8 16 168 64 128 0), good := (rows 7 63 37 232 80 160 64 160 0) }] }

theorem u3075 : Upper (D 9) (R 9) [6,24,33,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3075 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3076 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 3, region := 402, targets := 32 }], pairs := [(0,6),(1,5),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 41 145 96 448 384 384), lower := (rows 7 26 100 41 145 96 64 128 256), losses := [] }

theorem u3076 : Upper (D 9) (R 9) [6,24,96,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3076 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3077 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 42, targets := 320 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(1,6),(1,8),(3,6),(3,8)], upper := (rows 7 26 100 41 145 160 320 448 320), lower := (rows 7 26 100 41 145 160 64 128 256), losses := [] }

theorem u3077 : Upper (D 9) (R 9) [6,24,96,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3077 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3078 : Route 9 := (fun mask => (mask,id))

def c3078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3078 : Upper (D 9) (R 9) [6,24,96,33,129,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,129,256] 13 (by decide) (choices 1) [128,256] r3078 c3078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u271
  · exact u272

def b3079 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 26 100 41 208 33 448 384 384), lower := (rows 7 26 100 41 208 33 64 128 256), losses := [] }

theorem u3079 : Upper (D 9) (R 9) [6,24,96,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3079 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3080 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 7 26 100 41 208 160 321 385 257), lower := (rows 7 26 100 41 208 160 64 128 256), losses := [] }

theorem u3080 : Upper (D 9) (R 9) [6,24,96,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3080 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3081 : Route 9 := (fun mask => (mask,id))

def c3081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3081 : Upper (D 9) (R 9) [6,24,96,33,192,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,192,256] 13 (by decide) (choices 1) [1,128,256] r3081 c3081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u273
  · exact u274
  · exact u275

def b3082 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 40, targets := 448 },{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(3,6),(3,7),(3,8)], upper := (rows 7 26 100 41 400 33 448 448 448), lower := (rows 7 26 100 41 400 33 64 128 256), losses := [] }

theorem u3082 : Upper (D 9) (R 9) [6,24,96,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3082 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3083 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 26 100 41 400 96 449 385 385), lower := (rows 7 26 100 41 400 96 64 128 256), losses := [] }

theorem u3083 : Upper (D 9) (R 9) [6,24,96,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3083 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3084 : Route 9 := (fun mask => (mask,id))

def c3084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3084 : Upper (D 9) (R 9) [6,24,96,33,384,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,384,128] 13 (by decide) (choices 1) [1,256] r3084 c3084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u276
  · exact u277

def b3085 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 50, targets := 320 },{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(1,6),(1,8),(4,6),(4,8)], upper := (rows 7 26 100 137 176 33 320 448 320), lower := (rows 7 26 100 137 176 33 64 128 256), losses := [] }

theorem u3085 : Upper (D 9) (R 9) [6,24,96,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3085 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3086 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 26 100 137 176 96 321 385 257), lower := (rows 7 26 100 137 176 96 64 128 256), losses := [] }

theorem u3086 : Upper (D 9) (R 9) [6,24,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3086 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3087 : Route 9 := (fun mask => (mask,id))

def c3087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3087 : Upper (D 9) (R 9) [6,24,96,129,160,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,160,256] 13 (by decide) (choices 1) [1,256] r3087 c3087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u278
  · exact u279

def b3088 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 128 }], pairs := [(0,6),(1,6),(2,7),(3,6),(4,6)], upper := (rows 7 26 100 137 273 96 480 416 416), lower := (rows 7 26 100 137 273 96 64 128 256), losses := [] }

theorem u3088 : Upper (D 9) (R 9) [6,24,96,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3088 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3089_32 : Upper (D 9) (R 9) [6,24,96,129,257,128,32] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u280

def r3089 : Route 9 := (fun mask => (mask,id))

def c3089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3089 : Upper (D 9) (R 9) [6,24,96,129,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257,128] 13 (by decide) (choices 1) [32,256] r3089 c3089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3089_32
  · exact u281

def r3090 : Route 9 := (fun mask => (mask,id))

def c3090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3090 : Upper (D 9) (R 9) [6,24,96,129,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,1] 13 (by decide) (choices 1) [128,256] r3090 c3090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u282
  · exact u283

def b3091 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 26 100 137 304 96 449 385 385), lower := (rows 7 26 100 137 304 96 64 128 256), losses := [] }

theorem u3091 : Upper (D 9) (R 9) [6,24,96,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3091 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3092 : Route 9 := (fun mask => (mask,id))

def c3092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3092 : Upper (D 9) (R 9) [6,24,96,129,288,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,128] 13 (by decide) (choices 1) [1,256] r3092 c3092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u284
  · exact u285

def b3093 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 26 100 137 304 288 193 193 449), lower := (rows 7 26 100 137 304 288 64 128 256), losses := [] }

theorem u3093 : Upper (D 9) (R 9) [6,24,96,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3093 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 357, targets := 128 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(2,7),(4,0)], upper := (rows 7 26 100 137 400 33 352 480 352), lower := (rows 7 26 100 137 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 53 32 100 164 292), good := (rows 470 26 500 154 400 500 64 128 256) }] }

theorem u3094 : Upper (D 9) (R 9) [6,24,96,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3094 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3095 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 26 100 137 400 96 353 417 289), lower := (rows 7 26 100 137 400 96 64 128 256), losses := [] }

theorem u3095 : Upper (D 9) (R 9) [6,24,96,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3095 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3096_1 : Upper (D 9) (R 9) [6,24,96,129,384,256,1] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u286

theorem m3096_32 : Upper (D 9) (R 9) [6,24,96,129,384,256,32] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u287

def r3096 : Route 9 := (fun mask => (mask,id))

def c3096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3096 : Upper (D 9) (R 9) [6,24,96,129,384,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,384,256] 13 (by decide) (choices 1) [1,32] r3096 c3096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3096_1
  · exact m3096_32

def b3097 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 26 100 168 208 33 321 385 257), lower := (rows 7 26 100 168 208 33 64 128 256), losses := [] }

theorem u3097 : Upper (D 9) (R 9) [6,24,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3097 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3098_1 : Upper (D 9) (R 9) [6,24,96,160,192,256,1] 13 :=
  permutation_upper _ _ _ [6,24,96,160,192,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u288

def r3098 : Route 9 := (fun mask => (mask,id))

def c3098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3098 : Upper (D 9) (R 9) [6,24,96,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,192,256] 13 (by decide) (choices 1) [1,256] r3098 c3098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3098_1
  · exact u289

def r3099 : Route 9 := (fun mask => (mask,id))

def c3099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3099 : Upper (D 9) (R 9) [6,24,96,160,320,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,320,1] 13 (by decide) (choices 1) [1,128,256] r3099 c3099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u290
  · exact u291
  · exact u292

def b3100 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 26 100 168 336 160 321 385 257), lower := (rows 7 26 100 168 336 160 64 128 256), losses := [] }

theorem u3100 : Upper (D 9) (R 9) [6,24,96,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3100 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 36, targets := 129 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(0,7),(2,0),(2,7),(3,6),(4,5)], upper := (rows 7 26 100 168 336 288 193 129 385), lower := (rows 7 26 100 168 336 288 64 128 256), losses := [{ target := 7, region := (rows 3 2 20 8 16 304 64 0 256), good := (rows 7 63 100 40 372 288 64 0 288) }] }

theorem u3101 : Upper (D 9) (R 9) [6,24,96,160,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3101 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3102 : Route 9 := (fun mask => (mask,id))

def c3102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3102 : Upper (D 9) (R 9) [6,24,96,160,384,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,384,1] 13 (by decide) (choices 1) [1,256] r3102 c3102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u293
  · exact u294

def b3103 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 26 100 168 400 96 321 385 257), lower := (rows 7 26 100 168 400 96 64 128 256), losses := [] }

theorem u3103 : Upper (D 9) (R 9) [6,24,96,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3103 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 42, targets := 65 },{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 26 100 168 400 288 65 193 321), lower := (rows 7 26 100 168 400 288 64 128 256), losses := [] }

theorem u3104 : Upper (D 9) (R 9) [6,24,96,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3104 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 69 56 208 40 448 384 384), lower := (rows 7 35 69 56 208 40 64 128 256), losses := [] }

theorem u3105 : Upper (D 9) (R 9) [6,33,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3105 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 69 56 208 160 328 392 264), lower := (rows 7 35 69 56 208 160 64 128 256), losses := [] }

theorem u3106 : Upper (D 9) (R 9) [6,33,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3107 : Route 9 := (fun mask => (mask,id))

def c3107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3107 : Upper (D 9) (R 9) [6,33,65,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,192,256] 13 (by decide) (choices 1) [8,128,256] r3107 c3107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u295
  · exact u296
  · exact u297

def b3108 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 4, region := 40, targets := 64 }], pairs := [(0,5),(2,5),(3,6),(4,5)], upper := (rows 7 35 69 56 400 40 448 448 448), lower := (rows 7 35 69 56 400 40 64 128 256), losses := [] }

theorem u3108 : Upper (D 9) (R 9) [6,33,65,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3108 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3109 : PairBound 9 := { available := 392, camps := [{ cop := 5, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 69 56 400 96 456 392 392), lower := (rows 7 35 69 56 400 96 64 128 256), losses := [] }

theorem u3109 : Upper (D 9) (R 9) [6,33,65,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3109 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3110 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 7 35 69 56 400 160 328 456 328), lower := (rows 7 35 69 56 400 160 64 128 256), losses := [] }

theorem u3110 : Upper (D 9) (R 9) [6,33,65,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3111 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 69 152 280 96 480 416 416), lower := (rows 7 35 69 152 280 96 64 128 256), losses := [] }

theorem u3111 : Upper (D 9) (R 9) [6,33,65,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3111 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3112 : PairBound 9 := { available := 352, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 7 35 69 152 280 160 352 480 352), lower := (rows 7 35 69 152 280 160 64 128 256), losses := [] }

theorem u3112 : Upper (D 9) (R 9) [6,33,65,144,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3112 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3113 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 69 152 304 40 448 448 448), lower := (rows 7 35 69 152 304 40 64 128 256), losses := [] }

theorem u3113 : Upper (D 9) (R 9) [6,33,65,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3113 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 392, camps := [{ cop := 5, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 69 152 304 96 456 392 392), lower := (rows 7 35 69 152 304 96 64 128 256), losses := [] }

theorem u3114 : Upper (D 9) (R 9) [6,33,65,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3114 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3115 : Route 9 := (fun mask => (mask,id))

def c3115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3115 : Upper (D 9) (R 9) [6,33,65,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288,128] 13 (by decide) (choices 1) [8,256] r3115 c3115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u298
  · exact u299

def b3116 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 7 35 69 152 304 288 200 200 456), lower := (rows 7 35 69 152 304 288 64 128 256), losses := [] }

theorem u3116 : Upper (D 9) (R 9) [6,33,65,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3116 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3117 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 69 168 208 40 336 400 272), lower := (rows 7 35 69 168 208 40 64 128 256), losses := [] }

theorem u3117 : Upper (D 9) (R 9) [6,33,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3117 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3118 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 69 168 208 48 328 392 264), lower := (rows 7 35 69 168 208 48 64 128 256), losses := [] }

theorem u3118 : Upper (D 9) (R 9) [6,33,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3118 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3119_8 : Upper (D 9) (R 9) [6,33,65,160,192,256,8] 13 :=
  permutation_upper _ _ _ [6,33,65,160,192,16,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u301

theorem m3119_16 : Upper (D 9) (R 9) [6,33,65,160,192,256,16] 13 :=
  permutation_upper _ _ _ [6,33,65,160,192,8,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u300

def r3119 : Route 9 := (fun mask => (mask,id))

def c3119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3119 : Upper (D 9) (R 9) [6,33,65,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,192,256] 13 (by decide) (choices 1) [8,16,256] r3119 c3119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3119_8
  · exact m3119_16
  · exact u302

#print axioms u3119
end Delivery.IrregularNine14.P09
