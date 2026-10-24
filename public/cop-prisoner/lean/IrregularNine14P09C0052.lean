import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0005

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3120 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 168 336 40 464 400 400), lower := (rows 7 35 69 168 336 40 64 128 256), losses := [] }

theorem u3120 : Upper (D 9) (R 9) [6,33,65,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3120 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3121 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 69 168 336 48 456 392 392), lower := (rows 7 35 69 168 336 48 64 128 256), losses := [] }

theorem u3121 : Upper (D 9) (R 9) [6,33,65,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3121 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3122 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 35 69 168 336 160 344 408 280), lower := (rows 7 35 69 168 336 160 64 128 256), losses := [] }

theorem u3122 : Upper (D 9) (R 9) [6,33,65,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3122 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3123 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 7 35 69 168 336 288 216 152 408), lower := (rows 7 35 69 168 336 288 64 128 256), losses := [] }

theorem u3123 : Upper (D 9) (R 9) [6,33,65,160,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3123 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3124 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 168 400 40 336 464 336), lower := (rows 7 35 69 168 400 40 64 128 256), losses := [] }

theorem u3124 : Upper (D 9) (R 9) [6,33,65,160,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3124 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3125 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 168 400 48 328 456 328), lower := (rows 7 35 69 168 400 48 64 128 256), losses := [] }

theorem u3125 : Upper (D 9) (R 9) [6,33,65,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3125 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3126 : PairBound 9 := { available := 280, camps := [{ cop := 5, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 69 168 400 96 344 408 280), lower := (rows 7 35 69 168 400 96 64 128 256), losses := [] }

theorem u3126 : Upper (D 9) (R 9) [6,33,65,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3126 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3127 : Route 9 := (fun mask => (mask,id))

def c3127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3127 : Upper (D 9) (R 9) [6,33,65,160,384,256] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,384,256] 13 (by decide) (choices 1) [8,16] r3127 c3127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u303
  · exact u304

def b3128 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 25 176 96 448 384 384), lower := (rows 7 35 76 25 176 96 64 128 256), losses := [] }

theorem u3128 : Upper (D 9) (R 9) [6,33,72,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3128 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 3, region := 324, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(3,7)], upper := (rows 7 35 76 25 176 160 320 448 320), lower := (rows 7 35 76 25 176 160 64 128 256), losses := [] }

theorem u3129 : Upper (D 9) (R 9) [6,33,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3129 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3130 : Route 9 := (fun mask => (mask,id))

def c3130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3130 : Upper (D 9) (R 9) [6,33,72,17,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,160,256] 13 (by decide) (choices 1) [128,256] r3130 c3130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u305
  · exact u306

def b3131 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 25 208 160 352 416 288), lower := (rows 7 35 76 25 208 160 64 128 256), losses := [] }

theorem u3131 : Upper (D 9) (R 9) [6,33,72,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3131 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3132 : Route 9 := (fun mask => (mask,id))

def c3132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3132 : Upper (D 9) (R 9) [6,33,72,17,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,192,256] 13 (by decide) (choices 1) [32,128,256] r3132 c3132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u307
  · exact u308
  · exact u309

def b3133 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 25 400 96 480 416 416), lower := (rows 7 35 76 25 400 96 64 128 256), losses := [] }

theorem u3133 : Upper (D 9) (R 9) [6,33,72,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3133 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3134 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 500, targets := 1 }], pairs := [(0,6),(0,8),(1,6),(2,0),(4,0)], upper := (rows 7 35 76 25 400 160 352 480 352), lower := (rows 7 35 76 25 400 160 64 128 256), losses := [{ target := 6, region := (rows 5 10 4 8 16 176 0 128 256), good := (rows 7 35 15 59 432 160 0 160 256) },{ target := 8, region := (rows 5 10 4 8 16 176 64 128 0), good := (rows 7 35 79 59 176 160 64 160 0) }] }

theorem u3134 : Upper (D 9) (R 9) [6,33,72,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3134 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 56 145 96 448 384 384), lower := (rows 7 35 76 56 145 96 64 128 256), losses := [] }

theorem u3135 : Upper (D 9) (R 9) [6,33,72,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3135 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 42, targets := 320 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,6),(1,8),(3,6),(3,8)], upper := (rows 7 35 76 56 145 160 320 448 320), lower := (rows 7 35 76 56 145 160 64 128 256), losses := [] }

theorem u3136 : Upper (D 9) (R 9) [6,33,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3136 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3137 : Route 9 := (fun mask => (mask,id))

def c3137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3137 : Upper (D 9) (R 9) [6,33,72,48,129,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,129,256] 13 (by decide) (choices 1) [128,256] r3137 c3137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u310
  · exact u311

def b3138 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 76 56 208 33 448 384 384), lower := (rows 7 35 76 56 208 33 64 128 256), losses := [] }

theorem u3138 : Upper (D 9) (R 9) [6,33,72,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3138 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3139 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 56 208 160 321 385 257), lower := (rows 7 35 76 56 208 160 64 128 256), losses := [] }

theorem u3139 : Upper (D 9) (R 9) [6,33,72,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3139 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3140 : Route 9 := (fun mask => (mask,id))

def c3140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3140 : Upper (D 9) (R 9) [6,33,72,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,192,256] 13 (by decide) (choices 1) [1,128,256] r3140 c3140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u312
  · exact u313
  · exact u314

def b3141 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 76 56 400 33 448 448 448), lower := (rows 7 35 76 56 400 33 64 128 256), losses := [] }

theorem u3141 : Upper (D 9) (R 9) [6,33,72,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3141 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3142 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 56 400 96 449 385 385), lower := (rows 7 35 76 56 400 96 64 128 256), losses := [] }

theorem u3142 : Upper (D 9) (R 9) [6,33,72,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3142 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3143 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 7 35 76 56 400 160 321 449 321), lower := (rows 7 35 76 56 400 160 64 128 256), losses := [] }

theorem u3143 : Upper (D 9) (R 9) [6,33,72,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3143 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3144 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 76 137 112 48 448 384 384), lower := (rows 7 35 76 137 112 48 64 128 256), losses := [] }

theorem u3144 : Upper (D 9) (R 9) [6,33,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3144 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3145 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 34, targets := 320 },{ cop := 1, region := 336, targets := 128 }], pairs := [(1,6),(1,8),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 112 160 336 400 272), lower := (rows 7 35 76 137 112 160 64 128 256), losses := [] }

theorem u3145 : Upper (D 9) (R 9) [6,33,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3145 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3146 : Route 9 := (fun mask => (mask,id))

def c3146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u3146 : Upper (D 9) (R 9) [6,33,72,129,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,96,256] 13 (by decide) (choices 1) [16,128,256] r3146 c3146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u315
  · exact u316
  · exact u317

def b3147 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 50, targets := 320 }], pairs := [(1,6),(1,8),(4,6),(4,8)], upper := (rows 7 35 76 137 176 48 320 448 320), lower := (rows 7 35 76 137 176 48 64 128 256), losses := [] }

theorem u3147 : Upper (D 9) (R 9) [6,33,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3147 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3148 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 137 176 96 336 400 272), lower := (rows 7 35 76 137 176 96 64 128 256), losses := [] }

theorem u3148 : Upper (D 9) (R 9) [6,33,72,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3148 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3149 : Route 9 := (fun mask => (mask,id))

def c3149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3149 : Upper (D 9) (R 9) [6,33,72,129,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,160,256] 13 (by decide) (choices 1) [16,256] r3149 c3149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u318
  · exact u319

def b3150 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 137 208 48 352 416 288), lower := (rows 7 35 76 137 208 48 64 128 256), losses := [] }

theorem u3150 : Upper (D 9) (R 9) [6,33,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3150 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3151 : Route 9 := (fun mask => (mask,id))

def c3151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3151 : Upper (D 9) (R 9) [6,33,72,129,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,192,256] 13 (by decide) (choices 1) [16,32,256] r3151 c3151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u320
  · exact u321
  · exact u322

def b3152 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 3, region := 324, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(3,5)], upper := (rows 7 35 76 137 304 48 448 448 448), lower := (rows 7 35 76 137 304 48 64 128 256), losses := [] }

theorem u3152 : Upper (D 9) (R 9) [6,33,72,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3152 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3153 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 137 304 96 464 400 400), lower := (rows 7 35 76 137 304 96 64 128 256), losses := [] }

theorem u3153 : Upper (D 9) (R 9) [6,33,72,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3153 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 34, targets := 320 },{ cop := 1, region := 336, targets := 128 }], pairs := [(1,6),(1,8),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 304 160 336 464 336), lower := (rows 7 35 76 137 304 160 64 128 256), losses := [] }

theorem u3154 : Upper (D 9) (R 9) [6,33,72,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3154 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3155 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 35 76 137 304 288 208 208 464), lower := (rows 7 35 76 137 304 288 64 128 256), losses := [] }

theorem u3155 : Upper (D 9) (R 9) [6,33,72,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3155 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3156 : Route 9 := (fun mask => (mask,id))

def c3156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3156 : Upper (D 9) (R 9) [6,33,72,129,320,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,320,16] 13 (by decide) (choices 1) [32,128,256] r3156 c3156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u323
  · exact u324
  · exact u325

def b3157 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 34, targets := 320 },{ cop := 1, region := 336, targets := 128 }], pairs := [(1,6),(1,8),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 336 160 368 432 304), lower := (rows 7 35 76 137 336 160 64 128 256), losses := [] }

theorem u3157 : Upper (D 9) (R 9) [6,33,72,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3157 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3158 : Route 9 := (fun mask => (mask,id))

def c3158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3158 : Upper (D 9) (R 9) [6,33,72,129,320,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,320,256] 13 (by decide) (choices 1) [16,32,128] r3158 c3158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u326
  · exact u327
  · exact u328

def r3159 : Route 9 := (fun mask => (mask,id))

def c3159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3159 : Upper (D 9) (R 9) [6,33,72,129,384,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384,16] 13 (by decide) (choices 1) [32,256] r3159 c3159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u329
  · exact u330

def b3160 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 137 400 96 368 432 304), lower := (rows 7 35 76 137 400 96 64 128 256), losses := [] }

theorem u3160 : Upper (D 9) (R 9) [6,33,72,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3160 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3161 : Route 9 := (fun mask => (mask,id))

def c3161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3161 : Upper (D 9) (R 9) [6,33,72,129,384,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384,256] 13 (by decide) (choices 1) [16,32] r3161 c3161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u331
  · exact u332

def b3162 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 7 35 76 152 112 33 448 384 384), lower := (rows 7 35 76 152 112 33 64 128 256), losses := [] }

theorem u3162 : Upper (D 9) (R 9) [6,33,72,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3162 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3163 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(4,0),(4,7)], upper := (rows 7 35 76 152 112 160 321 385 257), lower := (rows 7 35 76 152 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 22 34 124 184 112 160 64 160 256) },{ target := 8, region := (rows 5 6 4 8 20 168 64 128 0), good := (rows 23 35 127 184 112 160 64 160 0) }] }

theorem u3163 : Upper (D 9) (R 9) [6,33,72,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3163 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3164 : Route 9 := (fun mask => (mask,id))

def c3164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3164 : Upper (D 9) (R 9) [6,33,72,144,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,96,256] 13 (by decide) (choices 1) [1,128,256] r3164 c3164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u333
  · exact u334
  · exact u335

def b3165 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 152 273 96 480 416 416), lower := (rows 7 35 76 152 273 96 64 128 256), losses := [] }

theorem u3165 : Upper (D 9) (R 9) [6,33,72,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3165 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3166 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,7)], upper := (rows 7 35 76 152 273 160 352 480 352), lower := (rows 7 35 76 152 273 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 184 273 160 0 160 256) }] }

theorem u3166 : Upper (D 9) (R 9) [6,33,72,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3166 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3167 : Route 9 := (fun mask => (mask,id))

def c3167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3167 : Upper (D 9) (R 9) [6,33,72,144,257,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,257,256] 13 (by decide) (choices 1) [32,128] r3167 c3167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u336
  · exact u337

def b3168 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 76 152 304 33 448 448 448), lower := (rows 7 35 76 152 304 33 64 128 256), losses := [] }

theorem u3168 : Upper (D 9) (R 9) [6,33,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3168 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3169 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 152 304 96 449 385 385), lower := (rows 7 35 76 152 304 96 64 128 256), losses := [] }

theorem u3169 : Upper (D 9) (R 9) [6,33,72,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3169 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3170 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(4,7)], upper := (rows 7 35 76 152 304 160 321 449 321), lower := (rows 7 35 76 152 304 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 184 304 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 7 35 111 184 48 160 64 160 0) }] }

theorem u3170 : Upper (D 9) (R 9) [6,33,72,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3170 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3171 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 35 76 152 304 288 193 193 449), lower := (rows 7 35 76 152 304 288 64 128 256), losses := [] }

theorem u3171 : Upper (D 9) (R 9) [6,33,72,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3171 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3172 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 7 35 76 152 336 33 480 416 416), lower := (rows 7 35 76 152 336 33 64 128 256), losses := [] }

theorem u3172 : Upper (D 9) (R 9) [6,33,72,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3172 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3173 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(4,7)], upper := (rows 7 35 76 152 336 160 353 417 289), lower := (rows 7 35 76 152 336 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 7 35 111 184 80 160 64 160 0) }] }

theorem u3173 : Upper (D 9) (R 9) [6,33,72,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3173 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3174 : Route 9 := (fun mask => (mask,id))

def c3174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3174 : Upper (D 9) (R 9) [6,33,72,144,320,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,320,256] 13 (by decide) (choices 1) [1,32,128] r3174 c3174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u338
  · exact u339
  · exact u340

def b3175 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 42, targets := 320 }], pairs := [(1,6),(1,8),(3,6),(3,8)], upper := (rows 7 35 76 168 145 48 320 448 320), lower := (rows 7 35 76 168 145 48 64 128 256), losses := [] }

theorem u3175 : Upper (D 9) (R 9) [6,33,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3175 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3176 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 168 145 96 336 400 272), lower := (rows 7 35 76 168 145 96 64 128 256), losses := [] }

theorem u3176 : Upper (D 9) (R 9) [6,33,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3176 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3177 : Route 9 := (fun mask => (mask,id))

def c3177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3177 : Upper (D 9) (R 9) [6,33,72,160,129,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,129,256] 13 (by decide) (choices 1) [16,256] r3177 c3177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u341
  · exact u342

def b3178 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 76 168 208 33 336 400 272), lower := (rows 7 35 76 168 208 33 64 128 256), losses := [] }

theorem u3178 : Upper (D 9) (R 9) [6,33,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3178 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3179 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 168 208 48 321 385 257), lower := (rows 7 35 76 168 208 48 64 128 256), losses := [] }

theorem u3179 : Upper (D 9) (R 9) [6,33,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3179 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3179
end Delivery.IrregularNine14.P09
