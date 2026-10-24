import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0154
import IrregularNine14P07C0155

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r26100 : Route 9 := (fun mask => (mask,id))

def c26100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26100 : Upper (D 7) (R 7) [36,257,192,66,130,8] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,130,8] 13 (by decide) (choices 1) [1,16,32] r26100 c26100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9277
  · exact u9278
  · exact u9279

def b26101 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 259 196 74 152 33 114 178 306), lower := (rows 37 259 196 74 152 33 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 24 39 0 136 264), good := (rows 37 291 165 442 408 33 0 128 256) }] }

theorem u26101 : Upper (D 7) (R 7) [36,257,192,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26102 : Route 9 := (fun mask => (mask,id))

def c26102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26102 : Upper (D 7) (R 7) [36,257,192,66,136,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,136,2] 13 (by decide) (choices 1) [1,16,32] r26102 c26102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9280
  · exact u9281
  · exact u9282

def b26103 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(1,6),(1,7),(3,7)], upper := (rows 37 259 196 74 152 48 99 163 291), lower := (rows 37 259 196 74 152 48 64 128 256), losses := [] }

theorem u26103 : Upper (D 7) (R 7) [36,257,192,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26103 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26104 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 259 196 74 176 33 90 154 282), lower := (rows 37 259 196 74 176 33 64 128 256), losses := [] }

theorem u26104 : Upper (D 7) (R 7) [36,257,192,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26105 : Route 9 := (fun mask => (mask,id))

def c26105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26105 : Upper (D 7) (R 7) [36,257,192,66,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,160,2] 13 (by decide) (choices 1) [1,8,16] r26105 c26105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9283
  · exact u9284
  · exact u9285

def r26106 : Route 9 := (fun mask => (mask,id))

def c26106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26106 : Upper (D 7) (R 7) [36,257,192,66,160,8] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,160,8] 13 (by decide) (choices 1) [1,2,16] r26106 c26106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9286
  · exact u9287
  · exact u9288

def b26107 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 259 196 74 176 48 75 139 267), lower := (rows 37 259 196 74 176 48 64 128 256), losses := [] }

theorem u26107 : Upper (D 7) (R 7) [36,257,192,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26107 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26108 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 57, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(3,1),(4,1)], upper := (rows 37 259 196 88 176 33 74 138 266), lower := (rows 37 259 196 88 176 33 64 128 256), losses := [] }

theorem u26108 : Upper (D 7) (R 7) [36,257,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26109 : Route 9 := (fun mask => (mask,id))

def c26109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26109 : Upper (D 7) (R 7) [36,257,192,80,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,80,160,2] 13 (by decide) (choices 1) [1,2,8] r26109 c26109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9289
  · exact u9290
  · exact u9291

def b26110 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 259 196 88 176 40 67 131 259), lower := (rows 37 259 196 88 176 40 64 128 256), losses := [] }

theorem u26110 : Upper (D 7) (R 7) [36,257,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26110 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26111 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 266 7 25 82 96 224 160 416), lower := (rows 37 266 7 25 82 96 64 128 256), losses := [] }

theorem u26111 : Upper (D 7) (R 7) [36,264,3,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26112 : Route 9 := (fun mask => (mask,id))

def c26112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26112 : Upper (D 7) (R 7) [36,264,3,17,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,17,66,128] 13 (by decide) (choices 1) [32,128] r26112 c26112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9292
  · exact u9293

def b26113 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 25 208 34 224 224 480), lower := (rows 37 266 7 25 208 34 64 128 256), losses := [] }

theorem u26113 : Upper (D 7) (R 7) [36,264,3,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26114 : Route 9 := (fun mask => (mask,id))

def c26114 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26114 : Upper (D 7) (R 7) [36,264,3,17,192,64] 13 := by
  apply FastRouting.sound _ _ [36,264,3,17,192,64] 13 (by decide) (choices 1) [2,32,128] r26114 c26114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9294
  · exact u9295
  · exact u9296

def b26115 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 26 112 33 192 192 448), lower := (rows 37 266 7 26 112 33 64 128 256), losses := [] }

theorem u26115 : Upper (D 7) (R 7) [36,264,3,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26116 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 37 266 7 26 112 96 193 129 385), lower := (rows 37 266 7 26 112 96 64 128 256), losses := [] }

theorem u26116 : Upper (D 7) (R 7) [36,264,3,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26117 : Route 9 := (fun mask => (mask,id))

def c26117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26117 : Upper (D 7) (R 7) [36,264,3,18,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,18,96,128] 13 (by decide) (choices 1) [1,128] r26117 c26117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9297
  · exact u9298

def b26118 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 26 208 33 224 224 480), lower := (rows 37 266 7 26 208 33 64 128 256), losses := [] }

theorem u26118 : Upper (D 7) (R 7) [36,264,3,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26119 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 266 7 26 208 96 225 161 417), lower := (rows 37 266 7 26 208 96 64 128 256), losses := [{ target := 7, region := (rows 9 2 14 8 16 112 64 0 256), good := (rows 37 271 7 63 112 96 96 0 256) }] }

theorem u26119 : Upper (D 7) (R 7) [36,264,3,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26120 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 56 82 33 192 192 448), lower := (rows 37 266 7 56 82 33 64 128 256), losses := [] }

theorem u26120 : Upper (D 7) (R 7) [36,264,3,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26121 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 37 266 7 56 82 96 193 129 385), lower := (rows 37 266 7 56 82 96 64 128 256), losses := [] }

theorem u26121 : Upper (D 7) (R 7) [36,264,3,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26122 : Route 9 := (fun mask => (mask,id))

def c26122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26122 : Upper (D 7) (R 7) [36,264,3,48,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,48,66,128] 13 (by decide) (choices 1) [1,128] r26122 c26122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9299
  · exact u9300

def b26123 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 56 208 33 194 194 450), lower := (rows 37 266 7 56 208 33 64 128 256), losses := [] }

theorem u26123 : Upper (D 7) (R 7) [36,264,3,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26124 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 56 208 34 193 193 449), lower := (rows 37 266 7 56 208 34 64 128 256), losses := [] }

theorem u26124 : Upper (D 7) (R 7) [36,264,3,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26125 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 37 266 7 56 208 96 195 131 387), lower := (rows 37 266 7 56 208 96 64 128 256), losses := [] }

theorem u26125 : Upper (D 7) (R 7) [36,264,3,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26126 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 73 112 34 208 144 400), lower := (rows 37 266 7 73 112 34 64 128 256), losses := [] }

theorem u26126 : Upper (D 7) (R 7) [36,264,3,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26127 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 7 73 112 48 194 130 386), lower := (rows 37 266 7 73 112 48 64 128 256), losses := [] }

theorem u26127 : Upper (D 7) (R 7) [36,264,3,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26127 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26128 : Route 9 := (fun mask => (mask,id))

def c26128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26128 : Upper (D 7) (R 7) [36,264,3,65,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65,96,128] 13 (by decide) (choices 1) [2,16,128] r26128 c26128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9301
  · exact u9302
  · exact u9303

def b26129 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 266 7 73 146 48 224 224 480), lower := (rows 37 266 7 73 146 48 64 128 256), losses := [] }

theorem u26129 : Upper (D 7) (R 7) [36,264,3,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26129 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26130 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(1,6),(2,6),(4,0)], upper := (rows 37 266 7 73 146 96 240 176 432), lower := (rows 37 266 7 73 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 28 32 0 129 257), good := (rows 437 286 407 415 146 32 0 128 256) }] }

theorem u26130 : Upper (D 7) (R 7) [36,264,3,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26131 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 266 7 73 146 160 112 240 368), lower := (rows 37 266 7 73 146 160 64 128 256), losses := [] }

theorem u26131 : Upper (D 7) (R 7) [36,264,3,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26132 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 73 176 34 208 208 464), lower := (rows 37 266 7 73 176 34 64 128 256), losses := [] }

theorem u26132 : Upper (D 7) (R 7) [36,264,3,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26133 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 7 73 176 48 194 194 450), lower := (rows 37 266 7 73 176 48 64 128 256), losses := [] }

theorem u26133 : Upper (D 7) (R 7) [36,264,3,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26133 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26134 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(1,6),(2,6),(4,0)], upper := (rows 37 266 7 73 176 96 210 146 402), lower := (rows 37 266 7 73 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 17 32 0 140 268), good := (rows 437 398 407 415 176 32 0 128 256) }] }

theorem u26134 : Upper (D 7) (R 7) [36,264,3,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26135 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 7 73 176 160 82 210 338), lower := (rows 37 266 7 73 176 160 64 128 256), losses := [] }

theorem u26135 : Upper (D 7) (R 7) [36,264,3,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26136 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 73 208 34 240 176 432), lower := (rows 37 266 7 73 208 34 64 128 256), losses := [] }

theorem u26136 : Upper (D 7) (R 7) [36,264,3,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26137 : Route 9 := (fun mask => (mask,id))

def c26137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26137 : Upper (D 7) (R 7) [36,264,3,65,192,16] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65,192,16] 13 (by decide) (choices 1) [2,32,128] r26137 c26137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9304
  · exact u9305
  · exact u9306

def r26138 : Route 9 := (fun mask => (mask,id))

def c26138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26138 : Upper (D 7) (R 7) [36,264,3,65,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65,192,128] 13 (by decide) (choices 1) [2,16,32] r26138 c26138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9307
  · exact u9308
  · exact u9309

def b26139 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 74 112 33 208 144 400), lower := (rows 37 266 7 74 112 33 64 128 256), losses := [] }

theorem u26139 : Upper (D 7) (R 7) [36,264,3,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26140 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 7 74 112 48 193 129 385), lower := (rows 37 266 7 74 112 48 64 128 256), losses := [] }

theorem u26140 : Upper (D 7) (R 7) [36,264,3,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26141 : Route 9 := (fun mask => (mask,id))

def c26141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26141 : Upper (D 7) (R 7) [36,264,3,66,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,66,96,128] 13 (by decide) (choices 1) [1,16,128] r26141 c26141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9310
  · exact u9311
  · exact u9312

def b26142 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 74 176 33 208 208 464), lower := (rows 37 266 7 74 176 33 64 128 256), losses := [] }

theorem u26142 : Upper (D 7) (R 7) [36,264,3,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26143 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 7 74 176 48 193 193 449), lower := (rows 37 266 7 74 176 48 64 128 256), losses := [] }

theorem u26143 : Upper (D 7) (R 7) [36,264,3,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26143 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26144 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 266 7 74 176 96 209 145 401), lower := (rows 37 266 7 74 176 96 64 128 256), losses := [] }

theorem u26144 : Upper (D 7) (R 7) [36,264,3,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26145 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 7 74 176 160 81 209 337), lower := (rows 37 266 7 74 176 160 64 128 256), losses := [] }

theorem u26145 : Upper (D 7) (R 7) [36,264,3,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26146 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 74 208 33 240 176 432), lower := (rows 37 266 7 74 208 33 64 128 256), losses := [] }

theorem u26146 : Upper (D 7) (R 7) [36,264,3,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26147 : Route 9 := (fun mask => (mask,id))

def c26147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26147 : Upper (D 7) (R 7) [36,264,3,66,192,16] 13 := by
  apply FastRouting.sound _ _ [36,264,3,66,192,16] 13 (by decide) (choices 1) [1,32,128] r26147 c26147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9313
  · exact u9314
  · exact u9315

def r26148 : Route 9 := (fun mask => (mask,id))

def c26148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26148 : Upper (D 7) (R 7) [36,264,3,66,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,66,192,128] 13 (by decide) (choices 1) [1,16,32] r26148 c26148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9316
  · exact u9317
  · exact u9318

def b26149 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 88 145 34 224 224 480), lower := (rows 37 266 7 88 145 34 64 128 256), losses := [] }

theorem u26149 : Upper (D 7) (R 7) [36,264,3,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26150 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 266 7 88 145 96 226 162 418), lower := (rows 37 266 7 88 145 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 6 8 16 104 64 0 256), good := (rows 37 303 7 120 17 96 96 0 256) }] }

theorem u26150 : Upper (D 7) (R 7) [36,264,3,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26151 : Route 9 := (fun mask => (mask,id))

def c26151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26151 : Upper (D 7) (R 7) [36,264,3,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,80,129,128] 13 (by decide) (choices 1) [2,32] r26151 c26151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9319
  · exact u9320

def b26152 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 88 146 33 224 224 480), lower := (rows 37 266 7 88 146 33 64 128 256), losses := [] }

theorem u26152 : Upper (D 7) (R 7) [36,264,3,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26153 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,6)], upper := (rows 37 266 7 88 146 96 225 161 417), lower := (rows 37 266 7 88 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 32 0 129 257), good := (rows 437 266 407 24 146 32 0 128 256) },{ target := 7, region := (rows 11 2 22 8 16 104 64 0 256), good := (rows 37 303 7 125 23 96 96 0 256) }] }

theorem u26153 : Upper (D 7) (R 7) [36,264,3,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26154 : Route 9 := (fun mask => (mask,id))

def c26154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26154 : Upper (D 7) (R 7) [36,264,3,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,3,80,130,128] 13 (by decide) (choices 1) [1,32] r26154 c26154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9321
  · exact u9322

def b26155 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 88 176 33 194 194 450), lower := (rows 37 266 7 88 176 33 64 128 256), losses := [] }

theorem u26155 : Upper (D 7) (R 7) [36,264,3,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26156 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 88 176 34 193 193 449), lower := (rows 37 266 7 88 176 34 64 128 256), losses := [] }

theorem u26156 : Upper (D 7) (R 7) [36,264,3,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26157 : Route 9 := (fun mask => (mask,id))

def c26157 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26157 : Upper (D 7) (R 7) [36,264,3,80,160,64] 13 := by
  apply FastRouting.sound _ _ [36,264,3,80,160,64] 13 (by decide) (choices 1) [1,2,128] r26157 c26157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9323
  · exact u9324
  · exact u9325

def b26158 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 7 88 176 160 67 195 323), lower := (rows 37 266 7 88 176 160 64 128 256), losses := [] }

theorem u26158 : Upper (D 7) (R 7) [36,264,3,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26159 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 104 81 34 208 144 400), lower := (rows 37 266 7 104 81 34 64 128 256), losses := [] }

theorem u26159 : Upper (D 7) (R 7) [36,264,3,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26159
end Delivery.IrregularNine14.P07
