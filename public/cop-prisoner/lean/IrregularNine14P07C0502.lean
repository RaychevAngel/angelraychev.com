import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0196
import IrregularNine14P07C0197
import IrregularNine14P07C0198

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30120 : Route 9 := (fun mask => (mask,id))

def c30120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30120 : Upper (D 7) (R 7) [6,9,96,258,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,258,160] 13 (by decide) (choices 1) [1,16,64,128] r30120 c30120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11786
  · exact u11787
  · exact u11788
  · exact u11789

def b30121 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 280 19 224 224 224 480), lower := (rows 7 11 100 280 19 32 64 128 256), losses := [] }

theorem u30121 : Upper (D 7) (R 7) [6,9,96,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30122 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 0, region := 228, targets := 1 }], pairs := [(1,5),(2,0),(3,0),(3,5)], upper := (rows 7 11 100 280 49 226 194 194 450), lower := (rows 7 11 100 280 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 100 284 508 32 64 128 256) }] }

theorem u30122 : Upper (D 7) (R 7) [6,9,96,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30123 : Route 9 := (fun mask => (mask,id))

def c30123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30123 : Upper (D 7) (R 7) [6,9,96,272,34] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,34] 13 (by decide) (choices 1) [1,64,128] r30123 c30123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11790
  · exact u11791
  · exact u11792

def b30124 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 11 100 280 112 163 195 131 387), lower := (rows 7 11 100 280 112 32 64 128 256), losses := [] }

theorem u30124 : Upper (D 7) (R 7) [6,9,96,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30125 : Route 9 := (fun mask => (mask,id))

def c30125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30125 : Upper (D 7) (R 7) [6,9,96,272,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,129] 13 (by decide) (choices 1) [2,64,128] r30125 c30125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11793
  · exact u11794
  · exact u11795

def r30126 : Route 9 := (fun mask => (mask,id))

def c30126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30126 : Upper (D 7) (R 7) [6,9,96,272,130] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,130] 13 (by decide) (choices 1) [1,64,128] r30126 c30126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11796
  · exact u11797
  · exact u11798

def r30127 : Route 9 := (fun mask => (mask,id))

def c30127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30127 : Upper (D 7) (R 7) [6,9,96,272,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,160] 13 (by decide) (choices 1) [1,2,64,128] r30127 c30127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11799
  · exact u11800
  · exact u11801
  · exact u11802

def b30128 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 296 19 240 208 208 464), lower := (rows 7 11 100 296 19 32 64 128 256), losses := [] }

theorem u30128 : Upper (D 7) (R 7) [6,9,96,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30129 : Route 9 := (fun mask => (mask,id))

def c30129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30129 : Upper (D 7) (R 7) [6,9,96,288,65] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,65] 13 (by decide) (choices 1) [2,16,128] r30129 c30129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11803
  · exact u11804
  · exact u11805

def r30130 : Route 9 := (fun mask => (mask,id))

def c30130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30130 : Upper (D 7) (R 7) [6,9,96,288,66] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,66] 13 (by decide) (choices 1) [1,16,128] r30130 c30130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11806
  · exact u11807
  · exact u11808

def r30131 : Route 9 := (fun mask => (mask,id))

def c30131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30131 : Upper (D 7) (R 7) [6,9,96,288,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,129] 13 (by decide) (choices 1) [2,16,64,128] r30131 c30131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11809
  · exact u11810
  · exact u11811
  · exact u11812

def r30132 : Route 9 := (fun mask => (mask,id))

def c30132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30132 : Upper (D 7) (R 7) [6,9,96,288,130] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,130] 13 (by decide) (choices 1) [1,16,64,128] r30132 c30132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11813
  · exact u11814
  · exact u11815
  · exact u11816

def r30133 : Route 9 := (fun mask => (mask,id))

def c30133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30133 : Upper (D 7) (R 7) [6,9,96,288,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,192] 13 (by decide) (choices 1) [1,2,16,128] r30133 c30133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11817
  · exact u11818
  · exact u11819
  · exact u11820

def b30134 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 392 19 240 240 240 496), lower := (rows 7 11 100 392 19 32 64 128 256), losses := [] }

theorem u30134 : Upper (D 7) (R 7) [6,9,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30135 : Route 9 := (fun mask => (mask,id))

def c30135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30135 : Upper (D 7) (R 7) [6,9,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,33] 13 (by decide) (choices 1) [2,16,64,128] r30135 c30135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11821
  · exact u11822
  · exact u11823
  · exact u11824

def r30136 : Route 9 := (fun mask => (mask,id))

def c30136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30136 : Upper (D 7) (R 7) [6,9,96,384,34] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,34] 13 (by decide) (choices 1) [1,16,64,128] r30136 c30136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11825
  · exact u11826
  · exact u11827
  · exact u11828

def b30137 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 16, targets := 131 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 11 100 392 112 179 211 147 403), lower := (rows 7 11 100 392 112 32 64 128 256), losses := [] }

theorem u30137 : Upper (D 7) (R 7) [6,9,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30138 : Route 9 := (fun mask => (mask,id))

def c30138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30138 : Upper (D 7) (R 7) [6,9,96,384,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,129] 13 (by decide) (choices 1) [2,16,64] r30138 c30138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11829
  · exact u11830
  · exact u11831

def r30139 : Route 9 := (fun mask => (mask,id))

def c30139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30139 : Upper (D 7) (R 7) [6,9,96,384,130] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,130] 13 (by decide) (choices 1) [1,16,64] r30139 c30139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11832
  · exact u11833
  · exact u11834

def r30140 : Route 9 := (fun mask => (mask,id))

def c30140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30140 : Upper (D 7) (R 7) [6,9,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160] 13 (by decide) (choices 1) [1,2,16,64] r30140 c30140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11835
  · exact u11836
  · exact u11837
  · exact u11838

def b30141 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 15, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 26 37 11 112 480 448 448 448), lower := (rows 7 26 37 11 112 32 64 128 256), losses := [] }

theorem u30141 : Upper (D 7) (R 7) [6,24,33,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30142 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 37 11 208 480 480 480 480), lower := (rows 7 26 37 11 208 32 64 128 256), losses := [] }

theorem u30142 : Upper (D 7) (R 7) [6,24,33,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30143 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 15, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 26 37 11 304 224 192 192 448), lower := (rows 7 26 37 11 304 32 64 128 256), losses := [] }

theorem u30143 : Upper (D 7) (R 7) [6,24,33,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30144 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 37 11 336 224 224 224 480), lower := (rows 7 26 37 11 336 32 64 128 256), losses := [] }

theorem u30144 : Upper (D 7) (R 7) [6,24,33,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30145 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 8, targets := 192 }], pairs := [(2,1),(3,1),(3,6),(3,7)], upper := (rows 7 26 37 41 82 480 448 448 448), lower := (rows 7 26 37 41 82 32 64 128 256), losses := [] }

theorem u30145 : Upper (D 7) (R 7) [6,24,33,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30146 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6),(3,7)], upper := (rows 7 26 37 41 208 482 450 450 450), lower := (rows 7 26 37 41 208 32 64 128 256), losses := [] }

theorem u30146 : Upper (D 7) (R 7) [6,24,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30147 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 8, targets := 192 }], pairs := [(2,1),(3,1),(3,6),(3,7)], upper := (rows 7 26 37 41 274 224 192 192 448), lower := (rows 7 26 37 41 274 32 64 128 256), losses := [] }

theorem u30147 : Upper (D 7) (R 7) [6,24,33,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30148 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6),(3,7)], upper := (rows 7 26 37 41 336 226 194 194 450), lower := (rows 7 26 37 41 336 32 64 128 256), losses := [] }

theorem u30148 : Upper (D 7) (R 7) [6,24,33,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30149 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 42 81 480 448 448 448), lower := (rows 7 26 37 42 81 32 64 128 256), losses := [] }

theorem u30149 : Upper (D 7) (R 7) [6,24,33,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30150 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 42 208 481 449 449 449), lower := (rows 7 26 37 42 208 32 64 128 256), losses := [] }

theorem u30150 : Upper (D 7) (R 7) [6,24,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30151 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 42 273 224 192 192 448), lower := (rows 7 26 37 42 273 32 64 128 256), losses := [] }

theorem u30151 : Upper (D 7) (R 7) [6,24,33,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30152 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 42 336 225 193 193 449), lower := (rows 7 26 37 42 336 32 64 128 256), losses := [] }

theorem u30152 : Upper (D 7) (R 7) [6,24,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30153 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 18, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7)], upper := (rows 7 26 37 73 82 416 480 416 416), lower := (rows 7 26 37 73 82 32 64 128 256), losses := [] }

theorem u30153 : Upper (D 7) (R 7) [6,24,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30154 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 73 112 418 450 386 386), lower := (rows 7 26 37 73 112 32 64 128 256), losses := [] }

theorem u30154 : Upper (D 7) (R 7) [6,24,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30155 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(2,1),(3,1),(4,0)], upper := (rows 7 26 37 73 146 480 480 480 480), lower := (rows 7 26 37 73 146 32 64 128 256), losses := [] }

theorem u30155 : Upper (D 7) (R 7) [6,24,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30156 : Route 9 := (fun mask => (mask,id))

def c30156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30156 : Upper (D 7) (R 7) [6,24,33,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,160] 13 (by decide) (choices 1) [2,64,128,256] r30156 c30156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11839
  · exact u11840
  · exact u11841
  · exact u11842

def b30157 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 26 37 73 208 418 482 418 418), lower := (rows 7 26 37 73 208 32 64 128 256), losses := [] }

theorem u30157 : Upper (D 7) (R 7) [6,24,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30158 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(2,1),(3,1),(4,0)], upper := (rows 7 26 37 73 274 224 224 224 480), lower := (rows 7 26 37 73 274 32 64 128 256), losses := [] }

theorem u30158 : Upper (D 7) (R 7) [6,24,33,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30159 : Route 9 := (fun mask => (mask,id))

def c30159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30159 : Upper (D 7) (R 7) [6,24,33,65,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,288] 13 (by decide) (choices 1) [2,64,128] r30159 c30159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11843
  · exact u11844
  · exact u11845

def b30160 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 26 37 73 336 162 226 162 418), lower := (rows 7 26 37 73 336 32 64 128 256), losses := [] }

theorem u30160 : Upper (D 7) (R 7) [6,24,33,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30161 : Route 9 := (fun mask => (mask,id))

def c30161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30161 : Upper (D 7) (R 7) [6,24,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,384] 13 (by decide) (choices 1) [2,64,128] r30161 c30161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11846
  · exact u11847
  · exact u11848

def b30162 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 7 26 37 74 112 417 449 385 385), lower := (rows 7 26 37 74 112 32 64 128 256), losses := [] }

theorem u30162 : Upper (D 7) (R 7) [6,24,33,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30163 : Route 9 := (fun mask => (mask,id))

def c30163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30163 : Upper (D 7) (R 7) [6,24,33,66,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,160] 13 (by decide) (choices 1) [1,64,128,256] r30163 c30163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11849
  · exact u11850
  · exact u11851
  · exact u11852

def b30164 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 7 26 37 74 208 417 481 417 417), lower := (rows 7 26 37 74 208 32 64 128 256), losses := [] }

theorem u30164 : Upper (D 7) (R 7) [6,24,33,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30165 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 26 37 74 273 224 224 224 480), lower := (rows 7 26 37 74 273 32 64 128 256), losses := [] }

theorem u30165 : Upper (D 7) (R 7) [6,24,33,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30166 : Route 9 := (fun mask => (mask,id))

def c30166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30166 : Upper (D 7) (R 7) [6,24,33,66,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,288] 13 (by decide) (choices 1) [1,64,128] r30166 c30166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11853
  · exact u11854
  · exact u11855

def b30167 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 7 26 37 74 336 161 225 161 417), lower := (rows 7 26 37 74 336 32 64 128 256), losses := [] }

theorem u30167 : Upper (D 7) (R 7) [6,24,33,66,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30168 : Route 9 := (fun mask => (mask,id))

def c30168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30168 : Upper (D 7) (R 7) [6,24,33,66,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,384] 13 (by decide) (choices 1) [1,64,128] r30168 c30168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11856
  · exact u11857
  · exact u11858

def r30169 : Route 9 := (fun mask => (mask,id))

def c30169 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30169 : Upper (D 7) (R 7) [6,24,33,96,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,192] 13 (by decide) (choices 1) [1,2,128,256] r30169 c30169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11859
  · exact u11860
  · exact u11861
  · exact u11862

def r30170 : Route 9 := (fun mask => (mask,id))

def c30170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30170 : Upper (D 7) (R 7) [6,24,33,96,257] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,257] 13 (by decide) (choices 1) [2,64,128] r30170 c30170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11863
  · exact u11864
  · exact u11865

def r30171 : Route 9 := (fun mask => (mask,id))

def c30171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30171 : Upper (D 7) (R 7) [6,24,33,96,258] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,258] 13 (by decide) (choices 1) [1,64,128] r30171 c30171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11866
  · exact u11867
  · exact u11868

def r30172 : Route 9 := (fun mask => (mask,id))

def c30172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30172 : Upper (D 7) (R 7) [6,24,33,96,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,320] 13 (by decide) (choices 1) [1,2,128] r30172 c30172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11869
  · exact u11870
  · exact u11871

def r30173 : Route 9 := (fun mask => (mask,id))

def c30173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30173 : Upper (D 7) (R 7) [6,24,33,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,384] 13 (by decide) (choices 1) [1,2,64,128] r30173 c30173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11872
  · exact u11873
  · exact u11874
  · exact u11875

def b30174 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 7 26 37 200 208 291 355 419 291), lower := (rows 7 26 37 200 208 32 64 128 256), losses := [] }

theorem u30174 : Upper (D 7) (R 7) [6,24,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30175 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30175 : Upper (D 7) (R 7) [6,24,33,192,257] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,257] 13 (by decide) (choices 1) [2,64] r30175 c30175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11876
  · exact u11877

def r30176 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30176 : Upper (D 7) (R 7) [6,24,33,192,258] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,258] 13 (by decide) (choices 1) [1,64] r30176 c30176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11878
  · exact u11879

def r30177 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30177 : Upper (D 7) (R 7) [6,24,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,288] 13 (by decide) (choices 1) [1,2,64] r30177 c30177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11880
  · exact u11881
  · exact u11882

def r30178 : Route 9 := (fun mask => (mask,id))

def c30178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30178 : Upper (D 7) (R 7) [6,24,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,320] 13 (by decide) (choices 1) [1,2,128] r30178 c30178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11883
  · exact u11884
  · exact u11885

def b30179 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 27, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 26 100 11 49 480 448 448 448), lower := (rows 7 26 100 11 49 32 64 128 256), losses := [] }

theorem u30179 : Upper (D 7) (R 7) [6,24,96,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u30179
end Delivery.IrregularNine14.P07
