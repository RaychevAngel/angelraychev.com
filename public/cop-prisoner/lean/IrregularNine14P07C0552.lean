import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0279
import IrregularNine14P07C0280
import IrregularNine14P07C0281

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33120 : Route 9 := (fun mask => (mask,id))

def c33120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33120 : Upper (D 7) (R 7) [12,96,18,288,129] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288,129] 13 (by decide) (choices 1) [1,2,64,128] r33120 c33120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16779
  · exact u16780
  · exact u16781
  · exact u16782

def b33121 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 296 146 225 193 193 449), lower := (rows 13 98 22 296 146 32 64 128 256), losses := [] }

theorem u33121 : Upper (D 7) (R 7) [12,96,18,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33122 : Route 9 := (fun mask => (mask,id))

def c33122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33122 : Upper (D 7) (R 7) [12,96,18,288,192] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288,192] 13 (by decide) (choices 1) [1,2,128] r33122 c33122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16783
  · exact u16784
  · exact u16785

def b33123 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 392 19 225 225 225 481), lower := (rows 13 98 22 392 19 32 64 128 256), losses := [] }

theorem u33123 : Upper (D 7) (R 7) [12,96,18,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33124 : Route 9 := (fun mask => (mask,id))

def c33124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33124 : Upper (D 7) (R 7) [12,96,18,384,33] 13 := by
  apply FastRouting.sound _ _ [12,96,18,384,33] 13 (by decide) (choices 1) [1,2,64,128] r33124 c33124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16786
  · exact u16787
  · exact u16788
  · exact u16789

def b33125 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 20, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 98 22 392 50 225 193 193 449), lower := (rows 13 98 22 392 50 32 64 128 256), losses := [] }

theorem u33125 : Upper (D 7) (R 7) [12,96,18,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33126 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 22 392 112 163 195 131 387), lower := (rows 13 98 22 392 112 32 64 128 256), losses := [] }

theorem u33126 : Upper (D 7) (R 7) [12,96,18,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33127 : Route 9 := (fun mask => (mask,id))

def c33127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33127 : Upper (D 7) (R 7) [12,96,18,384,129] 13 := by
  apply FastRouting.sound _ _ [12,96,18,384,129] 13 (by decide) (choices 1) [1,2,64] r33127 c33127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16790
  · exact u16791
  · exact u16792

def b33128 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 392 146 97 97 225 353), lower := (rows 13 98 22 392 146 32 64 128 256), losses := [] }

theorem u33128 : Upper (D 7) (R 7) [12,96,18,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33129 : Route 9 := (fun mask => (mask,id))

def c33129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33129 : Upper (D 7) (R 7) [12,96,18,384,160] 13 := by
  apply FastRouting.sound _ _ [12,96,18,384,160] 13 (by decide) (choices 1) [1,2,64] r33129 c33129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16793
  · exact u16794
  · exact u16795

def b33130 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 37 88 19 418 450 386 386), lower := (rows 13 98 37 88 19 32 64 128 256), losses := [] }

theorem u33130 : Upper (D 7) (R 7) [12,96,33,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33131 : Route 9 := (fun mask => (mask,id))

def c33131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33131 : Upper (D 7) (R 7) [12,96,33,80,129] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,129] 13 (by decide) (choices 1) [2,128,256] r33131 c33131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16796
  · exact u16797
  · exact u16798

def r33132 : Route 9 := (fun mask => (mask,id))

def c33132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33132 : Upper (D 7) (R 7) [12,96,33,80,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,130] 13 (by decide) (choices 1) [1,2,128,256] r33132 c33132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16799
  · exact u16800
  · exact u16801
  · exact u16802

def r33133 : Route 9 := (fun mask => (mask,id))

def c33133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33133 : Upper (D 7) (R 7) [12,96,33,80,257] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,257] 13 (by decide) (choices 1) [2,128] r33133 c33133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16803
  · exact u16804

def r33134 : Route 9 := (fun mask => (mask,id))

def c33134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33134 : Upper (D 7) (R 7) [12,96,33,80,258] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,258] 13 (by decide) (choices 1) [1,2,128] r33134 c33134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16805
  · exact u16806
  · exact u16807

def r33135 : Route 9 := (fun mask => (mask,id))

def c33135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33135 : Upper (D 7) (R 7) [12,96,33,80,384] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,384] 13 (by decide) (choices 1) [1,2,128] r33135 c33135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16808
  · exact u16809
  · exact u16810

def b33136 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 98 37 137 82 434 466 402 402), lower := (rows 13 98 37 137 82 32 64 128 256), losses := [] }

theorem u33136 : Upper (D 7) (R 7) [12,96,33,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33137 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 137 146 370 338 466 338), lower := (rows 13 98 37 137 146 32 64 128 256), losses := [] }

theorem u33137 : Upper (D 7) (R 7) [12,96,33,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33138 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 137 208 306 338 402 274), lower := (rows 13 98 37 137 208 32 64 128 256), losses := [] }

theorem u33138 : Upper (D 7) (R 7) [12,96,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33139 : Route 9 := (fun mask => (mask,id))

def c33139 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33139 : Upper (D 7) (R 7) [12,96,33,129,258] 13 := by
  apply FastRouting.sound _ _ [12,96,33,129,258] 13 (by decide) (choices 1) [2,16,64,128] r33139 c33139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16811
  · exact u16812
  · exact u16813
  · exact u16814

def r33140 : Route 9 := (fun mask => (mask,id))

def c33140 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33140 : Upper (D 7) (R 7) [12,96,33,129,320] 13 := by
  apply FastRouting.sound _ _ [12,96,33,129,320] 13 (by decide) (choices 1) [2,16,128] r33140 c33140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16815
  · exact u16816
  · exact u16817

def b33141 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 37 137 400 114 82 210 338), lower := (rows 13 98 37 137 400 32 64 128 256), losses := [] }

theorem u33141 : Upper (D 7) (R 7) [12,96,33,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33142 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 484, targets := 2 },{ cop := 4, region := 456, targets := 32 }], pairs := [(1,0),(2,1),(3,0),(3,5)], upper := (rows 13 98 37 138 19 496 464 464 464), lower := (rows 13 98 37 138 19 32 64 128 256), losses := [] }

theorem u33142 : Upper (D 7) (R 7) [12,96,33,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33143 : Route 9 := (fun mask => (mask,id))

def c33143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u33143 : Upper (D 7) (R 7) [12,96,33,130,65] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,65] 13 (by decide) (choices 1) [2,16,128,256] r33143 c33143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16818
  · exact u16819
  · exact u16820
  · exact u16821

def b33144 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 37 138 82 433 465 401 401), lower := (rows 13 98 37 138 82 32 64 128 256), losses := [] }

theorem u33144 : Upper (D 7) (R 7) [12,96,33,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33145 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 37 138 145 370 338 466 338), lower := (rows 13 98 37 138 145 32 64 128 256), losses := [] }

theorem u33145 : Upper (D 7) (R 7) [12,96,33,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33146 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 13 98 37 138 146 369 337 465 337), lower := (rows 13 98 37 138 146 32 64 128 256), losses := [] }

theorem u33146 : Upper (D 7) (R 7) [12,96,33,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33147 : Route 9 := (fun mask => (mask,id))

def c33147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33147 : Upper (D 7) (R 7) [12,96,33,130,192] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,192] 13 (by decide) (choices 1) [1,2,16,256] r33147 c33147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16822
  · exact u16823
  · exact u16824
  · exact u16825

def r33148 : Route 9 := (fun mask => (mask,id))

def c33148 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33148 : Upper (D 7) (R 7) [12,96,33,130,257] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,257] 13 (by decide) (choices 1) [2,16,64,128] r33148 c33148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16826
  · exact u16827
  · exact u16828
  · exact u16829

def r33149 : Route 9 := (fun mask => (mask,id))

def c33149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33149 : Upper (D 7) (R 7) [12,96,33,130,258] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,258] 13 (by decide) (choices 1) [1,16,64,128] r33149 c33149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16830
  · exact u16831
  · exact u16832
  · exact u16833

def r33150 : Route 9 := (fun mask => (mask,id))

def c33150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33150 : Upper (D 7) (R 7) [12,96,33,130,320] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,320] 13 (by decide) (choices 1) [1,2,16,128] r33150 c33150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16834
  · exact u16835
  · exact u16836
  · exact u16837

def r33151 : Route 9 := (fun mask => (mask,id))

def c33151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33151 : Upper (D 7) (R 7) [12,96,33,130,384] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130,384] 13 (by decide) (choices 1) [1,2,16,64] r33151 c33151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16838
  · exact u16839
  · exact u16840
  · exact u16841

def r33152 : Route 9 := (fun mask => (mask,id))

def c33152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33152 : Upper (D 7) (R 7) [12,96,33,144,3] 13 := by
  apply FastRouting.sound _ _ [12,96,33,144,3] 13 (by decide) (choices 1) [2,64,128,256] r33152 c33152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16842
  · exact u16843
  · exact u16844
  · exact u16845

def r33153 : Route 9 := (fun mask => (mask,id))

def c33153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33153 : Upper (D 7) (R 7) [12,96,33,144,65] 13 := by
  apply FastRouting.sound _ _ [12,96,33,144,65] 13 (by decide) (choices 1) [2,128,256] r33153 c33153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16846
  · exact u16847
  · exact u16848

def b33154 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 37 152 82 419 451 387 387), lower := (rows 13 98 37 152 82 32 64 128 256), losses := [] }

theorem u33154 : Upper (D 7) (R 7) [12,96,33,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33155 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 13 98 37 152 145 354 322 450 322), lower := (rows 13 98 37 152 145 32 64 128 256), losses := [] }

theorem u33155 : Upper (D 7) (R 7) [12,96,33,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33156 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 98 37 152 146 355 323 451 323), lower := (rows 13 98 37 152 146 32 64 128 256), losses := [] }

theorem u33156 : Upper (D 7) (R 7) [12,96,33,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33157 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 98 37 152 208 291 323 387 259), lower := (rows 13 98 37 152 208 32 64 128 256), losses := [] }

theorem u33157 : Upper (D 7) (R 7) [12,96,33,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33158 : Route 9 := (fun mask => (mask,id))

def c33158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33158 : Upper (D 7) (R 7) [12,96,33,144,257] 13 := by
  apply FastRouting.sound _ _ [12,96,33,144,257] 13 (by decide) (choices 1) [2,64,128] r33158 c33158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16849
  · exact u16850
  · exact u16851

def r33159 : Route 9 := (fun mask => (mask,id))

def c33159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33159 : Upper (D 7) (R 7) [12,96,33,144,258] 13 := by
  apply FastRouting.sound _ _ [12,96,33,144,258] 13 (by decide) (choices 1) [1,2,64,128] r33159 c33159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16852
  · exact u16853
  · exact u16854
  · exact u16855

def r33160 : Route 9 := (fun mask => (mask,id))

def c33160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33160 : Upper (D 7) (R 7) [12,96,33,144,320] 13 := by
  apply FastRouting.sound _ _ [12,96,33,144,320] 13 (by decide) (choices 1) [1,2,128] r33160 c33160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16856
  · exact u16857
  · exact u16858

def b33161 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 13 98 37 152 400 99 67 195 323), lower := (rows 13 98 37 152 400 32 64 128 256), losses := [] }

theorem u33161 : Upper (D 7) (R 7) [12,96,33,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33162 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 456, targets := 32 },{ cop := 4, region := 420, targets := 64 }], pairs := [(1,0),(2,6),(3,0),(3,5)], upper := (rows 13 98 37 200 19 434 466 402 402), lower := (rows 13 98 37 200 19 32 64 128 256), losses := [] }

theorem u33162 : Upper (D 7) (R 7) [12,96,33,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33163 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 37 200 145 306 338 402 274), lower := (rows 13 98 37 200 145 32 64 128 256), losses := [] }

theorem u33163 : Upper (D 7) (R 7) [12,96,33,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33164 : Route 9 := (fun mask => (mask,id))

def c33164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33164 : Upper (D 7) (R 7) [12,96,33,192,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192,130] 13 (by decide) (choices 1) [1,2,16,256] r33164 c33164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16859
  · exact u16860
  · exact u16861
  · exact u16862

def r33165 : Route 9 := (fun mask => (mask,id))

def c33165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33165 : Upper (D 7) (R 7) [12,96,33,192,257] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192,257] 13 (by decide) (choices 1) [2,16,128] r33165 c33165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16863
  · exact u16864
  · exact u16865

def r33166 : Route 9 := (fun mask => (mask,id))

def c33166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33166 : Upper (D 7) (R 7) [12,96,33,192,258] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192,258] 13 (by decide) (choices 1) [1,2,16,128] r33166 c33166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16866
  · exact u16867
  · exact u16868
  · exact u16869

def r33167 : Route 9 := (fun mask => (mask,id))

def c33167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33167 : Upper (D 7) (R 7) [12,96,33,192,384] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192,384] 13 (by decide) (choices 1) [1,2,16] r33167 c33167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16870
  · exact u16871
  · exact u16872

def b33168 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 98 37 265 82 178 210 146 402), lower := (rows 13 98 37 265 82 32 64 128 256), losses := [] }

theorem u33168 : Upper (D 7) (R 7) [12,96,33,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33169 : Route 9 := (fun mask => (mask,id))

def c33169 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33169 : Upper (D 7) (R 7) [12,96,33,257,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,257,130] 13 (by decide) (choices 1) [2,16,64,128] r33169 c33169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16873
  · exact u16874
  · exact u16875
  · exact u16876

def r33170 : Route 9 := (fun mask => (mask,id))

def c33170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33170 : Upper (D 7) (R 7) [12,96,33,257,192] 13 := by
  apply FastRouting.sound _ _ [12,96,33,257,192] 13 (by decide) (choices 1) [2,16,128] r33170 c33170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16877
  · exact u16878
  · exact u16879

def b33171 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 228, targets := 2 },{ cop := 4, region := 456, targets := 32 }], pairs := [(1,0),(2,1),(3,0),(3,5)], upper := (rows 13 98 37 266 19 240 208 208 464), lower := (rows 13 98 37 266 19 32 64 128 256), losses := [] }

theorem u33171 : Upper (D 7) (R 7) [12,96,33,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33172 : Route 9 := (fun mask => (mask,id))

def c33172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33172 : Upper (D 7) (R 7) [12,96,33,258,65] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,65] 13 (by decide) (choices 1) [2,16,128] r33172 c33172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16880
  · exact u16881
  · exact u16882

def b33173 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 37 266 82 177 209 145 401), lower := (rows 13 98 37 266 82 32 64 128 256), losses := [] }

theorem u33173 : Upper (D 7) (R 7) [12,96,33,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33174 : Route 9 := (fun mask => (mask,id))

def c33174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33174 : Upper (D 7) (R 7) [12,96,33,258,129] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,129] 13 (by decide) (choices 1) [2,16,64,128] r33174 c33174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16883
  · exact u16884
  · exact u16885
  · exact u16886

def r33175 : Route 9 := (fun mask => (mask,id))

def c33175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33175 : Upper (D 7) (R 7) [12,96,33,258,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,130] 13 (by decide) (choices 1) [1,16,64,128] r33175 c33175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16887
  · exact u16888
  · exact u16889
  · exact u16890

def r33176 : Route 9 := (fun mask => (mask,id))

def c33176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33176 : Upper (D 7) (R 7) [12,96,33,258,192] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258,192] 13 (by decide) (choices 1) [1,2,16,128] r33176 c33176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16891
  · exact u16892
  · exact u16893
  · exact u16894

def r33177 : Route 9 := (fun mask => (mask,id))

def c33177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33177 : Upper (D 7) (R 7) [12,96,33,272,3] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272,3] 13 (by decide) (choices 1) [2,64,128] r33177 c33177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16895
  · exact u16896
  · exact u16897

def r33178 : Route 9 := (fun mask => (mask,id))

def c33178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33178 : Upper (D 7) (R 7) [12,96,33,272,65] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272,65] 13 (by decide) (choices 1) [2,128] r33178 c33178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16898
  · exact u16899

def b33179 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 37 280 82 163 195 131 387), lower := (rows 13 98 37 280 82 32 64 128 256), losses := [] }

theorem u33179 : Upper (D 7) (R 7) [12,96,33,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33179
end Delivery.IrregularNine14.P07
