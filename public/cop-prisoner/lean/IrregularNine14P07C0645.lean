import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0436
import IrregularNine14P07C0437

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38700 : Route 9 := (fun mask => (mask,id))

def c38700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38700 : Upper (D 7) (R 7) [36,264,3,192,66] 13 := by
  apply FastRouting.sound _ _ [36,264,3,192,66] 13 (by decide) (choices 1) [1,16,128] r38700 c38700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26180
  · exact u26181
  · exact u26182

def r38701 : Route 9 := (fun mask => (mask,id))

def c38701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38701 : Upper (D 7) (R 7) [36,264,3,192,96] 13 := by
  apply FastRouting.sound _ _ [36,264,3,192,96] 13 (by decide) (choices 1) [1,2,16,128] r38701 c38701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26183
  · exact u26184
  · exact u26185
  · exact u26186

def b38702 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 7 200 208 51 115 179 307), lower := (rows 37 266 7 200 208 32 64 128 256), losses := [] }

theorem u38702 : Upper (D 7) (R 7) [36,264,3,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38703 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 11 50 224 192 192 448), lower := (rows 37 266 21 11 50 32 64 128 256), losses := [] }

theorem u38703 : Upper (D 7) (R 7) [36,264,17,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38704 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 21 11 82 224 224 224 480), lower := (rows 37 266 21 11 82 32 64 128 256), losses := [] }

theorem u38704 : Upper (D 7) (R 7) [36,264,17,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38705 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 11 112 226 194 194 450), lower := (rows 37 266 21 11 112 32 64 128 256), losses := [] }

theorem u38705 : Upper (D 7) (R 7) [36,264,17,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38706 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38706 : Upper (D 7) (R 7) [36,264,17,3,192] 13 := by
  apply FastRouting.sound _ _ [36,264,17,3,192] 13 (by decide) (choices 1) [2,64] r38706 c38706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26187
  · exact u26188

def b38707 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 42 19 224 192 192 448), lower := (rows 37 266 21 42 19 32 64 128 256), losses := [] }

theorem u38707 : Upper (D 7) (R 7) [36,264,17,34,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38708 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 266 21 42 81 226 194 194 450), lower := (rows 37 266 21 42 81 32 64 128 256), losses := [] }

theorem u38708 : Upper (D 7) (R 7) [36,264,17,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38709 : Route 9 := (fun mask => (mask,id))

def c38709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38709 : Upper (D 7) (R 7) [36,264,17,34,66] 13 := by
  apply FastRouting.sound _ _ [36,264,17,34,66] 13 (by decide) (choices 1) [1,64,128] r38709 c38709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26189
  · exact u26190
  · exact u26191

def r38710 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38710 : Upper (D 7) (R 7) [36,264,17,34,192] 13 := by
  apply FastRouting.sound _ _ [36,264,17,34,192] 13 (by decide) (choices 1) [1,2,64] r38710 c38710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26192
  · exact u26193
  · exact u26194

def b38711 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 73 50 226 194 194 450), lower := (rows 37 266 21 73 50 32 64 128 256), losses := [] }

theorem u38711 : Upper (D 7) (R 7) [36,264,17,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38712 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 266 21 73 82 162 226 162 418), lower := (rows 37 266 21 73 82 32 64 128 256), losses := [] }

theorem u38712 : Upper (D 7) (R 7) [36,264,17,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38713 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 21 73 112 162 194 130 386), lower := (rows 37 266 21 73 112 32 64 128 256), losses := [] }

theorem u38713 : Upper (D 7) (R 7) [36,264,17,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38714 : Route 9 := (fun mask => (mask,id))

def c38714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38714 : Upper (D 7) (R 7) [36,264,17,65,130] 13 := by
  apply FastRouting.sound _ _ [36,264,17,65,130] 13 (by decide) (choices 1) [2,64,128] r38714 c38714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26195
  · exact u26196
  · exact u26197

def b38715 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 73 176 226 194 194 450), lower := (rows 37 266 21 73 176 32 64 128 256), losses := [] }

theorem u38715 : Upper (D 7) (R 7) [36,264,17,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38716 : Route 9 := (fun mask => (mask,id))

def c38716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38716 : Upper (D 7) (R 7) [36,264,17,65,192] 13 := by
  apply FastRouting.sound _ _ [36,264,17,65,192] 13 (by decide) (choices 1) [2,128] r38716 c38716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26198
  · exact u26199

def b38717 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 0, region := 458, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 37 266 21 74 19 224 224 224 480), lower := (rows 37 266 21 74 19 32 64 128 256), losses := [] }

theorem u38717 : Upper (D 7) (R 7) [36,264,17,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38718 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 21, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 74 49 226 194 194 450), lower := (rows 37 266 21 74 49 32 64 128 256), losses := [] }

theorem u38718 : Upper (D 7) (R 7) [36,264,17,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38719 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 21 74 50 225 193 193 449), lower := (rows 37 266 21 74 50 32 64 128 256), losses := [] }

theorem u38719 : Upper (D 7) (R 7) [36,264,17,66,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38720 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 266 21 74 81 162 226 162 418), lower := (rows 37 266 21 74 81 32 64 128 256), losses := [] }

theorem u38720 : Upper (D 7) (R 7) [36,264,17,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38721 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 37 266 21 74 82 161 225 161 417), lower := (rows 37 266 21 74 82 32 64 128 256), losses := [] }

theorem u38721 : Upper (D 7) (R 7) [36,264,17,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38722 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 74 112 163 195 131 387), lower := (rows 37 266 21 74 112 32 64 128 256), losses := [] }

theorem u38722 : Upper (D 7) (R 7) [36,264,17,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38723 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 266 21 74 145 226 226 226 482), lower := (rows 37 266 21 74 145 32 64 128 256), losses := [] }

theorem u38723 : Upper (D 7) (R 7) [36,264,17,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38724 : Route 9 := (fun mask => (mask,id))

def c38724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38724 : Upper (D 7) (R 7) [36,264,17,66,130] 13 := by
  apply FastRouting.sound _ _ [36,264,17,66,130] 13 (by decide) (choices 1) [1,64,128] r38724 c38724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26200
  · exact u26201
  · exact u26202

def b38725 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 74 176 227 195 195 451), lower := (rows 37 266 21 74 176 32 64 128 256), losses := [] }

theorem u38725 : Upper (D 7) (R 7) [36,264,17,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38726 : Route 9 := (fun mask => (mask,id))

def c38726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38726 : Upper (D 7) (R 7) [36,264,17,66,192] 13 := by
  apply FastRouting.sound _ _ [36,264,17,66,192] 13 (by decide) (choices 1) [1,2,128] r38726 c38726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26203
  · exact u26204
  · exact u26205

def b38727 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 37 266 21 104 19 226 194 194 450), lower := (rows 37 266 21 104 19 32 64 128 256), losses := [] }

theorem u38727 : Upper (D 7) (R 7) [36,264,17,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38728 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 21, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 21 104 81 162 194 130 386), lower := (rows 37 266 21 104 81 32 64 128 256), losses := [] }

theorem u38728 : Upper (D 7) (R 7) [36,264,17,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38729 : Route 9 := (fun mask => (mask,id))

def c38729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38729 : Upper (D 7) (R 7) [36,264,17,96,66] 13 := by
  apply FastRouting.sound _ _ [36,264,17,96,66] 13 (by decide) (choices 1) [1,2,128] r38729 c38729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26206
  · exact u26207
  · exact u26208

def b38730 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 266 21 104 145 226 194 194 450), lower := (rows 37 266 21 104 145 32 64 128 256), losses := [] }

theorem u38730 : Upper (D 7) (R 7) [36,264,17,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38731 : Route 9 := (fun mask => (mask,id))

def c38731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38731 : Upper (D 7) (R 7) [36,264,17,96,130] 13 := by
  apply FastRouting.sound _ _ [36,264,17,96,130] 13 (by decide) (choices 1) [1,2,64,128] r38731 c38731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26209
  · exact u26210
  · exact u26211
  · exact u26212

def r38732 : Route 9 := (fun mask => (mask,id))

def c38732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38732 : Upper (D 7) (R 7) [36,264,17,96,192] 13 := by
  apply FastRouting.sound _ _ [36,264,17,96,192] 13 (by decide) (choices 1) [1,2,128] r38732 c38732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26213
  · exact u26214
  · exact u26215

def b38733 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 266 21 200 19 226 226 226 482), lower := (rows 37 266 21 200 19 32 64 128 256), losses := [] }

theorem u38733 : Upper (D 7) (R 7) [36,264,17,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38734 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 21, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 200 49 226 194 194 450), lower := (rows 37 266 21 200 49 32 64 128 256), losses := [] }

theorem u38734 : Upper (D 7) (R 7) [36,264,17,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38735 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 200 50 227 195 195 451), lower := (rows 37 266 21 200 50 32 64 128 256), losses := [] }

theorem u38735 : Upper (D 7) (R 7) [36,264,17,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38736 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 266 21 200 81 162 226 162 418), lower := (rows 37 266 21 200 81 32 64 128 256), losses := [] }

theorem u38736 : Upper (D 7) (R 7) [36,264,17,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38737 : Route 9 := (fun mask => (mask,id))

def c38737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38737 : Upper (D 7) (R 7) [36,264,17,192,66] 13 := by
  apply FastRouting.sound _ _ [36,264,17,192,66] 13 (by decide) (choices 1) [1,2,128] r38737 c38737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26216
  · exact u26217
  · exact u26218

def b38738 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 21 200 112 163 195 131 387), lower := (rows 37 266 21 200 112 32 64 128 256), losses := [] }

theorem u38738 : Upper (D 7) (R 7) [36,264,17,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38739 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 21 200 208 35 99 163 291), lower := (rows 37 266 21 200 208 32 64 128 256), losses := [] }

theorem u38739 : Upper (D 7) (R 7) [36,264,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38740 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 266 22 11 49 224 192 192 448), lower := (rows 37 266 22 11 49 32 64 128 256), losses := [] }

theorem u38740 : Upper (D 7) (R 7) [36,264,18,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38741 : Route 9 := (fun mask => (mask,id))

def c38741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38741 : Upper (D 7) (R 7) [36,264,18,3,65] 13 := by
  apply FastRouting.sound _ _ [36,264,18,3,65] 13 (by decide) (choices 1) [64,128] r38741 c38741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26219
  · exact u26220

def b38742 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 266 22 11 112 225 193 193 449), lower := (rows 37 266 22 11 112 32 64 128 256), losses := [] }

theorem u38742 : Upper (D 7) (R 7) [36,264,18,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38743 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38743 : Upper (D 7) (R 7) [36,264,18,3,192] 13 := by
  apply FastRouting.sound _ _ [36,264,18,3,192] 13 (by decide) (choices 1) [1,64] r38743 c38743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26221
  · exact u26222

def r38744 : Route 9 := (fun mask => (mask,id))

def c38744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38744 : Upper (D 7) (R 7) [36,264,18,34,65] 13 := by
  apply FastRouting.sound _ _ [36,264,18,34,65] 13 (by decide) (choices 1) [1,64,128] r38744 c38744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26223
  · exact u26224
  · exact u26225

def r38745 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38745 : Upper (D 7) (R 7) [36,264,18,34,192] 13 := by
  apply FastRouting.sound _ _ [36,264,18,34,192] 13 (by decide) (choices 1) [1,64] r38745 c38745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26226
  · exact u26227

def b38746 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(2,5),(2,6),(2,7)], upper := (rows 37 266 22 73 19 224 224 224 480), lower := (rows 37 266 22 73 19 32 64 128 256), losses := [] }

theorem u38746 : Upper (D 7) (R 7) [36,264,18,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38747 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 22 73 49 226 194 194 450), lower := (rows 37 266 22 73 49 32 64 128 256), losses := [] }

theorem u38747 : Upper (D 7) (R 7) [36,264,18,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38748 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 22 73 50 225 193 193 449), lower := (rows 37 266 22 73 50 32 64 128 256), losses := [] }

theorem u38748 : Upper (D 7) (R 7) [36,264,18,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38749 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 37 266 22 73 81 162 226 162 418), lower := (rows 37 266 22 73 81 32 64 128 256), losses := [] }

theorem u38749 : Upper (D 7) (R 7) [36,264,18,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38750 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 22 73 82 161 225 161 417), lower := (rows 37 266 22 73 82 32 64 128 256), losses := [] }

theorem u38750 : Upper (D 7) (R 7) [36,264,18,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38751 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 161, targets := 64 },{ cop := 3, region := 386, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(3,5)], upper := (rows 37 266 22 73 112 163 195 131 387), lower := (rows 37 266 22 73 112 32 64 128 256), losses := [] }

theorem u38751 : Upper (D 7) (R 7) [36,264,18,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38752 : Route 9 := (fun mask => (mask,id))

def c38752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38752 : Upper (D 7) (R 7) [36,264,18,65,129] 13 := by
  apply FastRouting.sound _ _ [36,264,18,65,129] 13 (by decide) (choices 1) [2,64,128] r38752 c38752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26228
  · exact u26229
  · exact u26230

def b38753 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 266 22 73 146 225 225 225 481), lower := (rows 37 266 22 73 146 32 64 128 256), losses := [] }

theorem u38753 : Upper (D 7) (R 7) [36,264,18,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38754 : Route 9 := (fun mask => (mask,id))

def c38754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38754 : Upper (D 7) (R 7) [36,264,18,65,160] 13 := by
  apply FastRouting.sound _ _ [36,264,18,65,160] 13 (by decide) (choices 1) [1,2,64,128] r38754 c38754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26231
  · exact u26232
  · exact u26233
  · exact u26234

def r38755 : Route 9 := (fun mask => (mask,id))

def c38755 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38755 : Upper (D 7) (R 7) [36,264,18,65,192] 13 := by
  apply FastRouting.sound _ _ [36,264,18,65,192] 13 (by decide) (choices 1) [1,2,128] r38755 c38755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26235
  · exact u26236
  · exact u26237

def b38756 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 266 22 74 49 225 193 193 449), lower := (rows 37 266 22 74 49 32 64 128 256), losses := [] }

theorem u38756 : Upper (D 7) (R 7) [36,264,18,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38757 : Route 9 := (fun mask => (mask,id))

def c38757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38757 : Upper (D 7) (R 7) [36,264,18,66,65] 13 := by
  apply FastRouting.sound _ _ [36,264,18,66,65] 13 (by decide) (choices 1) [1,128] r38757 c38757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26238
  · exact u26239

def b38758 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 266 22 74 112 161 193 129 385), lower := (rows 37 266 22 74 112 32 64 128 256), losses := [] }

theorem u38758 : Upper (D 7) (R 7) [36,264,18,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38759 : Route 9 := (fun mask => (mask,id))

def c38759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38759 : Upper (D 7) (R 7) [36,264,18,66,129] 13 := by
  apply FastRouting.sound _ _ [36,264,18,66,129] 13 (by decide) (choices 1) [1,64,128] r38759 c38759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26240
  · exact u26241
  · exact u26242

#print axioms u38759
end Delivery.IrregularNine14.P07
