import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0437
import IrregularNine14P07C0438

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38760 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 37 266 22 74 176 225 193 193 449), lower := (rows 37 266 22 74 176 32 64 128 256), losses := [] }

theorem u38760 : Upper (D 7) (R 7) [36,264,18,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38761 : Route 9 := (fun mask => (mask,id))

def c38761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38761 : Upper (D 7) (R 7) [36,264,18,66,192] 13 := by
  apply FastRouting.sound _ _ [36,264,18,66,192] 13 (by decide) (choices 1) [1,128] r38761 c38761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26243
  · exact u26244

def b38762 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 193 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 37 266 22 104 19 225 193 193 449), lower := (rows 37 266 22 104 19 32 64 128 256), losses := [] }

theorem u38762 : Upper (D 7) (R 7) [36,264,18,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38763 : Route 9 := (fun mask => (mask,id))

def c38763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38763 : Upper (D 7) (R 7) [36,264,18,96,65] 13 := by
  apply FastRouting.sound _ _ [36,264,18,96,65] 13 (by decide) (choices 1) [1,2,128] r38763 c38763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26245
  · exact u26246
  · exact u26247

def b38764 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 22 104 82 161 193 129 385), lower := (rows 37 266 22 104 82 32 64 128 256), losses := [] }

theorem u38764 : Upper (D 7) (R 7) [36,264,18,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38765 : Route 9 := (fun mask => (mask,id))

def c38765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38765 : Upper (D 7) (R 7) [36,264,18,96,129] 13 := by
  apply FastRouting.sound _ _ [36,264,18,96,129] 13 (by decide) (choices 1) [1,2,64,128] r38765 c38765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26248
  · exact u26249
  · exact u26250
  · exact u26251

def b38766 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 266 22 104 146 225 193 193 449), lower := (rows 37 266 22 104 146 32 64 128 256), losses := [] }

theorem u38766 : Upper (D 7) (R 7) [36,264,18,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38767 : Route 9 := (fun mask => (mask,id))

def c38767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38767 : Upper (D 7) (R 7) [36,264,18,96,192] 13 := by
  apply FastRouting.sound _ _ [36,264,18,96,192] 13 (by decide) (choices 1) [1,2,128] r38767 c38767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26252
  · exact u26253
  · exact u26254

def b38768 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 266 22 200 19 225 225 225 481), lower := (rows 37 266 22 200 19 32 64 128 256), losses := [] }

theorem u38768 : Upper (D 7) (R 7) [36,264,18,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38769 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 22 200 49 227 195 195 451), lower := (rows 37 266 22 200 49 32 64 128 256), losses := [] }

theorem u38769 : Upper (D 7) (R 7) [36,264,18,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38770 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 22 200 50 225 193 193 449), lower := (rows 37 266 22 200 50 32 64 128 256), losses := [] }

theorem u38770 : Upper (D 7) (R 7) [36,264,18,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38771 : Route 9 := (fun mask => (mask,id))

def c38771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38771 : Upper (D 7) (R 7) [36,264,18,192,65] 13 := by
  apply FastRouting.sound _ _ [36,264,18,192,65] 13 (by decide) (choices 1) [1,2,128] r38771 c38771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26255
  · exact u26256
  · exact u26257

def b38772 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 22 200 82 161 225 161 417), lower := (rows 37 266 22 200 82 32 64 128 256), losses := [] }

theorem u38772 : Upper (D 7) (R 7) [36,264,18,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38773 : Route 9 := (fun mask => (mask,id))

def c38773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38773 : Upper (D 7) (R 7) [36,264,18,192,96] 13 := by
  apply FastRouting.sound _ _ [36,264,18,192,96] 13 (by decide) (choices 1) [1,2,128] r38773 c38773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26258
  · exact u26259
  · exact u26260

def b38774 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 266 22 200 208 35 99 163 291), lower := (rows 37 266 22 200 208 32 64 128 256), losses := [] }

theorem u38774 : Upper (D 7) (R 7) [36,264,18,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38775 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 69 11 50 240 208 208 464), lower := (rows 37 266 69 11 50 32 64 128 256), losses := [] }

theorem u38775 : Upper (D 7) (R 7) [36,264,65,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38776 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 69 11 82 176 240 176 432), lower := (rows 37 266 69 11 82 32 64 128 256), losses := [] }

theorem u38776 : Upper (D 7) (R 7) [36,264,65,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38777 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 11 112 178 210 146 402), lower := (rows 37 266 69 11 112 32 64 128 256), losses := [] }

theorem u38777 : Upper (D 7) (R 7) [36,264,65,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38778 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 69 11 146 240 240 240 496), lower := (rows 37 266 69 11 146 32 64 128 256), losses := [] }

theorem u38778 : Upper (D 7) (R 7) [36,264,65,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38779 : Route 9 := (fun mask => (mask,id))

def c38779 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38779 : Upper (D 7) (R 7) [36,264,65,3,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,3,160] 13 (by decide) (choices 1) [2,16,64,128] r38779 c38779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26261
  · exact u26262
  · exact u26263
  · exact u26264

def r38780 : Route 9 := (fun mask => (mask,id))

def c38780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38780 : Upper (D 7) (R 7) [36,264,65,3,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,3,192] 13 (by decide) (choices 1) [2,16,128] r38780 c38780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26265
  · exact u26266
  · exact u26267

def b38781 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 266 69 25 50 226 194 194 450), lower := (rows 37 266 69 25 50 32 64 128 256), losses := [] }

theorem u38781 : Upper (D 7) (R 7) [36,264,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38782 : Route 9 := (fun mask => (mask,id))

def c38782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38782 : Upper (D 7) (R 7) [36,264,65,17,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,17,66] 13 (by decide) (choices 1) [2,128] r38782 c38782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26268
  · exact u26269

def b38783 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 25 112 162 194 130 386), lower := (rows 37 266 69 25 112 32 64 128 256), losses := [] }

theorem u38783 : Upper (D 7) (R 7) [36,264,65,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38784 : Route 9 := (fun mask => (mask,id))

def c38784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38784 : Upper (D 7) (R 7) [36,264,65,17,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,17,130] 13 (by decide) (choices 1) [2,64,128] r38784 c38784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26270
  · exact u26271
  · exact u26272

def b38785 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 266 69 25 176 226 194 194 450), lower := (rows 37 266 69 25 176 32 64 128 256), losses := [] }

theorem u38785 : Upper (D 7) (R 7) [36,264,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38786 : Route 9 := (fun mask => (mask,id))

def c38786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38786 : Upper (D 7) (R 7) [36,264,65,17,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,17,192] 13 (by decide) (choices 1) [2,128] r38786 c38786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26273
  · exact u26274

def b38787 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 1, region := 229, targets := 2 }], pairs := [(0,1),(3,5),(3,6),(3,7)], upper := (rows 37 266 69 26 19 224 224 224 480), lower := (rows 37 266 69 26 19 32 64 128 256), losses := [] }

theorem u38787 : Upper (D 7) (R 7) [36,264,65,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38788 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 69 26 49 226 194 194 450), lower := (rows 37 266 69 26 49 32 64 128 256), losses := [] }

theorem u38788 : Upper (D 7) (R 7) [36,264,65,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38789 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 266 69 26 50 225 193 193 449), lower := (rows 37 266 69 26 50 32 64 128 256), losses := [] }

theorem u38789 : Upper (D 7) (R 7) [36,264,65,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38790 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 266 69 26 81 162 226 162 418), lower := (rows 37 266 69 26 81 32 64 128 256), losses := [] }

theorem u38790 : Upper (D 7) (R 7) [36,264,65,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38791 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 266 69 26 82 161 225 161 417), lower := (rows 37 266 69 26 82 32 64 128 256), losses := [] }

theorem u38791 : Upper (D 7) (R 7) [36,264,65,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38792 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 26 112 163 195 131 387), lower := (rows 37 266 69 26 112 32 64 128 256), losses := [] }

theorem u38792 : Upper (D 7) (R 7) [36,264,65,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38793 : Route 9 := (fun mask => (mask,id))

def c38793 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38793 : Upper (D 7) (R 7) [36,264,65,18,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,18,129] 13 (by decide) (choices 1) [2,64,128] r38793 c38793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26275
  · exact u26276
  · exact u26277

def b38794 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 266 69 26 146 225 225 225 481), lower := (rows 37 266 69 26 146 32 64 128 256), losses := [] }

theorem u38794 : Upper (D 7) (R 7) [36,264,65,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38795 : Route 9 := (fun mask => (mask,id))

def c38795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38795 : Upper (D 7) (R 7) [36,264,65,18,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,18,160] 13 (by decide) (choices 1) [1,2,64,128] r38795 c38795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26278
  · exact u26279
  · exact u26280
  · exact u26281

def r38796 : Route 9 := (fun mask => (mask,id))

def c38796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38796 : Upper (D 7) (R 7) [36,264,65,18,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,18,192] 13 (by decide) (choices 1) [1,2,128] r38796 c38796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26282
  · exact u26283
  · exact u26284

def b38797 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 69 42 19 240 208 208 464), lower := (rows 37 266 69 42 19 32 64 128 256), losses := [] }

theorem u38797 : Upper (D 7) (R 7) [36,264,65,34,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38798 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 266 69 42 81 178 210 146 402), lower := (rows 37 266 69 42 81 32 64 128 256), losses := [] }

theorem u38798 : Upper (D 7) (R 7) [36,264,65,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38799 : Route 9 := (fun mask => (mask,id))

def c38799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38799 : Upper (D 7) (R 7) [36,264,65,34,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34,66] 13 (by decide) (choices 1) [1,16,128] r38799 c38799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26285
  · exact u26286
  · exact u26287

def r38800 : Route 9 := (fun mask => (mask,id))

def c38800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38800 : Upper (D 7) (R 7) [36,264,65,34,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34,129] 13 (by decide) (choices 1) [2,16,64,128] r38800 c38800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26288
  · exact u26289
  · exact u26290
  · exact u26291

def r38801 : Route 9 := (fun mask => (mask,id))

def c38801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38801 : Upper (D 7) (R 7) [36,264,65,34,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34,130] 13 (by decide) (choices 1) [1,16,64,128] r38801 c38801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26292
  · exact u26293
  · exact u26294
  · exact u26295

def r38802 : Route 9 := (fun mask => (mask,id))

def c38802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38802 : Upper (D 7) (R 7) [36,264,65,34,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34,192] 13 (by decide) (choices 1) [1,2,16,128] r38802 c38802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26296
  · exact u26297
  · exact u26298
  · exact u26299

def b38803 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 3, region := 450, targets := 32 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(3,0)], upper := (rows 37 266 69 56 19 226 194 194 450), lower := (rows 37 266 69 56 19 32 64 128 256), losses := [] }

theorem u38803 : Upper (D 7) (R 7) [36,264,65,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38804 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 37 266 69 56 81 162 194 130 386), lower := (rows 37 266 69 56 81 32 64 128 256), losses := [] }

theorem u38804 : Upper (D 7) (R 7) [36,264,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38805 : Route 9 := (fun mask => (mask,id))

def c38805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38805 : Upper (D 7) (R 7) [36,264,65,48,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,48,66] 13 (by decide) (choices 1) [1,2,128] r38805 c38805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26300
  · exact u26301
  · exact u26302

def r38806 : Route 9 := (fun mask => (mask,id))

def c38806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38806 : Upper (D 7) (R 7) [36,264,65,48,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,48,129] 13 (by decide) (choices 1) [2,64,128] r38806 c38806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26303
  · exact u26304
  · exact u26305

def r38807 : Route 9 := (fun mask => (mask,id))

def c38807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38807 : Upper (D 7) (R 7) [36,264,65,48,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,48,130] 13 (by decide) (choices 1) [1,2,64,128] r38807 c38807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26306
  · exact u26307
  · exact u26308
  · exact u26309

def r38808 : Route 9 := (fun mask => (mask,id))

def c38808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38808 : Upper (D 7) (R 7) [36,264,65,48,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,48,192] 13 (by decide) (choices 1) [1,2,128] r38808 c38808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26310
  · exact u26311
  · exact u26312

def b38809 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 69 74 19 176 240 176 432), lower := (rows 37 266 69 74 19 32 64 128 256), losses := [] }

theorem u38809 : Upper (D 7) (R 7) [36,264,65,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38810 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 69 74 49 178 210 146 402), lower := (rows 37 266 69 74 49 32 64 128 256), losses := [] }

theorem u38810 : Upper (D 7) (R 7) [36,264,65,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38811 : Route 9 := (fun mask => (mask,id))

def c38811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38811 : Upper (D 7) (R 7) [36,264,65,66,34] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,34] 13 (by decide) (choices 1) [1,16,128] r38811 c38811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26313
  · exact u26314
  · exact u26315

def r38812 : Route 9 := (fun mask => (mask,id))

def c38812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38812 : Upper (D 7) (R 7) [36,264,65,66,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,129] 13 (by decide) (choices 1) [2,16,128] r38812 c38812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26316
  · exact u26317
  · exact u26318

def r38813 : Route 9 := (fun mask => (mask,id))

def c38813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38813 : Upper (D 7) (R 7) [36,264,65,66,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,130] 13 (by decide) (choices 1) [1,16,128] r38813 c38813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26319
  · exact u26320
  · exact u26321

def r38814 : Route 9 := (fun mask => (mask,id))

def c38814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38814 : Upper (D 7) (R 7) [36,264,65,66,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66,160] 13 (by decide) (choices 1) [1,2,16,128] r38814 c38814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26322
  · exact u26323
  · exact u26324
  · exact u26325

def r38815 : Route 9 := (fun mask => (mask,id))

def c38815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38815 : Upper (D 7) (R 7) [36,264,65,80,3] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,3] 13 (by decide) (choices 1) [2,128] r38815 c38815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26326
  · exact u26327

def b38816 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 69 88 49 162 194 130 386), lower := (rows 37 266 69 88 49 32 64 128 256), losses := [] }

theorem u38816 : Upper (D 7) (R 7) [36,264,65,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38817 : Route 9 := (fun mask => (mask,id))

def c38817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38817 : Upper (D 7) (R 7) [36,264,65,80,34] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,34] 13 (by decide) (choices 1) [1,2,128] r38817 c38817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26328
  · exact u26329
  · exact u26330

def r38818 : Route 9 := (fun mask => (mask,id))

def c38818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38818 : Upper (D 7) (R 7) [36,264,65,80,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,129] 13 (by decide) (choices 1) [2,128] r38818 c38818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26331
  · exact u26332

def r38819 : Route 9 := (fun mask => (mask,id))

def c38819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38819 : Upper (D 7) (R 7) [36,264,65,80,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80,130] 13 (by decide) (choices 1) [1,2,128] r38819 c38819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26333
  · exact u26334
  · exact u26335

#print axioms u38819
end Delivery.IrregularNine14.P07
