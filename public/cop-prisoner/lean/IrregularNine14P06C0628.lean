import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0385
import IrregularNine14P06C0386
import IrregularNine14P06C0387

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37680 : Route 9 := (fun mask => (mask,id))

def c37680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37680 : Upper (D 6) (R 6) [34,132,72,288,66] 13 := by
  apply FastRouting.sound _ _ [34,132,72,288,66] 13 (by decide) (choices 1) [1,4,16] r37680 c37680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23110
  · exact u23111
  · exact u23112

def b37681 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 76 296 84 51 83 147 275), lower := (rows 35 134 76 296 84 32 64 128 256), losses := [] }

theorem u37681 : Upper (D 6) (R 6) [34,132,72,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37682 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 21 376 344 472 344), lower := (rows 35 134 100 11 21 32 64 128 256), losses := [] }

theorem u37682 : Upper (D 6) (R 6) [34,132,96,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37683 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 25 372 340 468 340), lower := (rows 35 134 100 11 25 32 64 128 256), losses := [] }

theorem u37683 : Upper (D 6) (R 6) [34,132,96,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37684 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 28 369 337 465 337), lower := (rows 35 134 100 11 28 32 64 128 256), losses := [] }

theorem u37684 : Upper (D 6) (R 6) [34,132,96,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37685 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 81 316 348 412 284), lower := (rows 35 134 100 11 81 32 64 128 256), losses := [] }

theorem u37685 : Upper (D 6) (R 6) [34,132,96,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37686 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 88 309 341 405 277), lower := (rows 35 134 100 11 88 32 64 128 256), losses := [] }

theorem u37686 : Upper (D 6) (R 6) [34,132,96,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37687 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 273 124 92 220 348), lower := (rows 35 134 100 11 273 32 64 128 256), losses := [] }

theorem u37687 : Upper (D 6) (R 6) [34,132,96,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37688 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 276 121 89 217 345), lower := (rows 35 134 100 11 276 32 64 128 256), losses := [] }

theorem u37688 : Upper (D 6) (R 6) [34,132,96,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37689 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 280 117 85 213 341), lower := (rows 35 134 100 11 280 32 64 128 256), losses := [] }

theorem u37689 : Upper (D 6) (R 6) [34,132,96,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37690 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 11 336 61 93 157 285), lower := (rows 35 134 100 11 336 32 64 128 256), losses := [] }

theorem u37690 : Upper (D 6) (R 6) [34,132,96,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37691 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 100 13 25 370 338 466 338), lower := (rows 35 134 100 13 25 32 64 128 256), losses := [] }

theorem u37691 : Upper (D 6) (R 6) [34,132,96,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37692 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 353, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 134 100 13 26 369 337 465 337), lower := (rows 35 134 100 13 26 32 64 128 256), losses := [] }

theorem u37692 : Upper (D 6) (R 6) [34,132,96,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37693 : Route 9 := (fun mask => (mask,id))

def c37693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37693 : Upper (D 6) (R 6) [34,132,96,5,65] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5,65] 13 (by decide) (choices 1) [2,8,16,256] r37693 c37693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23113
  · exact u23114
  · exact u23115
  · exact u23116

def r37694 : Route 9 := (fun mask => (mask,id))

def c37694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37694 : Upper (D 6) (R 6) [34,132,96,5,66] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5,66] 13 (by decide) (choices 1) [1,8,16,256] r37694 c37694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23117
  · exact u23118
  · exact u23119
  · exact u23120

def r37695 : Route 9 := (fun mask => (mask,id))

def c37695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37695 : Upper (D 6) (R 6) [34,132,96,5,72] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5,72] 13 (by decide) (choices 1) [1,2,16,256] r37695 c37695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23121
  · exact u23122
  · exact u23123
  · exact u23124

def r37696 : Route 9 := (fun mask => (mask,id))

def c37696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37696 : Upper (D 6) (R 6) [34,132,96,5,257] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5,257] 13 (by decide) (choices 1) [2,8,16,64] r37696 c37696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23125
  · exact u23126
  · exact u23127
  · exact u23128

def r37697 : Route 9 := (fun mask => (mask,id))

def c37697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37697 : Upper (D 6) (R 6) [34,132,96,5,258] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5,258] 13 (by decide) (choices 1) [1,8,16,64] r37697 c37697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23129
  · exact u23130
  · exact u23131
  · exact u23132

def r37698 : Route 9 := (fun mask => (mask,id))

def c37698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37698 : Upper (D 6) (R 6) [34,132,96,5,264] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5,264] 13 (by decide) (choices 1) [1,2,16,64] r37698 c37698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23133
  · exact u23134
  · exact u23135
  · exact u23136

def r37699 : Route 9 := (fun mask => (mask,id))

def c37699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37699 : Upper (D 6) (R 6) [34,132,96,5,320] 13 := by
  apply FastRouting.sound _ _ [34,132,96,5,320] 13 (by decide) (choices 1) [1,2,8,16] r37699 c37699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23137
  · exact u23138
  · exact u23139
  · exact u23140

def b37700 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 14 25 369 337 465 337), lower := (rows 35 134 100 14 25 32 64 128 256), losses := [] }

theorem u37700 : Upper (D 6) (R 6) [34,132,96,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37701 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 14 81 313 345 409 281), lower := (rows 35 134 100 14 81 32 64 128 256), losses := [] }

theorem u37701 : Upper (D 6) (R 6) [34,132,96,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37702 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 14 88 305 337 401 273), lower := (rows 35 134 100 14 88 32 64 128 256), losses := [] }

theorem u37702 : Upper (D 6) (R 6) [34,132,96,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37703 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 14 273 121 89 217 345), lower := (rows 35 134 100 14 273 32 64 128 256), losses := [] }

theorem u37703 : Upper (D 6) (R 6) [34,132,96,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37704 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 14 280 113 81 209 337), lower := (rows 35 134 100 14 280 32 64 128 256), losses := [] }

theorem u37704 : Upper (D 6) (R 6) [34,132,96,6,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37705 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 14 336 57 89 153 281), lower := (rows 35 134 100 14 336 32 64 128 256), losses := [] }

theorem u37705 : Upper (D 6) (R 6) [34,132,96,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37706 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 100 25 25 358 326 454 326), lower := (rows 35 134 100 25 25 32 64 128 256), losses := [] }

theorem u37706 : Upper (D 6) (R 6) [34,132,96,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37707 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 100 25 26 357 325 453 325), lower := (rows 35 134 100 25 26 32 64 128 256), losses := [] }

theorem u37707 : Upper (D 6) (R 6) [34,132,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37708 : Route 9 := (fun mask => (mask,id))

def c37708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37708 : Upper (D 6) (R 6) [34,132,96,17,12] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,12] 13 (by decide) (choices 1) [1,2,64,256] r37708 c37708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23141
  · exact u23142
  · exact u23143
  · exact u23144

def b37709 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 100 25 81 302 334 398 270), lower := (rows 35 134 100 25 81 32 64 128 256), losses := [] }

theorem u37709 : Upper (D 6) (R 6) [34,132,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37710 : Route 9 := (fun mask => (mask,id))

def c37710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37710 : Upper (D 6) (R 6) [34,132,96,17,66] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,66] 13 (by decide) (choices 1) [1,4,8,256] r37710 c37710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23145
  · exact u23146
  · exact u23147
  · exact u23148

def b37711 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 100 25 84 299 331 395 267), lower := (rows 35 134 100 25 84 32 64 128 256), losses := [] }

theorem u37711 : Upper (D 6) (R 6) [34,132,96,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37712 : Route 9 := (fun mask => (mask,id))

def c37712 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37712 : Upper (D 6) (R 6) [34,132,96,17,72] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,72] 13 (by decide) (choices 1) [1,2,4,256] r37712 c37712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23149
  · exact u23150
  · exact u23151
  · exact u23152

def b37713 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 100 25 273 110 78 206 334), lower := (rows 35 134 100 25 273 32 64 128 256), losses := [] }

theorem u37713 : Upper (D 6) (R 6) [34,132,96,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37714 : Route 9 := (fun mask => (mask,id))

def c37714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37714 : Upper (D 6) (R 6) [34,132,96,17,258] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,258] 13 (by decide) (choices 1) [1,4,8,64] r37714 c37714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23153
  · exact u23154
  · exact u23155
  · exact u23156

def r37715 : Route 9 := (fun mask => (mask,id))

def c37715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37715 : Upper (D 6) (R 6) [34,132,96,17,260] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,260] 13 (by decide) (choices 1) [1,2,8,64] r37715 c37715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23157
  · exact u23158
  · exact u23159
  · exact u23160

def r37716 : Route 9 := (fun mask => (mask,id))

def c37716 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37716 : Upper (D 6) (R 6) [34,132,96,17,264] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,264] 13 (by decide) (choices 1) [1,2,4,64] r37716 c37716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23161
  · exact u23162
  · exact u23163
  · exact u23164

def r37717 : Route 9 := (fun mask => (mask,id))

def c37717 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37717 : Upper (D 6) (R 6) [34,132,96,17,320] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,320] 13 (by decide) (choices 1) [1,2,4,8] r37717 c37717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23165
  · exact u23166
  · exact u23167
  · exact u23168

def b37718 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 100 26 28 353 321 449 321), lower := (rows 35 134 100 26 28 32 64 128 256), losses := [] }

theorem u37718 : Upper (D 6) (R 6) [34,132,96,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37719 : Route 9 := (fun mask => (mask,id))

def c37719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37719 : Upper (D 6) (R 6) [34,132,96,18,65] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,65] 13 (by decide) (choices 1) [1,4,8,256] r37719 c37719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23169
  · exact u23170
  · exact u23171
  · exact u23172

def b37720 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 100 26 84 297 329 393 265), lower := (rows 35 134 100 26 84 32 64 128 256), losses := [] }

theorem u37720 : Upper (D 6) (R 6) [34,132,96,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37721 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 134 100 26 88 293 325 389 261), lower := (rows 35 134 100 26 88 32 64 128 256), losses := [] }

theorem u37721 : Upper (D 6) (R 6) [34,132,96,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37722 : Route 9 := (fun mask => (mask,id))

def c37722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37722 : Upper (D 6) (R 6) [34,132,96,18,257] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,257] 13 (by decide) (choices 1) [1,4,8,64] r37722 c37722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23173
  · exact u23174
  · exact u23175
  · exact u23176

def r37723 : Route 9 := (fun mask => (mask,id))

def c37723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37723 : Upper (D 6) (R 6) [34,132,96,18,260] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,260] 13 (by decide) (choices 1) [1,8,64] r37723 c37723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23177
  · exact u23178
  · exact u23179

def r37724 : Route 9 := (fun mask => (mask,id))

def c37724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37724 : Upper (D 6) (R 6) [34,132,96,18,264] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,264] 13 (by decide) (choices 1) [1,4,64] r37724 c37724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23180
  · exact u23181
  · exact u23182

def r37725 : Route 9 := (fun mask => (mask,id))

def c37725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37725 : Upper (D 6) (R 6) [34,132,96,18,320] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,320] 13 (by decide) (choices 1) [1,4,8] r37725 c37725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23183
  · exact u23184
  · exact u23185

def r37726 : Route 9 := (fun mask => (mask,id))

def c37726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37726 : Upper (D 6) (R 6) [34,132,96,20,65] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,65] 13 (by decide) (choices 1) [1,2,8,256] r37726 c37726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23186
  · exact u23187
  · exact u23188
  · exact u23189

def r37727 : Route 9 := (fun mask => (mask,id))

def c37727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37727 : Upper (D 6) (R 6) [34,132,96,20,66] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,66] 13 (by decide) (choices 1) [1,8,256] r37727 c37727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23190
  · exact u23191
  · exact u23192

def b37728 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 134 100 28 88 291 323 387 259), lower := (rows 35 134 100 28 88 32 64 128 256), losses := [] }

theorem u37728 : Upper (D 6) (R 6) [34,132,96,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37729 : Route 9 := (fun mask => (mask,id))

def c37729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37729 : Upper (D 6) (R 6) [34,132,96,20,257] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,257] 13 (by decide) (choices 1) [1,2,8,64] r37729 c37729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23193
  · exact u23194
  · exact u23195
  · exact u23196

def r37730 : Route 9 := (fun mask => (mask,id))

def c37730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37730 : Upper (D 6) (R 6) [34,132,96,20,258] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,258] 13 (by decide) (choices 1) [1,8,64] r37730 c37730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23197
  · exact u23198
  · exact u23199

def r37731 : Route 9 := (fun mask => (mask,id))

def c37731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37731 : Upper (D 6) (R 6) [34,132,96,20,264] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,264] 13 (by decide) (choices 1) [1,2,64] r37731 c37731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23200
  · exact u23201
  · exact u23202

def r37732 : Route 9 := (fun mask => (mask,id))

def c37732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37732 : Upper (D 6) (R 6) [34,132,96,20,320] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,320] 13 (by decide) (choices 1) [1,2,8] r37732 c37732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23203
  · exact u23204
  · exact u23205

def r37733 : Route 9 := (fun mask => (mask,id))

def c37733 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37733 : Upper (D 6) (R 6) [34,132,96,65,257] 13 := by
  apply FastRouting.sound _ _ [34,132,96,65,257] 13 (by decide) (choices 1) [2,4,8,16] r37733 c37733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23206
  · exact u23207
  · exact u23208
  · exact u23209

def r37734 : Route 9 := (fun mask => (mask,id))

def c37734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37734 : Upper (D 6) (R 6) [34,132,96,65,258] 13 := by
  apply FastRouting.sound _ _ [34,132,96,65,258] 13 (by decide) (choices 1) [1,4,8,16] r37734 c37734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23210
  · exact u23211
  · exact u23212
  · exact u23213

def r37735 : Route 9 := (fun mask => (mask,id))

def c37735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37735 : Upper (D 6) (R 6) [34,132,96,65,260] 13 := by
  apply FastRouting.sound _ _ [34,132,96,65,260] 13 (by decide) (choices 1) [1,2,8,16] r37735 c37735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23214
  · exact u23215
  · exact u23216
  · exact u23217

def r37736 : Route 9 := (fun mask => (mask,id))

def c37736 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37736 : Upper (D 6) (R 6) [34,132,96,65,264] 13 := by
  apply FastRouting.sound _ _ [34,132,96,65,264] 13 (by decide) (choices 1) [1,2,4,16] r37736 c37736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23218
  · exact u23219
  · exact u23220
  · exact u23221

def r37737 : Route 9 := (fun mask => (mask,id))

def c37737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37737 : Upper (D 6) (R 6) [34,132,96,66,257] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66,257] 13 (by decide) (choices 1) [1,4,8,16] r37737 c37737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23222
  · exact u23223
  · exact u23224
  · exact u23225

def r37738 : Route 9 := (fun mask => (mask,id))

def c37738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37738 : Upper (D 6) (R 6) [34,132,96,66,260] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66,260] 13 (by decide) (choices 1) [1,8,16] r37738 c37738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23226
  · exact u23227
  · exact u23228

def r37739 : Route 9 := (fun mask => (mask,id))

def c37739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37739 : Upper (D 6) (R 6) [34,132,96,66,264] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66,264] 13 (by decide) (choices 1) [1,4,16] r37739 c37739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23229
  · exact u23230
  · exact u23231

#print axioms u37739
end Delivery.IrregularNine14.P06
