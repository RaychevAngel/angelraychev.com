import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0037
import IrregularNine14P09C0038

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5700 : Route 9 := (fun mask => (mask,id))

def c5700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5700 : Upper (D 9) (R 9) [96,5,136,257,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,288,128] 13 (by decide) (choices 1) [2,16] r5700 c5700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2242
  · exact u2243

def r5701 : Route 9 := (fun mask => (mask,id))

def c5701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5701 : Upper (D 9) (R 9) [96,5,136,257,384,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,384,2] 13 (by decide) (choices 1) [16,32] r5701 c5701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2244
  · exact u2245

theorem m5702_2 : Upper (D 9) (R 9) [96,5,136,257,384,16,2] 13 :=
  permutation_upper _ _ _ [96,5,136,257,384,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2244

def r5702 : Route 9 := (fun mask => (mask,id))

def c5702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5702 : Upper (D 9) (R 9) [96,5,136,257,384,16] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,384,16] 13 (by decide) (choices 1) [2,32] r5702 c5702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5702_2
  · exact u2246

def b5703 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 400 96 114 178 306), lower := (rows 97 7 140 265 400 96 64 128 256), losses := [] }

theorem u5703 : Upper (D 9) (R 9) [96,5,136,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5703 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5704 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(3,7)], upper := (rows 97 7 140 266 145 48 352 480 352), lower := (rows 97 7 140 266 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 48 113 177 305), good := (rows 480 462 140 270 496 496 64 128 256) },{ target := 7, region := (rows 49 2 4 10 16 48 113 0 305), good := (rows 353 335 12 266 369 369 64 0 256) }] }

theorem u5704 : Upper (D 9) (R 9) [96,5,136,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5704 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5705 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 266 145 96 368 432 304), lower := (rows 97 7 140 266 145 96 64 128 256), losses := [] }

theorem u5705 : Upper (D 9) (R 9) [96,5,136,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5705 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5706_16 : Upper (D 9) (R 9) [96,5,136,258,129,256,16] 13 :=
  permutation_upper _ _ _ [96,5,136,258,129,16,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2247

theorem m5706_32 : Upper (D 9) (R 9) [96,5,136,258,129,256,32] 13 :=
  permutation_upper _ _ _ [96,5,136,258,129,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2248

def r5706 : Route 9 := (fun mask => (mask,id))

def c5706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5706 : Upper (D 9) (R 9) [96,5,136,258,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,129,256] 13 (by decide) (choices 1) [16,32] r5706 c5706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5706_16
  · exact m5706_32

def b5707 : PairBound 9 := { available := 336, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 7 140 266 176 33 336 464 336), lower := (rows 97 7 140 266 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 14 10 49 32 115 179 307), good := (rows 496 478 140 462 496 496 64 128 256) }] }

theorem u5707 : Upper (D 9) (R 9) [96,5,136,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5707 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5708 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 140 266 176 48 321 449 321), lower := (rows 97 7 140 266 176 48 64 128 256), losses := [] }

theorem u5708 : Upper (D 9) (R 9) [96,5,136,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5708 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5709 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 266 176 96 337 401 273), lower := (rows 97 7 140 266 176 96 64 128 256), losses := [] }

theorem u5709 : Upper (D 9) (R 9) [96,5,136,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5709 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5710 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 209, targets := 256 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(4,0),(4,6),(4,8)], upper := (rows 97 7 140 266 176 288 81 209 337), lower := (rows 97 7 140 266 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 64 128 256), good := (rows 96 22 188 298 176 288 64 128 288) },{ target := 6, region := (rows 1 2 4 8 20 296 0 128 256), good := (rows 33 23 188 298 176 288 0 128 288) }] }

theorem u5710 : Upper (D 9) (R 9) [96,5,136,258,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5710 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5711 : Route 9 := (fun mask => (mask,id))

def c5711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5711 : Upper (D 9) (R 9) [96,5,136,258,257,16] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,257,16] 13 (by decide) (choices 1) [32,128] r5711 c5711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2249
  · exact u2250

def b5712 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 266 273 96 240 176 432), lower := (rows 97 7 140 266 273 96 64 128 256), losses := [] }

theorem u5712 : Upper (D 9) (R 9) [96,5,136,258,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5712 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5713_16 : Upper (D 9) (R 9) [96,5,136,258,257,128,16] 13 :=
  permutation_upper _ _ _ [96,5,136,258,257,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2250

theorem m5713_32 : Upper (D 9) (R 9) [96,5,136,258,257,128,32] 13 :=
  permutation_upper _ _ _ [96,5,136,258,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2251

def r5713 : Route 9 := (fun mask => (mask,id))

def c5713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5713 : Upper (D 9) (R 9) [96,5,136,258,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,257,128] 13 (by decide) (choices 1) [16,32] r5713 c5713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5713_16
  · exact m5713_32

def b5714 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 7 140 266 304 33 208 208 464), lower := (rows 97 7 140 266 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 14 10 49 32 115 179 307), good := (rows 496 478 140 462 496 496 64 128 256) }] }

theorem u5714 : Upper (D 9) (R 9) [96,5,136,258,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5715 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 140 266 304 48 193 193 449), lower := (rows 97 7 140 266 304 48 64 128 256), losses := [] }

theorem u5715 : Upper (D 9) (R 9) [96,5,136,258,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5715 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5716 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 266 304 96 209 145 401), lower := (rows 97 7 140 266 304 96 64 128 256), losses := [] }

theorem u5716 : Upper (D 9) (R 9) [96,5,136,258,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5716 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5717 : Route 9 := (fun mask => (mask,id))

def c5717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5717 : Upper (D 9) (R 9) [96,5,136,258,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,288,128] 13 (by decide) (choices 1) [1,16] r5717 c5717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2252
  · exact u2253

def b5718 : PairBound 9 := { available := 112, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 7 140 266 400 33 112 240 368), lower := (rows 97 7 140 266 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 51 32 97 161 289), good := (rows 496 478 140 286 400 496 64 128 256) }] }

theorem u5718 : Upper (D 9) (R 9) [96,5,136,258,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5718 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5719_1 : Upper (D 9) (R 9) [96,5,136,258,384,16,1] 13 :=
  permutation_upper _ _ _ [96,5,136,258,384,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2254

def r5719 : Route 9 := (fun mask => (mask,id))

def c5719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5719 : Upper (D 9) (R 9) [96,5,136,258,384,16] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258,384,16] 13 (by decide) (choices 1) [1,32] r5719 c5719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5719_1
  · exact u2255

def b5720 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 266 400 96 113 177 305), lower := (rows 97 7 140 266 400 96 64 128 256), losses := [] }

theorem u5720 : Upper (D 9) (R 9) [96,5,136,258,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5720 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5721 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 460, targets := 33 },{ cop := 1, region := 48, targets := 64 }], pairs := [(2,0),(2,5),(3,0),(3,5),(4,6)], upper := (rows 97 7 140 280 50 33 448 448 448), lower := (rows 97 7 140 280 50 33 64 128 256), losses := [] }

theorem u5721 : Upper (D 9) (R 9) [96,5,136,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5721 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5722 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 280 50 96 449 385 385), lower := (rows 97 7 140 280 50 96 64 128 256), losses := [] }

theorem u5722 : Upper (D 9) (R 9) [96,5,136,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5722 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5723 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(3,7),(4,0)], upper := (rows 97 7 140 280 50 160 321 449 321), lower := (rows 97 7 140 280 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 96 54 172 280 50 160 64 160 256) },{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 449 455 140 284 478 128 64 128 256) }] }

theorem u5723 : Upper (D 9) (R 9) [96,5,136,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5723 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5724 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 193, targets := 256 }], pairs := [(0,8),(1,8),(2,5),(2,8),(3,5)], upper := (rows 97 7 140 280 50 288 193 193 449), lower := (rows 97 7 140 280 50 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 449 455 140 284 478 256 64 128 256) },{ target := 8, region := (rows 49 10 12 8 16 32 123 187 0), good := (rows 225 199 206 223 243 225 64 128 0) }] }

theorem u5724 : Upper (D 9) (R 9) [96,5,136,272,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5724 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5725 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 97 7 140 280 145 34 352 480 352), lower := (rows 97 7 140 280 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 34 99 163 291), good := (rows 480 486 140 284 476 482 64 128 256) }] }

theorem u5725 : Upper (D 9) (R 9) [96,5,136,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5725 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5726 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 280 145 96 354 418 290), lower := (rows 97 7 140 280 145 96 64 128 256), losses := [] }

theorem u5726 : Upper (D 9) (R 9) [96,5,136,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5726 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5727_2 : Upper (D 9) (R 9) [96,5,136,272,129,256,2] 13 :=
  permutation_upper _ _ _ [96,5,136,272,129,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2256

theorem m5727_32 : Upper (D 9) (R 9) [96,5,136,272,129,256,32] 13 :=
  permutation_upper _ _ _ [96,5,136,272,129,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2257

def r5727 : Route 9 := (fun mask => (mask,id))

def c5727 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5727 : Upper (D 9) (R 9) [96,5,136,272,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,129,256] 13 (by decide) (choices 1) [2,32] r5727 c5727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5727_2
  · exact m5727_32

def b5728 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(3,7)], upper := (rows 97 7 140 280 146 33 352 480 352), lower := (rows 97 7 140 280 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 22 10 18 32 97 161 289), good := (rows 480 478 140 284 158 480 64 128 256) }] }

theorem u5728 : Upper (D 9) (R 9) [96,5,136,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5728 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5729 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 280 146 96 353 417 289), lower := (rows 97 7 140 280 146 96 64 128 256), losses := [] }

theorem u5729 : Upper (D 9) (R 9) [96,5,136,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5729 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5730 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 361, targets := 128 },{ cop := 5, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,7),(4,8)], upper := (rows 97 7 140 280 146 288 97 225 353), lower := (rows 97 7 140 280 146 288 64 128 256), losses := [{ target := 8, region := (rows 33 2 4 8 18 32 97 161 0), good := (rows 225 215 140 24 146 225 64 128 0) }] }

theorem u5730 : Upper (D 9) (R 9) [96,5,136,272,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5730 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5731 : Route 9 := (fun mask => (mask,id))

def c5731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5731 : Upper (D 9) (R 9) [96,5,136,272,160,1] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,160,1] 13 (by decide) (choices 1) [2,256] r5731 c5731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2258
  · exact u2259

def r5732 : Route 9 := (fun mask => (mask,id))

def c5732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5732 : Upper (D 9) (R 9) [96,5,136,272,160,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,160,2] 13 (by decide) (choices 1) [1,256] r5732 c5732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2260
  · exact u2261

def b5733 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 280 176 96 323 387 259), lower := (rows 97 7 140 280 176 96 64 128 256), losses := [] }

theorem u5733 : Upper (D 9) (R 9) [96,5,136,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5733 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5734 : Route 9 := (fun mask => (mask,id))

def c5734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5734 : Upper (D 9) (R 9) [96,5,136,272,160,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,160,256] 13 (by decide) (choices 1) [1,2] r5734 c5734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2262
  · exact u2263

def b5735 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(4,0),(4,5)], upper := (rows 97 7 140 296 82 33 464 400 400), lower := (rows 97 7 140 296 82 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 144 272), good := (rows 33 39 140 296 446 33 0 128 256) }] }

theorem u5735 : Upper (D 9) (R 9) [96,5,136,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5735 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5736 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 140 296 82 48 449 385 385), lower := (rows 97 7 140 296 82 48 64 128 256), losses := [] }

theorem u5736 : Upper (D 9) (R 9) [96,5,136,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5736 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5737 : Route 9 := (fun mask => (mask,id))

def c5737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5737 : Upper (D 9) (R 9) [96,5,136,288,66,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,66,128] 13 (by decide) (choices 1) [1,16,256] r5737 c5737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2264
  · exact u2265
  · exact u2266

def b5738 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 7 140 296 82 288 209 145 401), lower := (rows 97 7 140 296 82 288 64 128 256), losses := [] }

theorem u5738 : Upper (D 9) (R 9) [96,5,136,288,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5738 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5739 : Route 9 := (fun mask => (mask,id))

def c5739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5739 : Upper (D 9) (R 9) [96,5,136,288,129,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,129,2] 13 (by decide) (choices 1) [16,256] r5739 c5739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2267
  · exact u2268

def r5740 : Route 9 := (fun mask => (mask,id))

def c5740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5740 : Upper (D 9) (R 9) [96,5,136,288,129,16] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,129,16] 13 (by decide) (choices 1) [2,256] r5740 c5740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2269
  · exact u2270

def b5741 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 296 145 96 338 402 274), lower := (rows 97 7 140 296 145 96 64 128 256), losses := [] }

theorem u5741 : Upper (D 9) (R 9) [96,5,136,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5741 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5742 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 7 140 296 145 288 82 210 338), lower := (rows 97 7 140 296 145 288 64 128 256), losses := [] }

theorem u5742 : Upper (D 9) (R 9) [96,5,136,288,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5742 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5743 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 7 140 296 146 33 336 464 336), lower := (rows 97 7 140 296 146 33 64 128 256), losses := [] }

theorem u5743 : Upper (D 9) (R 9) [96,5,136,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5743 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5744 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 1, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(3,7),(4,5)], upper := (rows 97 7 140 296 146 48 321 449 321), lower := (rows 97 7 140 296 146 48 64 128 256), losses := [{ target := 7, region := (rows 57 6 4 57 16 48 127 0 319), good := (rows 361 335 335 361 379 377 64 0 256) }] }

theorem u5744 : Upper (D 9) (R 9) [96,5,136,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5744 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5745 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 296 146 96 337 401 273), lower := (rows 97 7 140 296 146 96 64 128 256), losses := [] }

theorem u5745 : Upper (D 9) (R 9) [96,5,136,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5745 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5746 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 7 140 296 146 288 81 209 337), lower := (rows 97 7 140 296 146 288 64 128 256), losses := [] }

theorem u5746 : Upper (D 9) (R 9) [96,5,136,288,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5746 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5747 : Route 9 := (fun mask => (mask,id))

def c5747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5747 : Upper (D 9) (R 9) [96,5,136,288,192,1] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,192,1] 13 (by decide) (choices 1) [2,16,256] r5747 c5747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2271
  · exact u2272
  · exact u2273

def r5748 : Route 9 := (fun mask => (mask,id))

def c5748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5748 : Upper (D 9) (R 9) [96,5,136,288,192,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,192,2] 13 (by decide) (choices 1) [1,16,256] r5748 c5748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2274
  · exact u2275
  · exact u2276

def b5749 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 140 296 208 48 323 387 259), lower := (rows 97 7 140 296 208 48 64 128 256), losses := [] }

theorem u5749 : Upper (D 9) (R 9) [96,5,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5749 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5750 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 7 140 296 208 288 83 147 275), lower := (rows 97 7 140 296 208 288 64 128 256), losses := [] }

theorem u5750 : Upper (D 9) (R 9) [96,5,136,288,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5750 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5751 : Route 9 := (fun mask => (mask,id))

def c5751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5751 : Upper (D 9) (R 9) [96,5,136,288,257,2] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,257,2] 13 (by decide) (choices 1) [16,128] r5751 c5751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2277
  · exact u2278

def b5752 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 7 140 296 273 48 194 194 450), lower := (rows 97 7 140 296 273 48 64 128 256), losses := [] }

theorem u5752 : Upper (D 9) (R 9) [96,5,136,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5752 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5753 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 296 273 96 210 146 402), lower := (rows 97 7 140 296 273 96 64 128 256), losses := [] }

theorem u5753 : Upper (D 9) (R 9) [96,5,136,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5753 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5754 : Route 9 := (fun mask => (mask,id))

def c5754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5754 : Upper (D 9) (R 9) [96,5,136,288,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,257,128] 13 (by decide) (choices 1) [2,16] r5754 c5754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2279
  · exact u2280

def b5755 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 6, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(3,6),(4,0),(4,5)], upper := (rows 97 7 140 296 274 33 208 208 464), lower := (rows 97 7 140 296 274 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 24 16 35 0 128 256), good := (rows 33 39 140 296 314 33 0 128 256) }] }

theorem u5755 : Upper (D 9) (R 9) [96,5,136,288,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5755 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5756 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 7 140 296 274 48 193 193 449), lower := (rows 97 7 140 296 274 48 64 128 256), losses := [] }

theorem u5756 : Upper (D 9) (R 9) [96,5,136,288,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5756 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5757 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 296 274 96 209 145 401), lower := (rows 97 7 140 296 274 96 64 128 256), losses := [] }

theorem u5757 : Upper (D 9) (R 9) [96,5,136,288,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5757 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5758 : Route 9 := (fun mask => (mask,id))

def c5758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5758 : Upper (D 9) (R 9) [96,5,136,288,258,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,258,128] 13 (by decide) (choices 1) [1,16] r5758 c5758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2281
  · exact u2282

def b5759 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 41, targets := 128 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 7 140 296 336 33 210 146 402), lower := (rows 97 7 140 296 336 33 64 128 256), losses := [] }

theorem u5759 : Upper (D 9) (R 9) [96,5,136,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5759 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5759
end Delivery.IrregularNine14.P09
