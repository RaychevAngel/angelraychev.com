import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0011

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8700 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 76 56 145 34 320 131 259), lower := (rows 37 194 76 56 145 34 320 128 256), losses := [{ target := 5, region := (rows 1 27 12 8 17 0 345 145 273), good := (rows 471 194 78 478 467 2 320 128 320) }] }

theorem u8700 : Upper (D 7) (R 7) [36,192,72,48,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8700 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8701 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 56 273 34 65 130 386), lower := (rows 37 194 76 56 273 34 65 128 256), losses := [] }

theorem u8701 : Upper (D 7) (R 7) [36,192,72,48,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8702 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 56 273 34 66 129 385), lower := (rows 37 194 76 56 273 34 66 128 256), losses := [] }

theorem u8702 : Upper (D 7) (R 7) [36,192,72,48,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8703 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 56 273 34 192 131 259), lower := (rows 37 194 76 56 273 34 192 128 256), losses := [] }

theorem u8703 : Upper (D 7) (R 7) [36,192,72,48,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8704 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 56 273 160 65 130 258), lower := (rows 37 194 76 56 273 160 65 128 256), losses := [] }

theorem u8704 : Upper (D 7) (R 7) [36,192,72,48,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8705 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,0),(4,5)], upper := (rows 37 194 76 56 273 160 66 131 259), lower := (rows 37 194 76 56 273 160 66 128 256), losses := [{ target := 0, region := (rows 0 162 12 8 16 162 235 128 256), good := (rows 102 226 76 126 336 226 98 226 256) }] }

theorem u8705 : Upper (D 7) (R 7) [36,192,72,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8706 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 56 400 34 65 131 259), lower := (rows 37 194 76 56 400 34 65 128 256), losses := [] }

theorem u8706 : Upper (D 7) (R 7) [36,192,72,48,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8707 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 56 400 34 66 129 257), lower := (rows 37 194 76 56 400 34 66 128 256), losses := [] }

theorem u8707 : Upper (D 7) (R 7) [36,192,72,48,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8708 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 76 137 19 34 80 416 288), lower := (rows 37 194 76 137 19 34 80 128 256), losses := [] }

theorem u8708 : Upper (D 7) (R 7) [36,192,72,129,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8708 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8709 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 4, region := 392, targets := 34 }], pairs := [(1,0),(2,0),(3,1),(3,5)], upper := (rows 37 194 76 137 19 34 96 400 272), lower := (rows 37 194 76 137 19 34 96 128 256), losses := [] }

theorem u8709 : Upper (D 7) (R 7) [36,192,72,129,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8710 : Route 9 := (fun mask => (mask,id))

def c8710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8710 : Upper (D 7) (R 7) [36,192,72,129,3,2,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,3,2,256] 13 (by decide) (choices 1) [16,32] r8710 c8710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u682
  · exact u683

def b8711 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 76 137 19 288 66 176 304), lower := (rows 37 194 76 137 19 288 66 128 256), losses := [] }

theorem u8711 : Upper (D 7) (R 7) [36,192,72,129,3,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8711 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8712 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 37 194 76 137 19 288 80 162 290), lower := (rows 37 194 76 137 19 288 80 128 256), losses := [] }

theorem u8712 : Upper (D 7) (R 7) [36,192,72,129,3,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8712 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8713 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 136, targets := 32 },{ cop := 4, region := 136, targets := 64 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 37 194 76 137 19 288 96 146 274), lower := (rows 37 194 76 137 19 288 96 128 256), losses := [] }

theorem u8713 : Upper (D 7) (R 7) [36,192,72,129,3,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8713 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8714 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 304, targets := 65 },{ cop := 3, region := 68, targets := 2 }], pairs := [(2,1),(4,0),(4,6)], upper := (rows 37 194 76 137 50 288 65 146 274), lower := (rows 37 194 76 137 50 288 65 128 256), losses := [] }

theorem u8714 : Upper (D 7) (R 7) [36,192,72,129,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8714 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8715 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 137 50 288 66 145 273), lower := (rows 37 194 76 137 50 288 66 128 256), losses := [] }

theorem u8715 : Upper (D 7) (R 7) [36,192,72,129,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8715 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8716 : Route 9 := (fun mask => (mask,id))

def c8716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8716 : Upper (D 7) (R 7) [36,192,72,129,34,256,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,34,256,16] 13 (by decide) (choices 1) [1,2] r8716 c8716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u684
  · exact u685

def b8717 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 137 273 34 66 176 304), lower := (rows 37 194 76 137 273 34 66 128 256), losses := [] }

theorem u8717 : Upper (D 7) (R 7) [36,192,72,129,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8718 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(3,6),(4,6)], upper := (rows 37 194 76 137 273 34 80 162 290), lower := (rows 37 194 76 137 273 34 80 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 17 34 0 162 290), good := (rows 445 418 12 153 281 418 16 128 256) }] }

theorem u8718 : Upper (D 7) (R 7) [36,192,72,129,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8718 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8719 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 37 194 76 137 273 34 96 146 274), lower := (rows 37 194 76 137 273 34 96 128 256), losses := [{ target := 1, region := (rows 97 0 46 10 16 32 97 128 256), good := (rows 101 205 77 205 337 109 101 128 256) }] }

theorem u8719 : Upper (D 7) (R 7) [36,192,72,129,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8720 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 137 273 48 66 162 290), lower := (rows 37 194 76 137 273 48 66 128 256), losses := [] }

theorem u8720 : Upper (D 7) (R 7) [36,192,72,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8720 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8721 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 137 273 48 96 130 258), lower := (rows 37 194 76 137 273 48 96 128 256), losses := [{ target := 0, region := (rows 0 127 12 8 16 48 113 255 383), good := (rows 486 450 462 462 498 498 482 128 256) }] }

theorem u8721 : Upper (D 7) (R 7) [36,192,72,129,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8721 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8722 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 304, targets := 65 },{ cop := 3, region := 68, targets := 130 }], pairs := [(2,1),(2,7),(4,0),(4,6)], upper := (rows 37 194 76 137 274 34 65 176 304), lower := (rows 37 194 76 137 274 34 65 128 256), losses := [] }

theorem u8722 : Upper (D 7) (R 7) [36,192,72,129,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8723 : Route 9 := (fun mask => (mask,id))

def c8723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8723 : Upper (D 7) (R 7) [36,192,72,129,258,2,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,258,2,16] 13 (by decide) (choices 1) [1,32] r8723 c8723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u686
  · exact u687

def b8724 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 37 194 76 137 274 34 96 145 273), lower := (rows 37 194 76 137 274 34 96 128 256), losses := [{ target := 1, region := (rows 97 0 46 10 16 32 97 128 256), good := (rows 101 205 77 205 284 109 101 128 256) }] }

theorem u8724 : Upper (D 7) (R 7) [36,192,72,129,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8725 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 304, targets := 65 },{ cop := 3, region := 68, targets := 2 }], pairs := [(2,1),(4,0),(4,6)], upper := (rows 37 194 76 137 274 48 65 162 290), lower := (rows 37 194 76 137 274 48 65 128 256), losses := [] }

theorem u8725 : Upper (D 7) (R 7) [36,192,72,129,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8725 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8726 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 137 274 48 66 161 289), lower := (rows 37 194 76 137 274 48 66 128 256), losses := [] }

theorem u8726 : Upper (D 7) (R 7) [36,192,72,129,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8726 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8727 : PairBound 9 := { available := 3, camps := [], pairs := [(1,0),(2,0),(2,1)], upper := (rows 37 194 76 137 274 48 96 131 259), lower := (rows 37 194 76 137 274 48 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 113 128 256), good := (rows 100 194 78 206 370 112 96 128 256) },{ target := 1, region := (rows 1 0 12 8 16 48 113 128 256), good := (rows 101 192 76 205 368 112 96 128 256) }] }

theorem u8727 : Upper (D 7) (R 7) [36,192,72,129,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8727 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8728 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 304, targets := 65 },{ cop := 3, region := 68, targets := 130 }], pairs := [(2,1),(2,7),(4,0),(4,6)], upper := (rows 37 194 76 137 304 34 65 146 274), lower := (rows 37 194 76 137 304 34 65 128 256), losses := [] }

theorem u8728 : Upper (D 7) (R 7) [36,192,72,129,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8729 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 137 304 34 66 145 273), lower := (rows 37 194 76 137 304 34 66 128 256), losses := [] }

theorem u8729 : Upper (D 7) (R 7) [36,192,72,129,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8730 : Route 9 := (fun mask => (mask,id))

def c8730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8730 : Upper (D 7) (R 7) [36,192,72,129,288,2,16] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,288,2,16] 13 (by decide) (choices 1) [1,2] r8730 c8730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u688
  · exact u689

def r8731 : Route 9 := (fun mask => (mask,id))

def c8731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8731 : Upper (D 7) (R 7) [36,192,72,144,34,256,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,34,256,1] 13 (by decide) (choices 1) [1,2] r8731 c8731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u690
  · exact u691

def b8732 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 152 50 288 66 129 257), lower := (rows 37 194 76 152 50 288 66 128 256), losses := [] }

theorem u8732 : Upper (D 7) (R 7) [36,192,72,144,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8732 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8733 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(1,5),(2,1),(3,0)], upper := (rows 37 194 76 152 273 34 65 162 290), lower := (rows 37 194 76 152 273 34 65 128 256), losses := [{ target := 0, region := (rows 0 70 4 24 16 103 64 231 359), good := (rows 422 482 494 152 440 418 482 128 256) },{ target := 1, region := (rows 1 0 12 8 16 32 81 128 256), good := (rows 101 192 76 220 337 32 65 128 256) },{ target := 5, region := (rows 1 10 12 8 16 0 81 128 256), good := (rows 69 194 78 222 337 2 65 128 256) }] }

theorem u8733 : Upper (D 7) (R 7) [36,192,72,144,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8734 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 152 273 34 66 161 289), lower := (rows 37 194 76 152 273 34 66 128 256), losses := [] }

theorem u8734 : Upper (D 7) (R 7) [36,192,72,144,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8735 : Route 9 := (fun mask => (mask,id))

def c8735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8735 : Upper (D 7) (R 7) [36,192,72,144,257,2,32] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,257,2,32] 13 (by decide) (choices 1) [1,2] r8735 c8735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u692
  · exact u693

def b8736 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 152 274 33 65 162 290), lower := (rows 37 194 76 152 274 33 65 128 256), losses := [] }

theorem u8736 : Upper (D 7) (R 7) [36,192,72,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8737 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 76 152 274 33 66 161 289), lower := (rows 37 194 76 152 274 33 66 128 256), losses := [] }

theorem u8737 : Upper (D 7) (R 7) [36,192,72,144,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8738 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 152 274 33 96 131 259), lower := (rows 37 194 76 152 274 33 96 128 256), losses := [] }

theorem u8738 : Upper (D 7) (R 7) [36,192,72,144,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8739 : Route 9 := (fun mask => (mask,id))

def c8739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8739 : Upper (D 7) (R 7) [36,192,72,144,258,2,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,258,2,1] 13 (by decide) (choices 1) [1,32] r8739 c8739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u694
  · exact u695

def b8740 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(2,7)], upper := (rows 37 194 76 152 274 34 96 129 257), lower := (rows 37 194 76 152 274 34 96 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 16 50 123 0 269), good := (rows 357 98 333 381 370 98 96 0 256) }] }

theorem u8740 : Upper (D 7) (R 7) [36,192,72,144,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8741 : Route 9 := (fun mask => (mask,id))

def c8741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8741 : Upper (D 7) (R 7) [36,192,72,144,288,2,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,288,2,1] 13 (by decide) (choices 1) [1,2] r8741 c8741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u696
  · exact u697

def b8742 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 152 304 34 66 129 257), lower := (rows 37 194 76 152 304 34 66 128 256), losses := [] }

theorem u8742 : Upper (D 7) (R 7) [36,192,72,144,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8743 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 168 273 48 65 130 258), lower := (rows 37 194 76 168 273 48 65 128 256), losses := [] }

theorem u8743 : Upper (D 7) (R 7) [36,192,72,160,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8743 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8744 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 168 273 48 66 131 259), lower := (rows 37 194 76 168 273 48 66 128 256), losses := [] }

theorem u8744 : Upper (D 7) (R 7) [36,192,72,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8745 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 168 274 48 65 131 259), lower := (rows 37 194 76 168 274 48 65 128 256), losses := [] }

theorem u8745 : Upper (D 7) (R 7) [36,192,72,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8745 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8746 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 168 274 48 66 129 257), lower := (rows 37 194 76 168 274 48 66 128 256), losses := [] }

theorem u8746 : Upper (D 7) (R 7) [36,192,72,160,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8746 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8747 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 194 76 265 19 34 80 160 416), lower := (rows 37 194 76 265 19 34 80 128 256), losses := [] }

theorem u8747 : Upper (D 7) (R 7) [36,192,72,257,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8747 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8748 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 392, targets := 34 },{ cop := 4, region := 226, targets := 1 },{ cop := 4, region := 392, targets := 64 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 194 76 265 19 34 96 144 400), lower := (rows 37 194 76 265 19 34 96 128 256), losses := [] }

theorem u8748 : Upper (D 7) (R 7) [36,192,72,257,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8749 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 265 19 34 192 176 304), lower := (rows 37 194 76 265 19 34 192 128 256), losses := [] }

theorem u8749 : Upper (D 7) (R 7) [36,192,72,257,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8750 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 424, targets := 66 },{ cop := 4, region := 226, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,1),(3,6)], upper := (rows 37 194 76 265 19 160 66 176 304), lower := (rows 37 194 76 265 19 160 66 128 256), losses := [] }

theorem u8750 : Upper (D 7) (R 7) [36,192,72,257,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8751 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 162, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 37 194 76 265 19 160 80 162 290), lower := (rows 37 194 76 265 19 160 80 128 256), losses := [{ target := 6, region := (rows 5 2 4 24 16 242 0 146 274), good := (rows 37 418 45 265 443 160 440 160 256) }] }

theorem u8751 : Upper (D 7) (R 7) [36,192,72,257,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8751 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8752 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 226, targets := 1 },{ cop := 4, region := 264, targets := 32 },{ cop := 4, region := 264, targets := 64 },{ cop := 4, region := 264, targets := 128 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 265 19 160 96 146 274), lower := (rows 37 194 76 265 19 160 96 128 256), losses := [] }

theorem u8752 : Upper (D 7) (R 7) [36,192,72,257,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8753 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 265 145 34 66 176 304), lower := (rows 37 194 76 265 145 34 66 128 256), losses := [] }

theorem u8753 : Upper (D 7) (R 7) [36,192,72,257,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8754 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 265 145 34 80 162 290), lower := (rows 37 194 76 265 145 34 80 128 256), losses := [] }

theorem u8754 : Upper (D 7) (R 7) [36,192,72,257,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8754 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8755 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(1,5),(2,0),(2,1)], upper := (rows 37 194 76 265 145 34 96 146 274), lower := (rows 37 194 76 265 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 146 12 8 16 178 243 144 272), good := (rows 100 226 76 332 498 98 96 226 256) },{ target := 1, region := (rows 1 0 12 8 16 32 97 128 256), good := (rows 101 192 76 333 209 96 96 128 256) },{ target := 5, region := (rows 1 6 4 25 25 0 64 133 261), good := (rows 415 194 478 409 409 2 64 128 256) }] }

theorem u8755 : Upper (D 7) (R 7) [36,192,72,257,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8756 : PairBound 9 := { available := 34, camps := [{ cop := 7, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 265 145 48 66 162 290), lower := (rows 37 194 76 265 145 48 66 128 256), losses := [{ target := 0, region := (rows 0 187 12 8 16 48 255 177 305), good := (rows 486 194 78 462 498 498 66 194 256) }] }

theorem u8756 : Upper (D 7) (R 7) [36,192,72,257,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8756 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8757 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 265 145 48 96 130 258), lower := (rows 37 194 76 265 145 48 96 128 256), losses := [{ target := 0, region := (rows 0 127 12 8 16 48 113 255 383), good := (rows 486 450 462 462 498 498 482 128 256) }] }

theorem u8757 : Upper (D 7) (R 7) [36,192,72,257,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8757 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8758 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 194 76 265 176 34 65 146 274), lower := (rows 37 194 76 265 176 34 65 128 256), losses := [] }

theorem u8758 : Upper (D 7) (R 7) [36,192,72,257,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8759 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 265 176 34 66 145 273), lower := (rows 37 194 76 265 176 34 66 128 256), losses := [] }

theorem u8759 : Upper (D 7) (R 7) [36,192,72,257,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8759
end Delivery.IrregularNine14.P07
