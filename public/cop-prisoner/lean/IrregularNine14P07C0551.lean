import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0278
import IrregularNine14P07C0279

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33060 : Route 9 := (fun mask => (mask,id))

def c33060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33060 : Upper (D 7) (R 7) [12,96,17,288,192] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,192] 13 (by decide) (choices 1) [1,2,128] r33060 c33060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16686
  · exact u16687
  · exact u16688

def b33061 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 392 19 226 226 226 482), lower := (rows 13 98 21 392 19 32 64 128 256), losses := [] }

theorem u33061 : Upper (D 7) (R 7) [12,96,17,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33062 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 392 49 226 194 194 450), lower := (rows 13 98 21 392 49 32 64 128 256), losses := [] }

theorem u33062 : Upper (D 7) (R 7) [12,96,17,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33063 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 21 392 50 227 195 195 451), lower := (rows 13 98 21 392 50 32 64 128 256), losses := [] }

theorem u33063 : Upper (D 7) (R 7) [12,96,17,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33064 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 21 392 112 163 195 131 387), lower := (rows 13 98 21 392 112 32 64 128 256), losses := [] }

theorem u33064 : Upper (D 7) (R 7) [12,96,17,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33065 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 21, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 21 392 145 98 98 226 354), lower := (rows 13 98 21 392 145 32 64 128 256), losses := [] }

theorem u33065 : Upper (D 7) (R 7) [12,96,17,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33066 : Route 9 := (fun mask => (mask,id))

def c33066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33066 : Upper (D 7) (R 7) [12,96,17,384,130] 13 := by
  apply FastRouting.sound _ _ [12,96,17,384,130] 13 (by decide) (choices 1) [1,2,64] r33066 c33066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16689
  · exact u16690
  · exact u16691

def r33067 : Route 9 := (fun mask => (mask,id))

def c33067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33067 : Upper (D 7) (R 7) [12,96,17,384,160] 13 := by
  apply FastRouting.sound _ _ [12,96,17,384,160] 13 (by decide) (choices 1) [1,2,64] r33067 c33067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16692
  · exact u16693
  · exact u16694

def b33068 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 22 41 19 480 448 448 448), lower := (rows 13 98 22 41 19 32 64 128 256), losses := [] }

theorem u33068 : Upper (D 7) (R 7) [12,96,18,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33069 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 22 41 81 418 450 386 386), lower := (rows 13 98 22 41 81 32 64 128 256), losses := [] }

theorem u33069 : Upper (D 7) (R 7) [12,96,18,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33070 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 20, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 13 98 22 41 82 417 449 385 385), lower := (rows 13 98 22 41 82 32 64 128 256), losses := [] }

theorem u33070 : Upper (D 7) (R 7) [12,96,18,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33071 : Route 9 := (fun mask => (mask,id))

def c33071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33071 : Upper (D 7) (R 7) [12,96,18,33,129] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,129] 13 (by decide) (choices 1) [2,64,128,256] r33071 c33071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16695
  · exact u16696
  · exact u16697
  · exact u16698

def b33072 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 41 146 481 449 449 449), lower := (rows 13 98 22 41 146 32 64 128 256), losses := [] }

theorem u33072 : Upper (D 7) (R 7) [12,96,18,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33073 : Route 9 := (fun mask => (mask,id))

def c33073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33073 : Upper (D 7) (R 7) [12,96,18,33,192] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,192] 13 (by decide) (choices 1) [1,2,128,256] r33073 c33073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16699
  · exact u16700
  · exact u16701
  · exact u16702

def r33074 : Route 9 := (fun mask => (mask,id))

def c33074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33074 : Upper (D 7) (R 7) [12,96,18,33,257] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,257] 13 (by decide) (choices 1) [2,64,128] r33074 c33074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16703
  · exact u16704
  · exact u16705

def b33075 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 41 274 225 193 193 449), lower := (rows 13 98 22 41 274 32 64 128 256), losses := [] }

theorem u33075 : Upper (D 7) (R 7) [12,96,18,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33076 : Route 9 := (fun mask => (mask,id))

def c33076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33076 : Upper (D 7) (R 7) [12,96,18,33,320] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,320] 13 (by decide) (choices 1) [1,2,128] r33076 c33076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16706
  · exact u16707
  · exact u16708

def r33077 : Route 9 := (fun mask => (mask,id))

def c33077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33077 : Upper (D 7) (R 7) [12,96,18,33,384] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,384] 13 (by decide) (choices 1) [1,2,64,128] r33077 c33077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16709
  · exact u16710
  · exact u16711
  · exact u16712

def b33078 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 137 19 480 480 480 480), lower := (rows 13 98 22 137 19 32 64 128 256), losses := [] }

theorem u33078 : Upper (D 7) (R 7) [12,96,18,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33079 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 4, region := 454, targets := 1 }], pairs := [(0,5),(1,0),(2,0),(3,5)], upper := (rows 13 98 22 137 49 482 450 450 450), lower := (rows 13 98 22 137 49 32 64 128 256), losses := [] }

theorem u33079 : Upper (D 7) (R 7) [12,96,18,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33080 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 20, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 98 22 137 50 481 449 449 449), lower := (rows 13 98 22 137 50 32 64 128 256), losses := [] }

theorem u33080 : Upper (D 7) (R 7) [12,96,18,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33081 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 22 137 112 419 451 387 387), lower := (rows 13 98 22 137 112 32 64 128 256), losses := [] }

theorem u33081 : Upper (D 7) (R 7) [12,96,18,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33082 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 13 98 22 137 145 354 354 482 354), lower := (rows 13 98 22 137 145 32 64 128 256), losses := [] }

theorem u33082 : Upper (D 7) (R 7) [12,96,18,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33083 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 13, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 13 98 22 137 146 353 353 481 353), lower := (rows 13 98 22 137 146 32 64 128 256), losses := [] }

theorem u33083 : Upper (D 7) (R 7) [12,96,18,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33084 : Route 9 := (fun mask => (mask,id))

def c33084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33084 : Upper (D 7) (R 7) [12,96,18,129,160] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129,160] 13 (by decide) (choices 1) [1,2,64,256] r33084 c33084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16713
  · exact u16714
  · exact u16715
  · exact u16716

def r33085 : Route 9 := (fun mask => (mask,id))

def c33085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33085 : Upper (D 7) (R 7) [12,96,18,129,257] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129,257] 13 (by decide) (choices 1) [2,64,128] r33085 c33085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16717
  · exact u16718
  · exact u16719

def b33086 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 137 274 225 225 225 481), lower := (rows 13 98 22 137 274 32 64 128 256), losses := [] }

theorem u33086 : Upper (D 7) (R 7) [12,96,18,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33087 : Route 9 := (fun mask => (mask,id))

def c33087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33087 : Upper (D 7) (R 7) [12,96,18,129,288] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129,288] 13 (by decide) (choices 1) [1,2,64,128] r33087 c33087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16720
  · exact u16721
  · exact u16722
  · exact u16723

def r33088 : Route 9 := (fun mask => (mask,id))

def c33088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33088 : Upper (D 7) (R 7) [12,96,18,129,384] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129,384] 13 (by decide) (choices 1) [1,2,64] r33088 c33088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16724
  · exact u16725
  · exact u16726

def r33089 : Route 9 := (fun mask => (mask,id))

def c33089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33089 : Upper (D 7) (R 7) [12,96,18,130,33] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,33] 13 (by decide) (choices 1) [1,64,128,256] r33089 c33089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16727
  · exact u16728
  · exact u16729
  · exact u16730

def b33090 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 22 138 112 417 449 385 385), lower := (rows 13 98 22 138 112 32 64 128 256), losses := [] }

theorem u33090 : Upper (D 7) (R 7) [12,96,18,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33091 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 21, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 13 98 22 138 145 353 353 481 353), lower := (rows 13 98 22 138 145 32 64 128 256), losses := [] }

theorem u33091 : Upper (D 7) (R 7) [12,96,18,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33092 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 354, targets := 128 }], pairs := [(0,5),(1,7),(3,5),(4,1)], upper := (rows 13 98 22 138 176 353 321 449 321), lower := (rows 13 98 22 138 176 32 64 128 256), losses := [] }

theorem u33092 : Upper (D 7) (R 7) [12,96,18,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33093 : Route 9 := (fun mask => (mask,id))

def c33093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33093 : Upper (D 7) (R 7) [12,96,18,130,257] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,257] 13 (by decide) (choices 1) [1,64,128] r33093 c33093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16731
  · exact u16732
  · exact u16733

def r33094 : Route 9 := (fun mask => (mask,id))

def c33094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33094 : Upper (D 7) (R 7) [12,96,18,130,288] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,288] 13 (by decide) (choices 1) [1,64,128] r33094 c33094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16734
  · exact u16735
  · exact u16736

def r33095 : Route 9 := (fun mask => (mask,id))

def c33095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33095 : Upper (D 7) (R 7) [12,96,18,130,384] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,384] 13 (by decide) (choices 1) [1,64] r33095 c33095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16737
  · exact u16738

def b33096 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 193 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 98 22 168 19 481 449 449 449), lower := (rows 13 98 22 168 19 32 64 128 256), losses := [] }

theorem u33096 : Upper (D 7) (R 7) [12,96,18,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33097 : Route 9 := (fun mask => (mask,id))

def c33097 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33097 : Upper (D 7) (R 7) [12,96,18,160,65] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,65] 13 (by decide) (choices 1) [1,2,128,256] r33097 c33097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16739
  · exact u16740
  · exact u16741
  · exact u16742

def b33098 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 13 98 22 168 82 417 449 385 385), lower := (rows 13 98 22 168 82 32 64 128 256), losses := [] }

theorem u33098 : Upper (D 7) (R 7) [12,96,18,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33099 : Route 9 := (fun mask => (mask,id))

def c33099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33099 : Upper (D 7) (R 7) [12,96,18,160,129] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,129] 13 (by decide) (choices 1) [1,2,64,256] r33099 c33099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16743
  · exact u16744
  · exact u16745
  · exact u16746

def b33100 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 168 146 353 321 449 321), lower := (rows 13 98 22 168 146 32 64 128 256), losses := [] }

theorem u33100 : Upper (D 7) (R 7) [12,96,18,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33101 : Route 9 := (fun mask => (mask,id))

def c33101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33101 : Upper (D 7) (R 7) [12,96,18,160,192] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,192] 13 (by decide) (choices 1) [1,2,256] r33101 c33101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16747
  · exact u16748
  · exact u16749

def r33102 : Route 9 := (fun mask => (mask,id))

def c33102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33102 : Upper (D 7) (R 7) [12,96,18,160,257] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,257] 13 (by decide) (choices 1) [1,2,64,128] r33102 c33102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16750
  · exact u16751
  · exact u16752
  · exact u16753

def b33103 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 168 274 225 193 193 449), lower := (rows 13 98 22 168 274 32 64 128 256), losses := [] }

theorem u33103 : Upper (D 7) (R 7) [12,96,18,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33104 : Route 9 := (fun mask => (mask,id))

def c33104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33104 : Upper (D 7) (R 7) [12,96,18,160,320] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,320] 13 (by decide) (choices 1) [1,2,128] r33104 c33104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16754
  · exact u16755
  · exact u16756

def r33105 : Route 9 := (fun mask => (mask,id))

def c33105 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33105 : Upper (D 7) (R 7) [12,96,18,160,384] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,384] 13 (by decide) (choices 1) [1,2,64] r33105 c33105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16757
  · exact u16758
  · exact u16759

def b33106 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 265 19 224 224 224 480), lower := (rows 13 98 22 265 19 32 64 128 256), losses := [] }

theorem u33106 : Upper (D 7) (R 7) [12,96,18,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33107 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 4, region := 198, targets := 1 }], pairs := [(0,5),(1,0),(2,0),(3,5)], upper := (rows 13 98 22 265 49 226 194 194 450), lower := (rows 13 98 22 265 49 32 64 128 256), losses := [] }

theorem u33107 : Upper (D 7) (R 7) [12,96,18,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33108 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 20, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 98 22 265 50 225 193 193 449), lower := (rows 13 98 22 265 50 32 64 128 256), losses := [] }

theorem u33108 : Upper (D 7) (R 7) [12,96,18,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33109 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 22 265 112 163 195 131 387), lower := (rows 13 98 22 265 112 32 64 128 256), losses := [] }

theorem u33109 : Upper (D 7) (R 7) [12,96,18,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33110 : Route 9 := (fun mask => (mask,id))

def c33110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33110 : Upper (D 7) (R 7) [12,96,18,257,129] 13 := by
  apply FastRouting.sound _ _ [12,96,18,257,129] 13 (by decide) (choices 1) [2,64,128] r33110 c33110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16760
  · exact u16761
  · exact u16762

def b33111 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 98 22 265 146 225 225 225 481), lower := (rows 13 98 22 265 146 32 64 128 256), losses := [] }

theorem u33111 : Upper (D 7) (R 7) [12,96,18,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33112 : Route 9 := (fun mask => (mask,id))

def c33112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33112 : Upper (D 7) (R 7) [12,96,18,257,160] 13 := by
  apply FastRouting.sound _ _ [12,96,18,257,160] 13 (by decide) (choices 1) [1,2,64,128] r33112 c33112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16763
  · exact u16764
  · exact u16765
  · exact u16766

def r33113 : Route 9 := (fun mask => (mask,id))

def c33113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33113 : Upper (D 7) (R 7) [12,96,18,258,33] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258,33] 13 (by decide) (choices 1) [1,64,128] r33113 c33113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16767
  · exact u16768
  · exact u16769

def b33114 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 22 266 112 161 193 129 385), lower := (rows 13 98 22 266 112 32 64 128 256), losses := [] }

theorem u33114 : Upper (D 7) (R 7) [12,96,18,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33115 : Route 9 := (fun mask => (mask,id))

def c33115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33115 : Upper (D 7) (R 7) [12,96,18,258,129] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258,129] 13 (by decide) (choices 1) [1,64,128] r33115 c33115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16770
  · exact u16771
  · exact u16772

def r33116 : Route 9 := (fun mask => (mask,id))

def c33116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33116 : Upper (D 7) (R 7) [12,96,18,258,160] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258,160] 13 (by decide) (choices 1) [1,64,128] r33116 c33116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16773
  · exact u16774
  · exact u16775

def b33117 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 193 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 98 22 296 19 225 193 193 449), lower := (rows 13 98 22 296 19 32 64 128 256), losses := [] }

theorem u33117 : Upper (D 7) (R 7) [12,96,18,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33118 : Route 9 := (fun mask => (mask,id))

def c33118 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33118 : Upper (D 7) (R 7) [12,96,18,288,65] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288,65] 13 (by decide) (choices 1) [1,2,128] r33118 c33118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16776
  · exact u16777
  · exact u16778

def b33119 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 13 98 22 296 82 161 193 129 385), lower := (rows 13 98 22 296 82 32 64 128 256), losses := [] }

theorem u33119 : Upper (D 7) (R 7) [12,96,18,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33119
end Delivery.IrregularNine14.P07
