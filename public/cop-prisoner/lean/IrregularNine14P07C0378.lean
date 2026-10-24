import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0115
import IrregularNine14P07C0116

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22680 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 472, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 7 280 112 34 193 129 385), lower := (rows 37 74 7 280 112 34 64 128 256), losses := [] }

theorem u22680 : Upper (D 7) (R 7) [36,72,3,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22681 : Route 9 := (fun mask => (mask,id))

def c22681 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22681 : Upper (D 7) (R 7) [36,72,3,272,96,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,96,128] 13 (by decide) (choices 1) [1,2,128] r22681 c22681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6939
  · exact u6940
  · exact u6941

def b22682 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 280 145 34 224 224 480), lower := (rows 37 74 7 280 145 34 64 128 256), losses := [] }

theorem u22682 : Upper (D 7) (R 7) [36,72,3,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22683 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 7 280 145 96 226 162 418), lower := (rows 37 74 7 280 145 96 64 128 256), losses := [] }

theorem u22683 : Upper (D 7) (R 7) [36,72,3,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22684 : Route 9 := (fun mask => (mask,id))

def c22684 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22684 : Upper (D 7) (R 7) [36,72,3,272,129,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,129,128] 13 (by decide) (choices 1) [2,32] r22684 c22684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6942
  · exact u6943

def b22685 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 280 146 33 224 224 480), lower := (rows 37 74 7 280 146 33 64 128 256), losses := [] }

theorem u22685 : Upper (D 7) (R 7) [36,72,3,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22686 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 74 7 280 146 96 225 161 417), lower := (rows 37 74 7 280 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 13 20 32 0 129 257), good := (rows 445 10 415 280 146 32 0 128 256) }] }

theorem u22686 : Upper (D 7) (R 7) [36,72,3,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22687 : Route 9 := (fun mask => (mask,id))

def c22687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22687 : Upper (D 7) (R 7) [36,72,3,272,130,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,130,128] 13 (by decide) (choices 1) [1,32] r22687 c22687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6944
  · exact u6945

def b22688 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 280 176 33 194 194 450), lower := (rows 37 74 7 280 176 33 64 128 256), losses := [] }

theorem u22688 : Upper (D 7) (R 7) [36,72,3,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22689 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 280 176 34 193 193 449), lower := (rows 37 74 7 280 176 34 64 128 256), losses := [] }

theorem u22689 : Upper (D 7) (R 7) [36,72,3,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22690 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 74 7 280 176 96 195 131 387), lower := (rows 37 74 7 280 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 104 37 280 176 96 96 128 256) },{ target := 6, region := (rows 1 2 4 13 17 32 0 132 260), good := (rows 445 10 415 280 176 32 0 128 256) }] }

theorem u22690 : Upper (D 7) (R 7) [36,72,3,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22691 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 280 176 160 67 195 323), lower := (rows 37 74 7 280 176 160 64 128 256), losses := [] }

theorem u22691 : Upper (D 7) (R 7) [36,72,3,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22692 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 474, targets := 1 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 280 208 33 226 162 418), lower := (rows 37 74 7 280 208 33 64 128 256), losses := [] }

theorem u22692 : Upper (D 7) (R 7) [36,72,3,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22693 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 74 7 280 208 34 225 161 417), lower := (rows 37 74 7 280 208 34 64 128 256), losses := [] }

theorem u22693 : Upper (D 7) (R 7) [36,72,3,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22694 : Route 9 := (fun mask => (mask,id))

def c22694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22694 : Upper (D 7) (R 7) [36,72,3,272,192,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,272,192,128] 13 (by decide) (choices 1) [1,2,32] r22694 c22694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6946
  · exact u6947
  · exact u6948

def b22695 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 296 81 34 208 144 400), lower := (rows 37 74 7 296 81 34 64 128 256), losses := [] }

theorem u22695 : Upper (D 7) (R 7) [36,72,3,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22696 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 7 296 81 48 194 130 386), lower := (rows 37 74 7 296 81 48 64 128 256), losses := [] }

theorem u22696 : Upper (D 7) (R 7) [36,72,3,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22696 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22697 : Route 9 := (fun mask => (mask,id))

def c22697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22697 : Upper (D 7) (R 7) [36,72,3,288,65,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,65,128] 13 (by decide) (choices 1) [2,16,128] r22697 c22697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6949
  · exact u6950
  · exact u6951

def b22698 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 296 145 34 208 208 464), lower := (rows 37 74 7 296 145 34 64 128 256), losses := [] }

theorem u22698 : Upper (D 7) (R 7) [36,72,3,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22699 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 74 7 296 145 48 194 194 450), lower := (rows 37 74 7 296 145 48 64 128 256), losses := [] }

theorem u22699 : Upper (D 7) (R 7) [36,72,3,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22699 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22700 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 7 296 145 96 210 146 402), lower := (rows 37 74 7 296 145 96 64 128 256), losses := [] }

theorem u22700 : Upper (D 7) (R 7) [36,72,3,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22701 : Route 9 := (fun mask => (mask,id))

def c22701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22701 : Upper (D 7) (R 7) [36,72,3,288,129,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,129,128] 13 (by decide) (choices 1) [2,16] r22701 c22701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6952
  · exact u6953

def b22702 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 296 146 33 208 208 464), lower := (rows 37 74 7 296 146 33 64 128 256), losses := [] }

theorem u22702 : Upper (D 7) (R 7) [36,72,3,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22703 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 74 7 296 146 48 193 193 449), lower := (rows 37 74 7 296 146 48 64 128 256), losses := [] }

theorem u22703 : Upper (D 7) (R 7) [36,72,3,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22703 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22704 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 144, targets := 32 },{ cop := 2, region := 144, targets := 64 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 37 74 7 296 146 96 209 145 401), lower := (rows 37 74 7 296 146 96 64 128 256), losses := [] }

theorem u22704 : Upper (D 7) (R 7) [36,72,3,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22705 : Route 9 := (fun mask => (mask,id))

def c22705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22705 : Upper (D 7) (R 7) [36,72,3,288,130,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,130,128] 13 (by decide) (choices 1) [1,16] r22705 c22705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6954
  · exact u6955

def b22706 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 296 208 33 210 146 402), lower := (rows 37 74 7 296 208 33 64 128 256), losses := [] }

theorem u22706 : Upper (D 7) (R 7) [36,72,3,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22707 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 296 208 34 209 145 401), lower := (rows 37 74 7 296 208 34 64 128 256), losses := [] }

theorem u22707 : Upper (D 7) (R 7) [36,72,3,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22708 : Route 9 := (fun mask => (mask,id))

def c22708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22708 : Upper (D 7) (R 7) [36,72,3,288,192,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,192,16] 13 (by decide) (choices 1) [1,2,128] r22708 c22708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6956
  · exact u6957
  · exact u6958

def r22709 : Route 9 := (fun mask => (mask,id))

def c22709 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22709 : Upper (D 7) (R 7) [36,72,3,288,192,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,288,192,128] 13 (by decide) (choices 1) [1,2,16] r22709 c22709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6959
  · exact u6960
  · exact u6961

def b22710 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 81 34 240 176 432), lower := (rows 37 74 7 392 81 34 64 128 256), losses := [] }

theorem u22710 : Upper (D 7) (R 7) [36,72,3,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22711 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 7 392 81 48 226 162 418), lower := (rows 37 74 7 392 81 48 64 128 256), losses := [] }

theorem u22711 : Upper (D 7) (R 7) [36,72,3,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22711 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22712 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 74 7 392 81 160 114 178 306), lower := (rows 37 74 7 392 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 47 7 424 17 160 0 160 256) }] }

theorem u22712 : Upper (D 7) (R 7) [36,72,3,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22713 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 7 392 112 33 210 146 402), lower := (rows 37 74 7 392 112 33 64 128 256), losses := [] }

theorem u22713 : Upper (D 7) (R 7) [36,72,3,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22714 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 112 34 209 145 401), lower := (rows 37 74 7 392 112 34 64 128 256), losses := [] }

theorem u22714 : Upper (D 7) (R 7) [36,72,3,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22715 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 392 112 48 195 131 387), lower := (rows 37 74 7 392 112 48 64 128 256), losses := [] }

theorem u22715 : Upper (D 7) (R 7) [36,72,3,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22715 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22716 : PairBound 9 := { available := 19, camps := [], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 37 74 7 392 112 160 83 147 275), lower := (rows 37 74 7 392 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 36 122 22 424 112 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 18 168 64 128 256), good := (rows 37 120 21 424 112 160 64 160 256) },{ target := 6, region := (rows 3 2 6 8 16 168 0 128 256), good := (rows 37 47 7 424 48 160 0 160 256) }] }

theorem u22716 : Upper (D 7) (R 7) [36,72,3,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22717 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 145 34 112 240 368), lower := (rows 37 74 7 392 145 34 64 128 256), losses := [] }

theorem u22717 : Upper (D 7) (R 7) [36,72,3,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22718 : Route 9 := (fun mask => (mask,id))

def c22718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22718 : Upper (D 7) (R 7) [36,72,3,384,129,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,129,16] 13 (by decide) (choices 1) [2,32] r22718 c22718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6962
  · exact u6963

def b22719 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 7 392 145 96 114 178 306), lower := (rows 37 74 7 392 145 96 64 128 256), losses := [] }

theorem u22719 : Upper (D 7) (R 7) [36,72,3,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22720 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 146 33 112 240 368), lower := (rows 37 74 7 392 146 33 64 128 256), losses := [] }

theorem u22720 : Upper (D 7) (R 7) [36,72,3,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22721 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 74 7 392 146 48 97 225 353), lower := (rows 37 74 7 392 146 48 64 128 256), losses := [] }

theorem u22721 : Upper (D 7) (R 7) [36,72,3,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22721 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22722 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 74 7 392 146 96 113 177 305), lower := (rows 37 74 7 392 146 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 104 37 392 176 96 96 128 256) },{ target := 6, region := (rows 1 2 4 13 20 32 0 129 257), good := (rows 445 10 415 392 146 32 0 128 256) }] }

theorem u22722 : Upper (D 7) (R 7) [36,72,3,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22723 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 176 33 82 210 338), lower := (rows 37 74 7 392 176 33 64 128 256), losses := [] }

theorem u22723 : Upper (D 7) (R 7) [36,72,3,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22724 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 176 34 81 209 337), lower := (rows 37 74 7 392 176 34 64 128 256), losses := [] }

theorem u22724 : Upper (D 7) (R 7) [36,72,3,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22725 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 392 176 48 67 195 323), lower := (rows 37 74 7 392 176 48 64 128 256), losses := [] }

theorem u22725 : Upper (D 7) (R 7) [36,72,3,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22725 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22726 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 74 7 392 176 96 83 147 275), lower := (rows 37 74 7 392 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 104 37 392 176 96 96 128 256) },{ target := 6, region := (rows 1 2 4 13 17 32 0 132 260), good := (rows 445 10 415 392 176 32 0 128 256) }] }

theorem u22726 : Upper (D 7) (R 7) [36,72,3,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22727 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 208 33 114 178 306), lower := (rows 37 74 7 392 208 33 64 128 256), losses := [] }

theorem u22727 : Upper (D 7) (R 7) [36,72,3,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22728 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 392 208 34 113 177 305), lower := (rows 37 74 7 392 208 34 64 128 256), losses := [] }

theorem u22728 : Upper (D 7) (R 7) [36,72,3,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22729 : Route 9 := (fun mask => (mask,id))

def c22729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22729 : Upper (D 7) (R 7) [36,72,3,384,192,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,384,192,16] 13 (by decide) (choices 1) [1,2,32] r22729 c22729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6964
  · exact u6965
  · exact u6966

def b22730 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 42 146 33 448 448 448), lower := (rows 37 74 21 42 146 33 64 128 256), losses := [] }

theorem u22730 : Upper (D 7) (R 7) [36,72,17,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22731 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 21 42 146 96 449 385 385), lower := (rows 37 74 21 42 146 96 64 128 256), losses := [] }

theorem u22731 : Upper (D 7) (R 7) [36,72,17,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22732 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 330, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(3,6)], upper := (rows 37 74 21 42 146 160 321 449 321), lower := (rows 37 74 21 42 146 160 64 128 256), losses := [] }

theorem u22732 : Upper (D 7) (R 7) [36,72,17,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22733 : Route 9 := (fun mask => (mask,id))

def c22733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22733 : Upper (D 7) (R 7) [36,72,17,34,130,256] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,130,256] 13 (by decide) (choices 1) [1,128] r22733 c22733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6967
  · exact u6968

def b22734 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 21 42 208 33 450 386 386), lower := (rows 37 74 21 42 208 33 64 128 256), losses := [] }

theorem u22734 : Upper (D 7) (R 7) [36,72,17,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22735 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 74 21 42 208 34 449 385 385), lower := (rows 37 74 21 42 208 34 64 128 256), losses := [] }

theorem u22735 : Upper (D 7) (R 7) [36,72,17,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22736 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 42 208 160 323 387 259), lower := (rows 37 74 21 42 208 160 64 128 256), losses := [] }

theorem u22736 : Upper (D 7) (R 7) [36,72,17,34,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22737 : Route 9 := (fun mask => (mask,id))

def c22737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22737 : Upper (D 7) (R 7) [36,72,17,34,192,256] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,192,256] 13 (by decide) (choices 1) [1,2,128] r22737 c22737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6969
  · exact u6970
  · exact u6971

def b22738 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 42 274 33 192 192 448), lower := (rows 37 74 21 42 274 33 64 128 256), losses := [] }

theorem u22738 : Upper (D 7) (R 7) [36,72,17,34,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22739 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 21 42 274 96 193 129 385), lower := (rows 37 74 21 42 274 96 64 128 256), losses := [] }

theorem u22739 : Upper (D 7) (R 7) [36,72,17,34,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22739
end Delivery.IrregularNine14.P07
