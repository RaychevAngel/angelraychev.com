import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0264
import IrregularNine14P07C0265

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32520 : Route 9 := (fun mask => (mask,id))

def c32520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32520 : Upper (D 7) (R 7) [12,33,66,192,258] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,258] 13 (by decide) (choices 1) [1,16,128] r32520 c32520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15843
  · exact u15844
  · exact u15845

def r32521 : Route 9 := (fun mask => (mask,id))

def c32521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32521 : Upper (D 7) (R 7) [12,33,66,192,288] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,288] 13 (by decide) (choices 1) [1,2,16,128] r32521 c32521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15846
  · exact u15847
  · exact u15848
  · exact u15849

def r32522 : Route 9 := (fun mask => (mask,id))

def c32522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32522 : Upper (D 7) (R 7) [12,33,66,192,384] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,384] 13 (by decide) (choices 1) [1,2,16] r32522 c32522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15850
  · exact u15851
  · exact u15852

def b32523 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(3,5)], upper := (rows 13 35 70 265 50 240 208 208 464), lower := (rows 13 35 70 265 50 32 64 128 256), losses := [] }

theorem u32523 : Upper (D 7) (R 7) [12,33,66,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32524 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 2, region := 16, targets := 160 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 35 70 265 82 176 240 176 432), lower := (rows 13 35 70 265 82 32 64 128 256), losses := [] }

theorem u32524 : Upper (D 7) (R 7) [12,33,66,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32525 : Route 9 := (fun mask => (mask,id))

def c32525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32525 : Upper (D 7) (R 7) [12,33,66,257,96] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257,96] 13 (by decide) (choices 1) [2,16,128] r32525 c32525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15853
  · exact u15854
  · exact u15855

def r32526 : Route 9 := (fun mask => (mask,id))

def c32526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32526 : Upper (D 7) (R 7) [12,33,66,257,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257,130] 13 (by decide) (choices 1) [16,64,128] r32526 c32526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15856
  · exact u15857
  · exact u15858

def r32527 : Route 9 := (fun mask => (mask,id))

def c32527 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32527 : Upper (D 7) (R 7) [12,33,66,257,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257,160] 13 (by decide) (choices 1) [2,16,64,128] r32527 c32527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15859
  · exact u15860
  · exact u15861
  · exact u15862

def r32528 : Route 9 := (fun mask => (mask,id))

def c32528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32528 : Upper (D 7) (R 7) [12,33,66,257,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257,192] 13 (by decide) (choices 1) [2,16,128] r32528 c32528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15863
  · exact u15864
  · exact u15865

def b32529 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 70 266 49 240 208 208 464), lower := (rows 13 35 70 266 49 32 64 128 256), losses := [] }

theorem u32529 : Upper (D 7) (R 7) [12,33,66,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32530 : Route 9 := (fun mask => (mask,id))

def c32530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32530 : Upper (D 7) (R 7) [12,33,66,258,65] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,65] 13 (by decide) (choices 1) [16,128] r32530 c32530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15866
  · exact u15867

def r32531 : Route 9 := (fun mask => (mask,id))

def c32531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32531 : Upper (D 7) (R 7) [12,33,66,258,96] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,96] 13 (by decide) (choices 1) [1,16,128] r32531 c32531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15868
  · exact u15869
  · exact u15870

def r32532 : Route 9 := (fun mask => (mask,id))

def c32532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32532 : Upper (D 7) (R 7) [12,33,66,258,129] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,129] 13 (by decide) (choices 1) [16,64,128] r32532 c32532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15871
  · exact u15872
  · exact u15873

def r32533 : Route 9 := (fun mask => (mask,id))

def c32533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32533 : Upper (D 7) (R 7) [12,33,66,258,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,160] 13 (by decide) (choices 1) [1,16,64,128] r32533 c32533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15874
  · exact u15875
  · exact u15876
  · exact u15877

def r32534 : Route 9 := (fun mask => (mask,id))

def c32534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32534 : Upper (D 7) (R 7) [12,33,66,258,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258,192] 13 (by decide) (choices 1) [1,16,128] r32534 c32534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15878
  · exact u15879
  · exact u15880

def b32535 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 35 70 280 19 224 224 224 480), lower := (rows 13 35 70 280 19 32 64 128 256), losses := [] }

theorem u32535 : Upper (D 7) (R 7) [12,33,66,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32536 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 70 280 49 226 194 194 450), lower := (rows 13 35 70 280 49 32 64 128 256), losses := [] }

theorem u32536 : Upper (D 7) (R 7) [12,33,66,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32537 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 35 70 280 50 225 193 193 449), lower := (rows 13 35 70 280 50 32 64 128 256), losses := [] }

theorem u32537 : Upper (D 7) (R 7) [12,33,66,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32538 : Route 9 := (fun mask => (mask,id))

def c32538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32538 : Upper (D 7) (R 7) [12,33,66,272,65] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,65] 13 (by decide) (choices 1) [2,128] r32538 c32538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15881
  · exact u15882

def b32539 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 35 70 280 82 161 225 161 417), lower := (rows 13 35 70 280 82 32 64 128 256), losses := [] }

theorem u32539 : Upper (D 7) (R 7) [12,33,66,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32540 : Route 9 := (fun mask => (mask,id))

def c32540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32540 : Upper (D 7) (R 7) [12,33,66,272,96] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,96] 13 (by decide) (choices 1) [1,2,128] r32540 c32540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15883
  · exact u15884
  · exact u15885

def r32541 : Route 9 := (fun mask => (mask,id))

def c32541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32541 : Upper (D 7) (R 7) [12,33,66,272,129] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,129] 13 (by decide) (choices 1) [2,64,128] r32541 c32541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15886
  · exact u15887
  · exact u15888

def r32542 : Route 9 := (fun mask => (mask,id))

def c32542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32542 : Upper (D 7) (R 7) [12,33,66,272,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,130] 13 (by decide) (choices 1) [1,64,128] r32542 c32542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15889
  · exact u15890
  · exact u15891

def r32543 : Route 9 := (fun mask => (mask,id))

def c32543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32543 : Upper (D 7) (R 7) [12,33,66,272,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,160] 13 (by decide) (choices 1) [1,2,64,128] r32543 c32543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15892
  · exact u15893
  · exact u15894
  · exact u15895

def r32544 : Route 9 := (fun mask => (mask,id))

def c32544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32544 : Upper (D 7) (R 7) [12,33,66,272,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272,192] 13 (by decide) (choices 1) [1,2,128] r32544 c32544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15896
  · exact u15897
  · exact u15898

def b32545 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 70 296 19 240 208 208 464), lower := (rows 13 35 70 296 19 32 64 128 256), losses := [] }

theorem u32545 : Upper (D 7) (R 7) [12,33,66,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32546 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 13 35 70 296 81 178 210 146 402), lower := (rows 13 35 70 296 81 32 64 128 256), losses := [] }

theorem u32546 : Upper (D 7) (R 7) [12,33,66,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32547 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 35 70 296 82 177 209 145 401), lower := (rows 13 35 70 296 82 32 64 128 256), losses := [] }

theorem u32547 : Upper (D 7) (R 7) [12,33,66,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32548 : Route 9 := (fun mask => (mask,id))

def c32548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32548 : Upper (D 7) (R 7) [12,33,66,288,129] 13 := by
  apply FastRouting.sound _ _ [12,33,66,288,129] 13 (by decide) (choices 1) [2,16,64,128] r32548 c32548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15899
  · exact u15900
  · exact u15901
  · exact u15902

def r32549 : Route 9 := (fun mask => (mask,id))

def c32549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32549 : Upper (D 7) (R 7) [12,33,66,288,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,288,130] 13 (by decide) (choices 1) [1,16,64,128] r32549 c32549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15903
  · exact u15904
  · exact u15905
  · exact u15906

def r32550 : Route 9 := (fun mask => (mask,id))

def c32550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32550 : Upper (D 7) (R 7) [12,33,66,288,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,288,192] 13 (by decide) (choices 1) [1,2,16,128] r32550 c32550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15907
  · exact u15908
  · exact u15909
  · exact u15910

def b32551 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 16, targets := 160 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 13 35 70 328 19 176 240 176 432), lower := (rows 13 35 70 328 19 32 64 128 256), losses := [] }

theorem u32551 : Upper (D 7) (R 7) [12,33,66,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32552 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,6),(4,1),(4,6),(4,7)], upper := (rows 13 35 70 328 49 178 210 146 402), lower := (rows 13 35 70 328 49 32 64 128 256), losses := [] }

theorem u32552 : Upper (D 7) (R 7) [12,33,66,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32553 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 35 70 328 50 177 209 145 401), lower := (rows 13 35 70 328 50 32 64 128 256), losses := [] }

theorem u32553 : Upper (D 7) (R 7) [12,33,66,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32554 : Route 9 := (fun mask => (mask,id))

def c32554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32554 : Upper (D 7) (R 7) [12,33,66,320,129] 13 := by
  apply FastRouting.sound _ _ [12,33,66,320,129] 13 (by decide) (choices 1) [2,16,128] r32554 c32554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15911
  · exact u15912
  · exact u15913

def r32555 : Route 9 := (fun mask => (mask,id))

def c32555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32555 : Upper (D 7) (R 7) [12,33,66,320,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,320,130] 13 (by decide) (choices 1) [1,16,128] r32555 c32555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15914
  · exact u15915
  · exact u15916

def r32556 : Route 9 := (fun mask => (mask,id))

def c32556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32556 : Upper (D 7) (R 7) [12,33,66,320,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,320,160] 13 (by decide) (choices 1) [1,2,16,128] r32556 c32556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15917
  · exact u15918
  · exact u15919
  · exact u15920

def b32557 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 35 70 392 19 240 240 240 496), lower := (rows 13 35 70 392 19 32 64 128 256), losses := [] }

theorem u32557 : Upper (D 7) (R 7) [12,33,66,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32558 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 16, targets := 192 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 35 70 392 49 242 210 210 466), lower := (rows 13 35 70 392 49 32 64 128 256), losses := [] }

theorem u32558 : Upper (D 7) (R 7) [12,33,66,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32559 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 35 70 392 50 241 209 209 465), lower := (rows 13 35 70 392 50 32 64 128 256), losses := [] }

theorem u32559 : Upper (D 7) (R 7) [12,33,66,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32560 : Route 9 := (fun mask => (mask,id))

def c32560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32560 : Upper (D 7) (R 7) [12,33,66,384,65] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384,65] 13 (by decide) (choices 1) [2,16,128] r32560 c32560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15921
  · exact u15922
  · exact u15923

def b32561 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 35 70 392 82 177 241 177 433), lower := (rows 13 35 70 392 82 32 64 128 256), losses := [] }

theorem u32561 : Upper (D 7) (R 7) [12,33,66,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32562 : Route 9 := (fun mask => (mask,id))

def c32562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32562 : Upper (D 7) (R 7) [12,33,66,384,96] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384,96] 13 (by decide) (choices 1) [1,2,16,128] r32562 c32562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15924
  · exact u15925
  · exact u15926
  · exact u15927

def r32563 : Route 9 := (fun mask => (mask,id))

def c32563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32563 : Upper (D 7) (R 7) [12,33,66,384,129] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384,129] 13 (by decide) (choices 1) [2,16,64] r32563 c32563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15928
  · exact u15929
  · exact u15930

def r32564 : Route 9 := (fun mask => (mask,id))

def c32564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32564 : Upper (D 7) (R 7) [12,33,66,384,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384,130] 13 (by decide) (choices 1) [1,16,64] r32564 c32564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15931
  · exact u15932
  · exact u15933

def r32565 : Route 9 := (fun mask => (mask,id))

def c32565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32565 : Upper (D 7) (R 7) [12,33,66,384,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384,160] 13 (by decide) (choices 1) [1,2,16,64] r32565 c32565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15934
  · exact u15935
  · exact u15936
  · exact u15937

def r32566 : Route 9 := (fun mask => (mask,id))

def c32566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32566 : Upper (D 7) (R 7) [12,33,66,384,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384,192] 13 (by decide) (choices 1) [1,2,16] r32566 c32566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15938
  · exact u15939
  · exact u15940

def b32567 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 35 84 168 19 482 450 450 450), lower := (rows 13 35 84 168 19 32 64 128 256), losses := [] }

theorem u32567 : Upper (D 7) (R 7) [12,33,80,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32568 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 168 81 418 450 386 386), lower := (rows 13 35 84 168 81 32 64 128 256), losses := [] }

theorem u32568 : Upper (D 7) (R 7) [12,33,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32569 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 168 82 419 451 387 387), lower := (rows 13 35 84 168 82 32 64 128 256), losses := [] }

theorem u32569 : Upper (D 7) (R 7) [12,33,80,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32570 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,7),(2,5),(2,7),(4,5)], upper := (rows 13 35 84 168 145 354 322 450 322), lower := (rows 13 35 84 168 145 32 64 128 256), losses := [] }

theorem u32570 : Upper (D 7) (R 7) [12,33,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32571 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7),(2,5),(2,7),(4,5)], upper := (rows 13 35 84 168 146 355 323 451 323), lower := (rows 13 35 84 168 146 32 64 128 256), losses := [{ target := 7, region := (rows 1 3 20 8 16 35 67 0 259), good := (rows 367 355 84 40 374 32 64 0 256) }] }

theorem u32571 : Upper (D 7) (R 7) [12,33,80,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32572 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 168 208 291 323 387 259), lower := (rows 13 35 84 168 208 32 64 128 256), losses := [] }

theorem u32572 : Upper (D 7) (R 7) [12,33,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32573 : Route 9 := (fun mask => (mask,id))

def c32573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32573 : Upper (D 7) (R 7) [12,33,80,160,257] 13 := by
  apply FastRouting.sound _ _ [12,33,80,160,257] 13 (by decide) (choices 1) [2,64,128] r32573 c32573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15941
  · exact u15942
  · exact u15943

def r32574 : Route 9 := (fun mask => (mask,id))

def c32574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32574 : Upper (D 7) (R 7) [12,33,80,160,258] 13 := by
  apply FastRouting.sound _ _ [12,33,80,160,258] 13 (by decide) (choices 1) [1,2,64,128] r32574 c32574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15944
  · exact u15945
  · exact u15946
  · exact u15947

def b32575 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 13 35 84 168 336 163 195 131 387), lower := (rows 13 35 84 168 336 32 64 128 256), losses := [] }

theorem u32575 : Upper (D 7) (R 7) [12,33,80,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32576 : Route 9 := (fun mask => (mask,id))

def c32576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32576 : Upper (D 7) (R 7) [12,33,80,160,384] 13 := by
  apply FastRouting.sound _ _ [12,33,80,160,384] 13 (by decide) (choices 1) [1,2,64] r32576 c32576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15948
  · exact u15949
  · exact u15950

def b32577 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 16, targets := 160 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 13 35 84 200 19 418 482 418 418), lower := (rows 13 35 84 200 19 32 64 128 256), losses := [] }

theorem u32577 : Upper (D 7) (R 7) [12,33,80,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32578 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 456, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,6),(3,0),(4,1),(4,6)], upper := (rows 13 35 84 200 49 418 450 386 386), lower := (rows 13 35 84 200 49 32 64 128 256), losses := [] }

theorem u32578 : Upper (D 7) (R 7) [12,33,80,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32579 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 35 84 200 50 419 451 387 387), lower := (rows 13 35 84 200 50 32 64 128 256), losses := [] }

theorem u32579 : Upper (D 7) (R 7) [12,33,80,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32579
end Delivery.IrregularNine14.P07
