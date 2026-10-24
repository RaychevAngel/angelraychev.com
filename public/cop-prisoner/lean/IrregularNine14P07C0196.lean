import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0015
import IrregularNine14P07C0016

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11760 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 11 52 328 146 160 97 225 353), lower := (rows 7 11 52 328 146 160 64 128 256), losses := [] }

theorem u11760 : Upper (D 7) (R 7) [6,9,48,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11761 : Route 9 := (fun mask => (mask,id))

def c11761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11761 : Upper (D 7) (R 7) [6,9,48,320,192,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192,1] 13 (by decide) (choices 1) [2,32,128] r11761 c11761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u932
  · exact u933
  · exact u934

def r11762 : Route 9 := (fun mask => (mask,id))

def c11762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11762 : Upper (D 7) (R 7) [6,9,48,320,192,2] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192,2] 13 (by decide) (choices 1) [1,32,128] r11762 c11762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u935
  · exact u936
  · exact u937

def b11763 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 11 52 328 208 160 99 163 291), lower := (rows 7 11 52 328 208 160 64 128 256), losses := [] }

theorem u11763 : Upper (D 7) (R 7) [6,9,48,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11764 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(4,1),(4,5)], upper := (rows 7 11 100 168 81 34 464 400 400), lower := (rows 7 11 100 168 81 34 64 128 256), losses := [] }

theorem u11764 : Upper (D 7) (R 7) [6,9,96,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11765 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 168 81 48 450 386 386), lower := (rows 7 11 100 168 81 48 64 128 256), losses := [] }

theorem u11765 : Upper (D 7) (R 7) [6,9,96,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11765 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11766 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 100 168 81 160 338 402 274), lower := (rows 7 11 100 168 81 160 64 128 256), losses := [] }

theorem u11766 : Upper (D 7) (R 7) [6,9,96,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11767 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,6),(3,6),(4,5)], upper := (rows 7 11 100 168 81 288 210 146 402), lower := (rows 7 11 100 168 81 288 64 128 256), losses := [] }

theorem u11767 : Upper (D 7) (R 7) [6,9,96,160,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11767 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11768 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 7 11 100 168 82 33 464 400 400), lower := (rows 7 11 100 168 82 33 64 128 256), losses := [] }

theorem u11768 : Upper (D 7) (R 7) [6,9,96,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11769 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 168 82 48 449 385 385), lower := (rows 7 11 100 168 82 48 64 128 256), losses := [] }

theorem u11769 : Upper (D 7) (R 7) [6,9,96,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11769 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11770 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 100 168 82 160 337 401 273), lower := (rows 7 11 100 168 82 160 64 128 256), losses := [] }

theorem u11770 : Upper (D 7) (R 7) [6,9,96,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11771 : Route 9 := (fun mask => (mask,id))

def c11771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11771 : Upper (D 7) (R 7) [6,9,96,160,66,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,66,256] 13 (by decide) (choices 1) [1,16,128] r11771 c11771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u938
  · exact u939
  · exact u940

def b11772 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 464, targets := 33 }], pairs := [(2,0),(3,0),(4,0),(4,5)], upper := (rows 7 11 100 168 208 33 338 402 274), lower := (rows 7 11 100 168 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 51 32 67 131 259), good := (rows 470 474 124 188 208 508 64 128 256) }] }

theorem u11772 : Upper (D 7) (R 7) [6,9,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11773 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 168 208 48 323 387 259), lower := (rows 7 11 100 168 208 48 64 128 256), losses := [] }

theorem u11773 : Upper (D 7) (R 7) [6,9,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11773 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11774 : Route 9 := (fun mask => (mask,id))

def c11774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11774 : Upper (D 7) (R 7) [6,9,96,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,192,256] 13 (by decide) (choices 1) [1,2,16] r11774 c11774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u941
  · exact u942
  · exact u943

def b11775 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(2,0),(3,0),(4,1),(4,5)], upper := (rows 7 11 100 168 273 34 208 208 464), lower := (rows 7 11 100 168 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 100 168 508 34 64 128 256) }] }

theorem u11775 : Upper (D 7) (R 7) [6,9,96,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11776 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 100 168 273 48 194 194 450), lower := (rows 7 11 100 168 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 48 67 131 259), good := (rows 454 458 100 168 508 60 64 128 256) }] }

theorem u11776 : Upper (D 7) (R 7) [6,9,96,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11776 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11777 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 168 273 96 210 146 402), lower := (rows 7 11 100 168 273 96 64 128 256), losses := [] }

theorem u11777 : Upper (D 7) (R 7) [6,9,96,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11778 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 100 168 273 160 82 210 338), lower := (rows 7 11 100 168 273 160 64 128 256), losses := [] }

theorem u11778 : Upper (D 7) (R 7) [6,9,96,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11779 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 464, targets := 33 }], pairs := [(2,0),(3,0),(4,0),(4,5)], upper := (rows 7 11 100 168 336 33 210 146 402), lower := (rows 7 11 100 168 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 51 32 67 131 259), good := (rows 470 474 124 188 336 508 64 128 256) }] }

theorem u11779 : Upper (D 7) (R 7) [6,9,96,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11780 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(2,1),(3,1),(4,1),(4,5)], upper := (rows 7 11 100 168 336 34 209 145 401), lower := (rows 7 11 100 168 336 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 40 51 32 67 131 259), good := (rows 469 473 124 188 336 508 64 128 256) }] }

theorem u11780 : Upper (D 7) (R 7) [6,9,96,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11781 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 168 336 48 195 131 387), lower := (rows 7 11 100 168 336 48 64 128 256), losses := [] }

theorem u11781 : Upper (D 7) (R 7) [6,9,96,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11781 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11782 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 100 168 336 160 83 147 275), lower := (rows 7 11 100 168 336 160 64 128 256), losses := [] }

theorem u11782 : Upper (D 7) (R 7) [6,9,96,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11783 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 100 266 145 48 224 224 480), lower := (rows 7 11 100 266 145 48 64 128 256), losses := [] }

theorem u11783 : Upper (D 7) (R 7) [6,9,96,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11783 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11784 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 266 145 96 240 176 432), lower := (rows 7 11 100 266 145 96 64 128 256), losses := [] }

theorem u11784 : Upper (D 7) (R 7) [6,9,96,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11785_16 : Upper (D 7) (R 7) [6,9,96,258,129,128,16] 13 :=
  permutation_upper _ _ _ [6,9,96,258,129,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u944

theorem m11785_32 : Upper (D 7) (R 7) [6,9,96,258,129,128,32] 13 :=
  permutation_upper _ _ _ [6,9,96,258,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u945

def r11785 : Route 9 := (fun mask => (mask,id))

def c11785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11785 : Upper (D 7) (R 7) [6,9,96,258,129,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,258,129,128] 13 (by decide) (choices 1) [16,32] r11785 c11785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11785_16
  · exact m11785_32

def b11786 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 11 100 266 176 33 208 208 464), lower := (rows 7 11 100 266 176 33 64 128 256), losses := [] }

theorem u11786 : Upper (D 7) (R 7) [6,9,96,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11787 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 266 176 48 193 193 449), lower := (rows 7 11 100 266 176 48 64 128 256), losses := [] }

theorem u11787 : Upper (D 7) (R 7) [6,9,96,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11787 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11788 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 266 176 96 209 145 401), lower := (rows 7 11 100 266 176 96 64 128 256), losses := [] }

theorem u11788 : Upper (D 7) (R 7) [6,9,96,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11789 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 100 266 176 160 81 209 337), lower := (rows 7 11 100 266 176 160 64 128 256), losses := [] }

theorem u11789 : Upper (D 7) (R 7) [6,9,96,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11790 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 280 50 33 192 192 448), lower := (rows 7 11 100 280 50 33 64 128 256), losses := [] }

theorem u11790 : Upper (D 7) (R 7) [6,9,96,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11791 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 280 50 96 193 129 385), lower := (rows 7 11 100 280 50 96 64 128 256), losses := [] }

theorem u11791 : Upper (D 7) (R 7) [6,9,96,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11792 : Route 9 := (fun mask => (mask,id))

def c11792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11792 : Upper (D 7) (R 7) [6,9,96,272,34,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,34,128] 13 (by decide) (choices 1) [1,128] r11792 c11792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u946
  · exact u947

def b11793 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 100 280 145 34 224 224 480), lower := (rows 7 11 100 280 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 486 494 484 476 508 486 64 128 256) },{ target := 1, region := (rows 1 0 36 9 17 32 100 164 292), good := (rows 477 25 484 280 153 484 64 128 256) }] }

theorem u11793 : Upper (D 7) (R 7) [6,9,96,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11794 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 280 145 96 226 162 418), lower := (rows 7 11 100 280 145 96 64 128 256), losses := [] }

theorem u11794 : Upper (D 7) (R 7) [6,9,96,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11795_2 : Upper (D 7) (R 7) [6,9,96,272,129,128,2] 13 :=
  permutation_upper _ _ _ [6,9,96,272,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u948

theorem m11795_32 : Upper (D 7) (R 7) [6,9,96,272,129,128,32] 13 :=
  permutation_upper _ _ _ [6,9,96,272,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u949

def r11795 : Route 9 := (fun mask => (mask,id))

def c11795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11795 : Upper (D 7) (R 7) [6,9,96,272,129,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,129,128] 13 (by decide) (choices 1) [2,32] r11795 c11795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11795_2
  · exact m11795_32

def b11796 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 11 100 280 146 33 224 224 480), lower := (rows 7 11 100 280 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 100 164 292), good := (rows 478 26 492 280 146 508 64 128 256) }] }

theorem u11796 : Upper (D 7) (R 7) [6,9,96,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11797 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 280 146 96 225 161 417), lower := (rows 7 11 100 280 146 96 64 128 256), losses := [] }

theorem u11797 : Upper (D 7) (R 7) [6,9,96,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11798_1 : Upper (D 7) (R 7) [6,9,96,272,130,128,1] 13 :=
  permutation_upper _ _ _ [6,9,96,272,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u950

theorem m11798_32 : Upper (D 7) (R 7) [6,9,96,272,130,128,32] 13 :=
  permutation_upper _ _ _ [6,9,96,272,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u951

def r11798 : Route 9 := (fun mask => (mask,id))

def c11798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11798 : Upper (D 7) (R 7) [6,9,96,272,130,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,130,128] 13 (by decide) (choices 1) [1,32] r11798 c11798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11798_1
  · exact m11798_32

def r11799 : Route 9 := (fun mask => (mask,id))

def c11799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11799 : Upper (D 7) (R 7) [6,9,96,272,160,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,160,1] 13 (by decide) (choices 1) [2,128] r11799 c11799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u952
  · exact u953

def r11800 : Route 9 := (fun mask => (mask,id))

def c11800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11800 : Upper (D 7) (R 7) [6,9,96,272,160,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,160,2] 13 (by decide) (choices 1) [1,128] r11800 c11800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u954
  · exact u955

def b11801 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 280 176 96 195 131 387), lower := (rows 7 11 100 280 176 96 64 128 256), losses := [] }

theorem u11801 : Upper (D 7) (R 7) [6,9,96,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11802 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 100 280 176 160 67 195 323), lower := (rows 7 11 100 280 176 160 64 128 256), losses := [] }

theorem u11802 : Upper (D 7) (R 7) [6,9,96,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11803 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(4,1),(4,5)], upper := (rows 7 11 100 296 81 34 208 144 400), lower := (rows 7 11 100 296 81 34 64 128 256), losses := [] }

theorem u11803 : Upper (D 7) (R 7) [6,9,96,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11804 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 296 81 48 194 130 386), lower := (rows 7 11 100 296 81 48 64 128 256), losses := [] }

theorem u11804 : Upper (D 7) (R 7) [6,9,96,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11804 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11805 : Route 9 := (fun mask => (mask,id))

def c11805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11805 : Upper (D 7) (R 7) [6,9,96,288,65,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,65,128] 13 (by decide) (choices 1) [2,16,128] r11805 c11805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u956
  · exact u957
  · exact u958

def b11806 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 208, targets := 33 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 7 11 100 296 82 33 208 144 400), lower := (rows 7 11 100 296 82 33 64 128 256), losses := [] }

theorem u11806 : Upper (D 7) (R 7) [6,9,96,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11807 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 296 82 48 193 129 385), lower := (rows 7 11 100 296 82 48 64 128 256), losses := [] }

theorem u11807 : Upper (D 7) (R 7) [6,9,96,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11807 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11808 : Route 9 := (fun mask => (mask,id))

def c11808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11808 : Upper (D 7) (R 7) [6,9,96,288,66,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,66,128] 13 (by decide) (choices 1) [1,16,128] r11808 c11808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u959
  · exact u960
  · exact u961

def b11809 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,0),(3,0),(4,1),(4,5)], upper := (rows 7 11 100 296 145 34 208 208 464), lower := (rows 7 11 100 296 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 100 296 508 34 64 128 256) }] }

theorem u11809 : Upper (D 7) (R 7) [6,9,96,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11810 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 100 296 145 48 194 194 450), lower := (rows 7 11 100 296 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 48 67 131 259), good := (rows 454 458 100 296 508 60 64 128 256) }] }

theorem u11810 : Upper (D 7) (R 7) [6,9,96,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11810 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11811 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 296 145 96 210 146 402), lower := (rows 7 11 100 296 145 96 64 128 256), losses := [] }

theorem u11811 : Upper (D 7) (R 7) [6,9,96,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11812 : Route 9 := (fun mask => (mask,id))

def c11812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11812 : Upper (D 7) (R 7) [6,9,96,288,129,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,129,128] 13 (by decide) (choices 1) [2,16] r11812 c11812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u962
  · exact u963

def b11813 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 208, targets := 33 }], pairs := [(2,0),(3,0),(4,0),(4,5)], upper := (rows 7 11 100 296 146 33 208 208 464), lower := (rows 7 11 100 296 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 19 32 115 179 307), good := (rows 478 478 492 492 466 508 64 128 256) }] }

theorem u11813 : Upper (D 7) (R 7) [6,9,96,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11814 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 11 100 296 146 48 193 193 449), lower := (rows 7 11 100 296 146 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 48 67 131 259), good := (rows 453 457 100 296 508 60 64 128 256) }] }

theorem u11814 : Upper (D 7) (R 7) [6,9,96,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11814 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11815 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 296 146 96 209 145 401), lower := (rows 7 11 100 296 146 96 64 128 256), losses := [] }

theorem u11815 : Upper (D 7) (R 7) [6,9,96,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11816 : Route 9 := (fun mask => (mask,id))

def c11816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11816 : Upper (D 7) (R 7) [6,9,96,288,130,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288,130,128] 13 (by decide) (choices 1) [1,16] r11816 c11816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u964
  · exact u965

def b11817 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 208, targets := 33 }], pairs := [(2,0),(3,0),(4,0),(4,5)], upper := (rows 7 11 100 296 208 33 210 146 402), lower := (rows 7 11 100 296 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 51 32 67 131 259), good := (rows 470 474 124 316 208 508 64 128 256) }] }

theorem u11817 : Upper (D 7) (R 7) [6,9,96,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11818 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,1),(3,1),(4,1),(4,5)], upper := (rows 7 11 100 296 208 34 209 145 401), lower := (rows 7 11 100 296 208 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 40 51 32 67 131 259), good := (rows 469 473 124 316 208 508 64 128 256) }] }

theorem u11818 : Upper (D 7) (R 7) [6,9,96,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11819 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 296 208 48 195 131 387), lower := (rows 7 11 100 296 208 48 64 128 256), losses := [] }

theorem u11819 : Upper (D 7) (R 7) [6,9,96,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11819 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11819
end Delivery.IrregularNine14.P07
