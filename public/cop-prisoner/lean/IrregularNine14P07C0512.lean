import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0213
import IrregularNine14P07C0214
import IrregularNine14P07C0215

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30720 : Route 9 := (fun mask => (mask,id))

def c30720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30720 : Upper (D 7) (R 7) [6,40,17,66,384] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,384] 13 (by decide) (choices 1) [1,64,128] r30720 c30720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12837
  · exact u12838
  · exact u12839

def b30721 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 21, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 21 200 19 480 480 480 480), lower := (rows 7 42 21 200 19 32 64 128 256), losses := [] }

theorem u30721 : Upper (D 7) (R 7) [6,40,17,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30722 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 200 49 482 450 450 450), lower := (rows 7 42 21 200 49 32 64 128 256), losses := [] }

theorem u30722 : Upper (D 7) (R 7) [6,40,17,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30723 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 200 50 481 449 449 449), lower := (rows 7 42 21 200 50 32 64 128 256), losses := [] }

theorem u30723 : Upper (D 7) (R 7) [6,40,17,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30724 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 42 21 200 81 418 482 418 418), lower := (rows 7 42 21 200 81 32 64 128 256), losses := [] }

theorem u30724 : Upper (D 7) (R 7) [6,40,17,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30725 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 21 200 82 417 481 417 417), lower := (rows 7 42 21 200 82 32 64 128 256), losses := [] }

theorem u30725 : Upper (D 7) (R 7) [6,40,17,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30726 : Route 9 := (fun mask => (mask,id))

def c30726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30726 : Upper (D 7) (R 7) [6,40,17,192,96] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192,96] 13 (by decide) (choices 1) [1,2,128,256] r30726 c30726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12840
  · exact u12841
  · exact u12842
  · exact u12843

def b30727 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 21 200 208 291 355 419 291), lower := (rows 7 42 21 200 208 32 64 128 256), losses := [] }

theorem u30727 : Upper (D 7) (R 7) [6,40,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30728 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 42 21 200 273 226 226 226 482), lower := (rows 7 42 21 200 273 32 64 128 256), losses := [] }

theorem u30728 : Upper (D 7) (R 7) [6,40,17,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30729 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 21 200 274 225 225 225 481), lower := (rows 7 42 21 200 274 32 64 128 256), losses := [] }

theorem u30729 : Upper (D 7) (R 7) [6,40,17,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30730 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30730 : Upper (D 7) (R 7) [6,40,17,192,288] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192,288] 13 (by decide) (choices 1) [1,2,64] r30730 c30730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12844
  · exact u12845
  · exact u12846

def r30731 : Route 9 := (fun mask => (mask,id))

def c30731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30731 : Upper (D 7) (R 7) [6,40,17,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192,320] 13 (by decide) (choices 1) [1,2,128] r30731 c30731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12847
  · exact u12848
  · exact u12849

def b30732 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 265 50 224 192 192 448), lower := (rows 7 42 21 265 50 32 64 128 256), losses := [] }

theorem u30732 : Upper (D 7) (R 7) [6,40,17,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30733 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 21 265 82 224 224 224 480), lower := (rows 7 42 21 265 82 32 64 128 256), losses := [] }

theorem u30733 : Upper (D 7) (R 7) [6,40,17,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30734 : Route 9 := (fun mask => (mask,id))

def c30734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30734 : Upper (D 7) (R 7) [6,40,17,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,17,257,96] 13 (by decide) (choices 1) [2,64,128] r30734 c30734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12850
  · exact u12851
  · exact u12852

def r30735 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30735 : Upper (D 7) (R 7) [6,40,17,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,17,257,192] 13 (by decide) (choices 1) [2,64] r30735 c30735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12853
  · exact u12854

def b30736 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 266 49 224 192 192 448), lower := (rows 7 42 21 266 49 32 64 128 256), losses := [] }

theorem u30736 : Upper (D 7) (R 7) [6,40,17,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30737 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 0, region := 490, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 7 42 21 266 81 224 224 224 480), lower := (rows 7 42 21 266 81 32 64 128 256), losses := [] }

theorem u30737 : Upper (D 7) (R 7) [6,40,17,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30738 : Route 9 := (fun mask => (mask,id))

def c30738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30738 : Upper (D 7) (R 7) [6,40,17,258,96] 13 := by
  apply FastRouting.sound _ _ [6,40,17,258,96] 13 (by decide) (choices 1) [1,64,128] r30738 c30738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12855
  · exact u12856
  · exact u12857

def r30739 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30739 : Upper (D 7) (R 7) [6,40,17,258,192] 13 := by
  apply FastRouting.sound _ _ [6,40,17,258,192] 13 (by decide) (choices 1) [1,64] r30739 c30739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12858
  · exact u12859

def b30740 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 21, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 21 328 19 224 224 224 480), lower := (rows 7 42 21 328 19 32 64 128 256), losses := [] }

theorem u30740 : Upper (D 7) (R 7) [6,40,17,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30741 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 328 49 226 194 194 450), lower := (rows 7 42 21 328 49 32 64 128 256), losses := [] }

theorem u30741 : Upper (D 7) (R 7) [6,40,17,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30742 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 21 328 50 225 193 193 449), lower := (rows 7 42 21 328 50 32 64 128 256), losses := [] }

theorem u30742 : Upper (D 7) (R 7) [6,40,17,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30743 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 42 21 328 81 162 226 162 418), lower := (rows 7 42 21 328 81 32 64 128 256), losses := [] }

theorem u30743 : Upper (D 7) (R 7) [6,40,17,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30744 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 21 328 82 161 225 161 417), lower := (rows 7 42 21 328 82 32 64 128 256), losses := [] }

theorem u30744 : Upper (D 7) (R 7) [6,40,17,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30745 : Route 9 := (fun mask => (mask,id))

def c30745 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30745 : Upper (D 7) (R 7) [6,40,17,320,96] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,96] 13 (by decide) (choices 1) [1,2,128] r30745 c30745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12860
  · exact u12861
  · exact u12862

def b30746 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 42 21 328 145 226 226 226 482), lower := (rows 7 42 21 328 145 32 64 128 256), losses := [] }

theorem u30746 : Upper (D 7) (R 7) [6,40,17,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30747 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 42 21 328 146 225 225 225 481), lower := (rows 7 42 21 328 146 32 64 128 256), losses := [] }

theorem u30747 : Upper (D 7) (R 7) [6,40,17,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30748 : Route 9 := (fun mask => (mask,id))

def c30748 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30748 : Upper (D 7) (R 7) [6,40,17,320,160] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,160] 13 (by decide) (choices 1) [1,2,64,128] r30748 c30748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12863
  · exact u12864
  · exact u12865
  · exact u12866

def r30749 : Route 9 := (fun mask => (mask,id))

def c30749 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30749 : Upper (D 7) (R 7) [6,40,17,320,192] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,192] 13 (by decide) (choices 1) [1,2,128] r30749 c30749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12867
  · exact u12868
  · exact u12869

def b30750 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 73 19 480 448 448 448), lower := (rows 7 42 52 73 19 32 64 128 256), losses := [] }

theorem u30750 : Upper (D 7) (R 7) [6,40,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30751 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 52 73 81 418 450 386 386), lower := (rows 7 42 52 73 81 32 64 128 256), losses := [] }

theorem u30751 : Upper (D 7) (R 7) [6,40,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30752 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 42 52 73 82 417 449 385 385), lower := (rows 7 42 52 73 82 32 64 128 256), losses := [] }

theorem u30752 : Upper (D 7) (R 7) [6,40,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30753 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 7 42 52 73 145 482 450 450 450), lower := (rows 7 42 52 73 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 52 490 500 32 64 128 256) }] }

theorem u30753 : Upper (D 7) (R 7) [6,40,48,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30754 : Route 9 := (fun mask => (mask,id))

def c30754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30754 : Upper (D 7) (R 7) [6,40,48,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,130] 13 (by decide) (choices 1) [1,64,128,256] r30754 c30754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12870
  · exact u12871
  · exact u12872
  · exact u12873

def r30755 : Route 9 := (fun mask => (mask,id))

def c30755 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30755 : Upper (D 7) (R 7) [6,40,48,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,192] 13 (by decide) (choices 1) [1,2,128,256] r30755 c30755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12874
  · exact u12875
  · exact u12876
  · exact u12877

def b30756 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 7 42 52 73 273 226 194 194 450), lower := (rows 7 42 52 73 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 52 490 500 32 64 128 256) }] }

theorem u30756 : Upper (D 7) (R 7) [6,40,48,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30757 : Route 9 := (fun mask => (mask,id))

def c30757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30757 : Upper (D 7) (R 7) [6,40,48,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,258] 13 (by decide) (choices 1) [1,64,128] r30757 c30757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12878
  · exact u12879
  · exact u12880

def r30758 : Route 9 := (fun mask => (mask,id))

def c30758 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30758 : Upper (D 7) (R 7) [6,40,48,65,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,320] 13 (by decide) (choices 1) [1,2,128] r30758 c30758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12881
  · exact u12882
  · exact u12883

def r30759 : Route 9 := (fun mask => (mask,id))

def c30759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30759 : Upper (D 7) (R 7) [6,40,48,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,384] 13 (by decide) (choices 1) [1,2,64,128] r30759 c30759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12884
  · exact u12885
  · exact u12886
  · exact u12887

def b30760 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 200 19 481 449 449 449), lower := (rows 7 42 52 200 19 32 64 128 256), losses := [] }

theorem u30760 : Upper (D 7) (R 7) [6,40,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30761 : Route 9 := (fun mask => (mask,id))

def c30761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30761 : Upper (D 7) (R 7) [6,40,48,192,65] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,65] 13 (by decide) (choices 1) [1,2,128,256] r30761 c30761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12888
  · exact u12889
  · exact u12890
  · exact u12891

def b30762 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 42 52 200 82 417 449 385 385), lower := (rows 7 42 52 200 82 32 64 128 256), losses := [] }

theorem u30762 : Upper (D 7) (R 7) [6,40,48,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30763 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 52 200 208 291 323 387 259), lower := (rows 7 42 52 200 208 32 64 128 256), losses := [] }

theorem u30763 : Upper (D 7) (R 7) [6,40,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30764 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30764 : Upper (D 7) (R 7) [6,40,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,257] 13 (by decide) (choices 1) [1,2,64] r30764 c30764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12892
  · exact u12893
  · exact u12894

def r30765 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30765 : Upper (D 7) (R 7) [6,40,48,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,258] 13 (by decide) (choices 1) [1,64] r30765 c30765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12895
  · exact u12896

def r30766 : Route 9 := (fun mask => (mask,id))

def c30766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30766 : Upper (D 7) (R 7) [6,40,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320] 13 (by decide) (choices 1) [1,2,128] r30766 c30766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12897
  · exact u12898
  · exact u12899

def b30767 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 265 19 224 192 192 448), lower := (rows 7 42 52 265 19 32 64 128 256), losses := [] }

theorem u30767 : Upper (D 7) (R 7) [6,40,48,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30768 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 7 42 52 265 81 226 194 194 450), lower := (rows 7 42 52 265 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 75 139 267), good := (rows 486 490 52 490 500 32 64 128 256) }] }

theorem u30768 : Upper (D 7) (R 7) [6,40,48,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30769 : Route 9 := (fun mask => (mask,id))

def c30769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30769 : Upper (D 7) (R 7) [6,40,48,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,48,257,66] 13 (by decide) (choices 1) [1,64,128] r30769 c30769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12900
  · exact u12901
  · exact u12902

def r30770 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30770 : Upper (D 7) (R 7) [6,40,48,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,257,192] 13 (by decide) (choices 1) [1,2,64] r30770 c30770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12903
  · exact u12904
  · exact u12905

def b30771 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 21, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 42 52 328 19 225 193 193 449), lower := (rows 7 42 52 328 19 32 64 128 256), losses := [] }

theorem u30771 : Upper (D 7) (R 7) [6,40,48,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30772 : Route 9 := (fun mask => (mask,id))

def c30772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30772 : Upper (D 7) (R 7) [6,40,48,320,65] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320,65] 13 (by decide) (choices 1) [1,2,128] r30772 c30772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12906
  · exact u12907
  · exact u12908

def b30773 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 42 52 328 82 161 193 129 385), lower := (rows 7 42 52 328 82 32 64 128 256), losses := [] }

theorem u30773 : Upper (D 7) (R 7) [6,40,48,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30774 : Route 9 := (fun mask => (mask,id))

def c30774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30774 : Upper (D 7) (R 7) [6,40,48,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320,129] 13 (by decide) (choices 1) [1,2,64,128] r30774 c30774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12909
  · exact u12910
  · exact u12911
  · exact u12912

def r30775 : Route 9 := (fun mask => (mask,id))

def c30775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30775 : Upper (D 7) (R 7) [6,40,48,320,130] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320,130] 13 (by decide) (choices 1) [1,64,128] r30775 c30775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12913
  · exact u12914
  · exact u12915

def r30776 : Route 9 := (fun mask => (mask,id))

def c30776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30776 : Upper (D 7) (R 7) [6,40,48,320,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320,192] 13 (by decide) (choices 1) [1,2,128] r30776 c30776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12916
  · exact u12917
  · exact u12918

def b30777 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 42 69 25 50 480 448 448 448), lower := (rows 7 42 69 25 50 32 64 128 256), losses := [] }

theorem u30777 : Upper (D 7) (R 7) [6,40,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30778 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 25 82 416 480 416 416), lower := (rows 7 42 69 25 82 32 64 128 256), losses := [] }

theorem u30778 : Upper (D 7) (R 7) [6,40,65,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30779 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 25 112 418 450 386 386), lower := (rows 7 42 69 25 112 32 64 128 256), losses := [] }

theorem u30779 : Upper (D 7) (R 7) [6,40,65,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u30779
end Delivery.IrregularNine14.P07
