import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0413
import IrregularNine14P07C0414

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37860 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 194 7 11 88 432 496 432 432), lower := (rows 37 194 7 11 88 32 64 128 256), losses := [] }

theorem u37860 : Upper (D 7) (R 7) [36,192,3,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37861 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 194 7 11 112 440 472 408 408), lower := (rows 37 194 7 11 112 32 64 128 256), losses := [] }

theorem u37861 : Upper (D 7) (R 7) [36,192,3,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37862 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 194 7 11 280 240 240 240 496), lower := (rows 37 194 7 11 280 32 64 128 256), losses := [] }

theorem u37862 : Upper (D 7) (R 7) [36,192,3,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37863 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 194 7 11 304 248 216 216 472), lower := (rows 37 194 7 11 304 32 64 128 256), losses := [] }

theorem u37863 : Upper (D 7) (R 7) [36,192,3,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37864 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 194 7 11 336 184 248 184 440), lower := (rows 37 194 7 11 336 32 64 128 256), losses := [] }

theorem u37864 : Upper (D 7) (R 7) [36,192,3,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37865 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 37 194 7 25 26 480 480 480 480), lower := (rows 37 194 7 25 26 32 64 128 256), losses := [] }

theorem u37865 : Upper (D 7) (R 7) [36,192,3,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37866 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 25 50 488 456 456 456), lower := (rows 37 194 7 25 50 32 64 128 256), losses := [] }

theorem u37866 : Upper (D 7) (R 7) [36,192,3,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37867 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 7 25 56 482 450 450 450), lower := (rows 37 194 7 25 56 32 64 128 256), losses := [] }

theorem u37867 : Upper (D 7) (R 7) [36,192,3,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37868 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 7 25 82 424 488 424 424), lower := (rows 37 194 7 25 82 32 64 128 256), losses := [] }

theorem u37868 : Upper (D 7) (R 7) [36,192,3,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37869 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 194 7 25 88 418 482 418 418), lower := (rows 37 194 7 25 88 32 64 128 256), losses := [] }

theorem u37869 : Upper (D 7) (R 7) [36,192,3,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37870 : PairBound 9 := { available := 394, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 194 7 25 112 426 458 394 394), lower := (rows 37 194 7 25 112 32 64 128 256), losses := [] }

theorem u37870 : Upper (D 7) (R 7) [36,192,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37871 : PairBound 9 := { available := 298, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 7 25 208 298 362 426 298), lower := (rows 37 194 7 25 208 32 64 128 256), losses := [] }

theorem u37871 : Upper (D 7) (R 7) [36,192,3,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37872 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37872 : Upper (D 7) (R 7) [36,192,3,17,258] 13 := by
  apply FastRouting.sound _ _ [36,192,3,17,258] 13 (by decide) (choices 1) [8,64] r37872 c37872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24809
  · exact u24810

def r37873 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37873 : Upper (D 7) (R 7) [36,192,3,17,264] 13 := by
  apply FastRouting.sound _ _ [36,192,3,17,264] 13 (by decide) (choices 1) [2,64] r37873 c37873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24811
  · exact u24812

def b37874 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 194 7 25 304 234 202 202 458), lower := (rows 37 194 7 25 304 32 64 128 256), losses := [] }

theorem u37874 : Upper (D 7) (R 7) [36,192,3,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37875 : Route 9 := (fun mask => (mask,id))

def c37875 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37875 : Upper (D 7) (R 7) [36,192,3,17,320] 13 := by
  apply FastRouting.sound _ _ [36,192,3,17,320] 13 (by decide) (choices 1) [2,8,128] r37875 c37875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24813
  · exact u24814
  · exact u24815

def b37876 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 7 26 49 488 456 456 456), lower := (rows 37 194 7 26 49 32 64 128 256), losses := [] }

theorem u37876 : Upper (D 7) (R 7) [36,192,3,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37877 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 481, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,0)], upper := (rows 37 194 7 26 56 481 449 449 449), lower := (rows 37 194 7 26 56 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 32 64 128 256), good := (rows 60 194 30 26 56 32 64 128 256) }] }

theorem u37877 : Upper (D 7) (R 7) [36,192,3,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37878 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 194 7 26 81 424 488 424 424), lower := (rows 37 194 7 26 81 32 64 128 256), losses := [] }

theorem u37878 : Upper (D 7) (R 7) [36,192,3,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37879 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 194 7 26 88 417 481 417 417), lower := (rows 37 194 7 26 88 32 64 128 256), losses := [] }

theorem u37879 : Upper (D 7) (R 7) [36,192,3,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37880 : Route 9 := (fun mask => (mask,id))

def c37880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37880 : Upper (D 7) (R 7) [36,192,3,18,96] 13 := by
  apply FastRouting.sound _ _ [36,192,3,18,96] 13 (by decide) (choices 1) [1,8,128,256] r37880 c37880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24816
  · exact u24817
  · exact u24818
  · exact u24819

def b37881 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 7 26 208 297 361 425 297), lower := (rows 37 194 7 26 208 32 64 128 256), losses := [] }

theorem u37881 : Upper (D 7) (R 7) [36,192,3,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37882 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37882 : Upper (D 7) (R 7) [36,192,3,18,257] 13 := by
  apply FastRouting.sound _ _ [36,192,3,18,257] 13 (by decide) (choices 1) [8,64] r37882 c37882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24820
  · exact u24821

def r37883 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37883 : Upper (D 7) (R 7) [36,192,3,18,264] 13 := by
  apply FastRouting.sound _ _ [36,192,3,18,264] 13 (by decide) (choices 1) [1,64] r37883 c37883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24822
  · exact u24823

def r37884 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37884 : Upper (D 7) (R 7) [36,192,3,18,288] 13 := by
  apply FastRouting.sound _ _ [36,192,3,18,288] 13 (by decide) (choices 1) [1,8,64] r37884 c37884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24824
  · exact u24825
  · exact u24826

def r37885 : Route 9 := (fun mask => (mask,id))

def c37885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37885 : Upper (D 7) (R 7) [36,192,3,18,320] 13 := by
  apply FastRouting.sound _ _ [36,192,3,18,320] 13 (by decide) (choices 1) [1,8,128] r37885 c37885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24827
  · exact u24828
  · exact u24829

def b37886 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 7 41 88 434 466 402 402), lower := (rows 37 194 7 41 88 32 64 128 256), losses := [] }

theorem u37886 : Upper (D 7) (R 7) [36,192,3,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37887 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 7 41 274 248 216 216 472), lower := (rows 37 194 7 41 274 32 64 128 256), losses := [] }

theorem u37887 : Upper (D 7) (R 7) [36,192,3,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37888 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 7 41 280 242 210 210 466), lower := (rows 37 194 7 41 280 32 64 128 256), losses := [] }

theorem u37888 : Upper (D 7) (R 7) [36,192,3,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37889 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 7 41 336 186 218 154 410), lower := (rows 37 194 7 41 336 32 64 128 256), losses := [] }

theorem u37889 : Upper (D 7) (R 7) [36,192,3,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37890 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 42 81 440 472 408 408), lower := (rows 37 194 7 42 81 32 64 128 256), losses := [] }

theorem u37890 : Upper (D 7) (R 7) [36,192,3,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37891 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 42 88 433 465 401 401), lower := (rows 37 194 7 42 88 32 64 128 256), losses := [] }

theorem u37891 : Upper (D 7) (R 7) [36,192,3,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37892 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 42 273 248 216 216 472), lower := (rows 37 194 7 42 273 32 64 128 256), losses := [] }

theorem u37892 : Upper (D 7) (R 7) [36,192,3,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37893 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 42 280 241 209 209 465), lower := (rows 37 194 7 42 280 32 64 128 256), losses := [] }

theorem u37893 : Upper (D 7) (R 7) [36,192,3,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37894 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 42 336 185 217 153 409), lower := (rows 37 194 7 42 336 32 64 128 256), losses := [] }

theorem u37894 : Upper (D 7) (R 7) [36,192,3,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37895 : Route 9 := (fun mask => (mask,id))

def c37895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37895 : Upper (D 7) (R 7) [36,192,3,48,65] 13 := by
  apply FastRouting.sound _ _ [36,192,3,48,65] 13 (by decide) (choices 1) [2,8,128,256] r37895 c37895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24830
  · exact u24831
  · exact u24832
  · exact u24833

def b37896 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 7 56 82 425 457 393 393), lower := (rows 37 194 7 56 82 32 64 128 256), losses := [] }

theorem u37896 : Upper (D 7) (R 7) [36,192,3,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37897 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 37 194 7 56 88 419 451 387 387), lower := (rows 37 194 7 56 88 32 64 128 256), losses := [] }

theorem u37897 : Upper (D 7) (R 7) [36,192,3,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37898 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 7 56 208 299 331 395 267), lower := (rows 37 194 7 56 208 32 64 128 256), losses := [] }

theorem u37898 : Upper (D 7) (R 7) [36,192,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37899 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37899 : Upper (D 7) (R 7) [36,192,3,48,257] 13 := by
  apply FastRouting.sound _ _ [36,192,3,48,257] 13 (by decide) (choices 1) [2,8,64] r37899 c37899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24834
  · exact u24835
  · exact u24836

def r37900 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37900 : Upper (D 7) (R 7) [36,192,3,48,258] 13 := by
  apply FastRouting.sound _ _ [36,192,3,48,258] 13 (by decide) (choices 1) [1,8,64] r37900 c37900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24837
  · exact u24838
  · exact u24839

def r37901 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c37901 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37901 : Upper (D 7) (R 7) [36,192,3,48,264] 13 := by
  apply FastRouting.sound _ _ [36,192,3,48,264] 13 (by decide) (choices 1) [1,2,64] r37901 c37901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24840
  · exact u24841
  · exact u24842

def r37902 : Route 9 := (fun mask => (mask,id))

def c37902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37902 : Upper (D 7) (R 7) [36,192,3,48,320] 13 := by
  apply FastRouting.sound _ _ [36,192,3,48,320] 13 (by decide) (choices 1) [1,2,8,128] r37902 c37902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24843
  · exact u24844
  · exact u24845
  · exact u24846

def b37903 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 7 73 146 312 376 440 312), lower := (rows 37 194 7 73 146 32 64 128 256), losses := [] }

theorem u37903 : Upper (D 7) (R 7) [36,192,3,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37904 : Route 9 := (fun mask => (mask,id))

def c37904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37904 : Upper (D 7) (R 7) [36,192,3,65,136] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,136] 13 (by decide) (choices 1) [2,16,256] r37904 c37904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24847
  · exact u24848
  · exact u24849

def r37905 : Route 9 := (fun mask => (mask,id))

def c37905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37905 : Upper (D 7) (R 7) [36,192,3,65,160] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,160] 13 (by decide) (choices 1) [2,8,16,256] r37905 c37905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24850
  · exact u24851
  · exact u24852
  · exact u24853

def r37906 : Route 9 := (fun mask => (mask,id))

def c37906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37906 : Upper (D 7) (R 7) [36,192,3,65,258] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,258] 13 (by decide) (choices 1) [8,16,128] r37906 c37906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24854
  · exact u24855
  · exact u24856

def r37907 : Route 9 := (fun mask => (mask,id))

def c37907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37907 : Upper (D 7) (R 7) [36,192,3,65,264] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,264] 13 (by decide) (choices 1) [2,16,128] r37907 c37907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24857
  · exact u24858
  · exact u24859

def r37908 : Route 9 := (fun mask => (mask,id))

def c37908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37908 : Upper (D 7) (R 7) [36,192,3,65,288] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,288] 13 (by decide) (choices 1) [2,8,16,128] r37908 c37908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24860
  · exact u24861
  · exact u24862
  · exact u24863

def r37909 : Route 9 := (fun mask => (mask,id))

def c37909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37909 : Upper (D 7) (R 7) [36,192,3,65,384] 13 := by
  apply FastRouting.sound _ _ [36,192,3,65,384] 13 (by decide) (choices 1) [2,8,16] r37909 c37909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24864
  · exact u24865
  · exact u24866

def b37910 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 7 74 152 305 369 433 305), lower := (rows 37 194 7 74 152 32 64 128 256), losses := [] }

theorem u37910 : Upper (D 7) (R 7) [36,192,3,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37911 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 7 74 176 313 345 409 281), lower := (rows 37 194 7 74 176 32 64 128 256), losses := [] }

theorem u37911 : Upper (D 7) (R 7) [36,192,3,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37912 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 7 74 273 184 248 184 440), lower := (rows 37 194 7 74 273 32 64 128 256), losses := [] }

theorem u37912 : Upper (D 7) (R 7) [36,192,3,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37913 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 7 74 280 177 241 177 433), lower := (rows 37 194 7 74 280 32 64 128 256), losses := [] }

theorem u37913 : Upper (D 7) (R 7) [36,192,3,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37914 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 7 74 304 185 217 153 409), lower := (rows 37 194 7 74 304 32 64 128 256), losses := [] }

theorem u37914 : Upper (D 7) (R 7) [36,192,3,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37915 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 7 74 400 57 121 185 313), lower := (rows 37 194 7 74 400 32 64 128 256), losses := [] }

theorem u37915 : Upper (D 7) (R 7) [36,192,3,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37916 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 7 88 152 291 355 419 291), lower := (rows 37 194 7 88 152 32 64 128 256), losses := [] }

theorem u37916 : Upper (D 7) (R 7) [36,192,3,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37917 : Route 9 := (fun mask => (mask,id))

def c37917 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37917 : Upper (D 7) (R 7) [36,192,3,80,160] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,160] 13 (by decide) (choices 1) [1,2,8,256] r37917 c37917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24867
  · exact u24868
  · exact u24869
  · exact u24870

def r37918 : Route 9 := (fun mask => (mask,id))

def c37918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37918 : Upper (D 7) (R 7) [36,192,3,80,257] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,257] 13 (by decide) (choices 1) [2,8,128] r37918 c37918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24871
  · exact u24872
  · exact u24873

def r37919 : Route 9 := (fun mask => (mask,id))

def c37919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37919 : Upper (D 7) (R 7) [36,192,3,80,258] 13 := by
  apply FastRouting.sound _ _ [36,192,3,80,258] 13 (by decide) (choices 1) [1,8,128] r37919 c37919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24874
  · exact u24875
  · exact u24876

#print axioms u37919
end Delivery.IrregularNine14.P07
