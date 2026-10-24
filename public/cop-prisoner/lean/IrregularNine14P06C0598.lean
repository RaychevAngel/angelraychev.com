import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0333
import IrregularNine14P06C0334
import IrregularNine14P06C0335

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35880 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 44 25 84 419 451 387 387), lower := (rows 35 70 44 25 84 32 64 128 256), losses := [] }

theorem u35880 : Upper (D 6) (R 6) [34,68,40,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35881 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 44 25 145 358 326 454 326), lower := (rows 35 70 44 25 145 32 64 128 256), losses := [] }

theorem u35881 : Upper (D 6) (R 6) [34,68,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35882 : Route 9 := (fun mask => (mask,id))

def c35882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35882 : Upper (D 6) (R 6) [34,68,40,17,130] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,130] 13 (by decide) (choices 1) [1,4,64,256] r35882 c35882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20008
  · exact u20009
  · exact u20010
  · exact u20011

def r35883 : Route 9 := (fun mask => (mask,id))

def c35883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35883 : Upper (D 6) (R 6) [34,68,40,17,132] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,132] 13 (by decide) (choices 1) [1,2,64,256] r35883 c35883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20012
  · exact u20013
  · exact u20014
  · exact u20015

def r35884 : Route 9 := (fun mask => (mask,id))

def c35884 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35884 : Upper (D 6) (R 6) [34,68,40,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,192] 13 (by decide) (choices 1) [1,2,4,256] r35884 c35884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20016
  · exact u20017
  · exact u20018
  · exact u20019

def r35885 : Route 9 := (fun mask => (mask,id))

def c35885 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35885 : Upper (D 6) (R 6) [34,68,40,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,384] 13 (by decide) (choices 1) [1,2,4,64] r35885 c35885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20020
  · exact u20021
  · exact u20022
  · exact u20023

def b35886 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 44 26 21 481 449 449 449), lower := (rows 35 70 44 26 21 32 64 128 256), losses := [] }

theorem u35886 : Upper (D 6) (R 6) [34,68,40,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35887 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c35887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35887 : Upper (D 6) (R 6) [34,68,40,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,65] 13 (by decide) (choices 1) [1,4,128] r35887 c35887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20024
  · exact u20025
  · exact u20026

def b35888 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 44 26 84 417 449 385 385), lower := (rows 35 70 44 26 84 32 64 128 256), losses := [] }

theorem u35888 : Upper (D 6) (R 6) [34,68,40,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35889 : Route 9 := (fun mask => (mask,id))

def c35889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35889 : Upper (D 6) (R 6) [34,68,40,18,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,129] 13 (by decide) (choices 1) [1,4,64,256] r35889 c35889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20027
  · exact u20028
  · exact u20029
  · exact u20030

def r35890 : Route 9 := (fun mask => (mask,id))

def c35890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35890 : Upper (D 6) (R 6) [34,68,40,18,132] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,132] 13 (by decide) (choices 1) [1,64,256] r35890 c35890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20031
  · exact u20032
  · exact u20033

def r35891 : Route 9 := (fun mask => (mask,id))

def c35891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35891 : Upper (D 6) (R 6) [34,68,40,18,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,192] 13 (by decide) (choices 1) [1,4,256] r35891 c35891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20034
  · exact u20035
  · exact u20036

def r35892 : Route 9 := (fun mask => (mask,id))

def c35892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35892 : Upper (D 6) (R 6) [34,68,40,18,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,384] 13 (by decide) (choices 1) [1,4,64] r35892 c35892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20037
  · exact u20038
  · exact u20039

def b35893 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 44 73 19 436 468 404 404), lower := (rows 35 70 44 73 19 32 64 128 256), losses := [] }

theorem u35893 : Upper (D 6) (R 6) [34,68,40,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35894 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 35 70 44 73 21 434 466 402 402), lower := (rows 35 70 44 73 21 32 64 128 256), losses := [] }

theorem u35894 : Upper (D 6) (R 6) [34,68,40,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35895 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,0),(4,5)], upper := (rows 35 70 44 73 22 433 465 401 401), lower := (rows 35 70 44 73 22 32 64 128 256), losses := [] }

theorem u35895 : Upper (D 6) (R 6) [34,68,40,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35896 : Route 9 := (fun mask => (mask,id))

def c35896 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35896 : Upper (D 6) (R 6) [34,68,40,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,65,129] 13 (by decide) (choices 1) [2,4,16,256] r35896 c35896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20040
  · exact u20041
  · exact u20042
  · exact u20043

def b35897 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 44 73 146 309 341 405 277), lower := (rows 35 70 44 73 146 32 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 42 0 138 266), good := (rows 435 439 428 445 435 32 0 128 256) }] }

theorem u35897 : Upper (D 6) (R 6) [34,68,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35898 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 44 73 148 307 339 403 275), lower := (rows 35 70 44 73 148 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 26 35 0 131 259), good := (rows 435 439 60 445 148 32 0 128 256) }] }

theorem u35898 : Upper (D 6) (R 6) [34,68,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35899 : Route 9 := (fun mask => (mask,id))

def c35899 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35899 : Upper (D 6) (R 6) [34,68,40,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,65,384] 13 (by decide) (choices 1) [1,2,4,16] r35899 c35899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20044
  · exact u20045
  · exact u20046
  · exact u20047

def b35900 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 44 88 19 421 453 389 389), lower := (rows 35 70 44 88 19 32 64 128 256), losses := [] }

theorem u35900 : Upper (D 6) (R 6) [34,68,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35901 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 35 70 44 88 21 419 451 387 387), lower := (rows 35 70 44 88 21 32 64 128 256), losses := [] }

theorem u35901 : Upper (D 6) (R 6) [34,68,40,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35902 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 44 88 22 417 449 385 385), lower := (rows 35 70 44 88 22 32 64 128 256), losses := [] }

theorem u35902 : Upper (D 6) (R 6) [34,68,40,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35903 : Route 9 := (fun mask => (mask,id))

def c35903 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35903 : Upper (D 6) (R 6) [34,68,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,80,129] 13 (by decide) (choices 1) [1,2,4,256] r35903 c35903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20048
  · exact u20049
  · exact u20050
  · exact u20051

def b35904 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 44 88 146 293 325 389 261), lower := (rows 35 70 44 88 146 32 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 42 0 138 266), good := (rows 435 439 428 445 435 32 0 128 256) }] }

theorem u35904 : Upper (D 6) (R 6) [34,68,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35905 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 44 88 148 291 323 387 259), lower := (rows 35 70 44 88 148 32 64 128 256), losses := [] }

theorem u35905 : Upper (D 6) (R 6) [34,68,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35906 : Route 9 := (fun mask => (mask,id))

def c35906 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35906 : Upper (D 6) (R 6) [34,68,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,80,384] 13 (by decide) (choices 1) [1,2,4] r35906 c35906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20052
  · exact u20053
  · exact u20054

def b35907 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 44 137 19 372 340 468 340), lower := (rows 35 70 44 137 19 32 64 128 256), losses := [] }

theorem u35907 : Upper (D 6) (R 6) [34,68,40,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35908 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 322, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 35 70 44 137 21 370 338 466 338), lower := (rows 35 70 44 137 21 32 64 128 256), losses := [] }

theorem u35908 : Upper (D 6) (R 6) [34,68,40,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35909 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 44 137 22 369 337 465 337), lower := (rows 35 70 44 137 22 32 64 128 256), losses := [] }

theorem u35909 : Upper (D 6) (R 6) [34,68,40,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35910 : Route 9 := (fun mask => (mask,id))

def c35910 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35910 : Upper (D 6) (R 6) [34,68,40,129,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,65] 13 (by decide) (choices 1) [2,4,16,256] r35910 c35910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20055
  · exact u20056
  · exact u20057
  · exact u20058

def b35911 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 44 137 82 309 341 405 277), lower := (rows 35 70 44 137 82 32 64 128 256), losses := [] }

theorem u35911 : Upper (D 6) (R 6) [34,68,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35912 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 44 137 84 307 339 403 275), lower := (rows 35 70 44 137 84 32 64 128 256), losses := [] }

theorem u35912 : Upper (D 6) (R 6) [34,68,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35913 : Route 9 := (fun mask => (mask,id))

def c35913 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35913 : Upper (D 6) (R 6) [34,68,40,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,257] 13 (by decide) (choices 1) [2,4,16,64] r35913 c35913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20059
  · exact u20060
  · exact u20061
  · exact u20062

def r35914 : Route 9 := (fun mask => (mask,id))

def c35914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35914 : Upper (D 6) (R 6) [34,68,40,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,258] 13 (by decide) (choices 1) [1,4,16,64] r35914 c35914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20063
  · exact u20064
  · exact u20065
  · exact u20066

def r35915 : Route 9 := (fun mask => (mask,id))

def c35915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35915 : Upper (D 6) (R 6) [34,68,40,129,260] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,260] 13 (by decide) (choices 1) [1,2,16,64] r35915 c35915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20067
  · exact u20068
  · exact u20069
  · exact u20070

def r35916 : Route 9 := (fun mask => (mask,id))

def c35916 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35916 : Upper (D 6) (R 6) [34,68,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,320] 13 (by decide) (choices 1) [1,2,4,16] r35916 c35916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20071
  · exact u20072
  · exact u20073
  · exact u20074

def r35917 : Route 9 := (fun mask => (mask,id))

def c35917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35917 : Upper (D 6) (R 6) [34,68,40,130,5] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,5] 13 (by decide) (choices 1) [1,16,64,256] r35917 c35917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20075
  · exact u20076
  · exact u20077
  · exact u20078

def r35918 : Route 9 := (fun mask => (mask,id))

def c35918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35918 : Upper (D 6) (R 6) [34,68,40,130,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,65] 13 (by decide) (choices 1) [1,4,16,256] r35918 c35918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20079
  · exact u20080
  · exact u20081
  · exact u20082

def b35919 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 44 138 84 305 337 401 273), lower := (rows 35 70 44 138 84 32 64 128 256), losses := [] }

theorem u35919 : Upper (D 6) (R 6) [34,68,40,130,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35920 : Route 9 := (fun mask => (mask,id))

def c35920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35920 : Upper (D 6) (R 6) [34,68,40,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,257] 13 (by decide) (choices 1) [1,4,16,64] r35920 c35920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20083
  · exact u20084
  · exact u20085
  · exact u20086

def r35921 : Route 9 := (fun mask => (mask,id))

def c35921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35921 : Upper (D 6) (R 6) [34,68,40,130,260] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,260] 13 (by decide) (choices 1) [1,16,64] r35921 c35921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20087
  · exact u20088
  · exact u20089

def r35922 : Route 9 := (fun mask => (mask,id))

def c35922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35922 : Upper (D 6) (R 6) [34,68,40,130,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,320] 13 (by decide) (choices 1) [1,4,16] r35922 c35922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20090
  · exact u20091
  · exact u20092

def b35923 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 44 152 19 357 325 453 325), lower := (rows 35 70 44 152 19 32 64 128 256), losses := [] }

theorem u35923 : Upper (D 6) (R 6) [34,68,40,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35924 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 35 70 44 152 21 355 323 451 323), lower := (rows 35 70 44 152 21 32 64 128 256), losses := [] }

theorem u35924 : Upper (D 6) (R 6) [34,68,40,144,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35925 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 44 152 22 353 321 449 321), lower := (rows 35 70 44 152 22 32 64 128 256), losses := [] }

theorem u35925 : Upper (D 6) (R 6) [34,68,40,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35926 : Route 9 := (fun mask => (mask,id))

def c35926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35926 : Upper (D 6) (R 6) [34,68,40,144,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,65] 13 (by decide) (choices 1) [1,2,4,256] r35926 c35926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20093
  · exact u20094
  · exact u20095
  · exact u20096

def b35927 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 44 152 82 293 325 389 261), lower := (rows 35 70 44 152 82 32 64 128 256), losses := [] }

theorem u35927 : Upper (D 6) (R 6) [34,68,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35928 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 44 152 84 291 323 387 259), lower := (rows 35 70 44 152 84 32 64 128 256), losses := [] }

theorem u35928 : Upper (D 6) (R 6) [34,68,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35929 : Route 9 := (fun mask => (mask,id))

def c35929 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35929 : Upper (D 6) (R 6) [34,68,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,257] 13 (by decide) (choices 1) [1,2,4,64] r35929 c35929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20097
  · exact u20098
  · exact u20099
  · exact u20100

def r35930 : Route 9 := (fun mask => (mask,id))

def c35930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35930 : Upper (D 6) (R 6) [34,68,40,144,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,258] 13 (by decide) (choices 1) [1,4,64] r35930 c35930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20101
  · exact u20102
  · exact u20103

def r35931 : Route 9 := (fun mask => (mask,id))

def c35931 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35931 : Upper (D 6) (R 6) [34,68,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,260] 13 (by decide) (choices 1) [1,2,64] r35931 c35931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20104
  · exact u20105
  · exact u20106

def r35932 : Route 9 := (fun mask => (mask,id))

def c35932 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35932 : Upper (D 6) (R 6) [34,68,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,320] 13 (by decide) (choices 1) [1,2,4] r35932 c35932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20107
  · exact u20108
  · exact u20109

def b35933 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 44 200 19 309 341 405 277), lower := (rows 35 70 44 200 19 32 64 128 256), losses := [] }

theorem u35933 : Upper (D 6) (R 6) [34,68,40,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35934 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 322, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 35 70 44 200 21 307 339 403 275), lower := (rows 35 70 44 200 21 32 64 128 256), losses := [] }

theorem u35934 : Upper (D 6) (R 6) [34,68,40,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35935 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,0),(4,5)], upper := (rows 35 70 44 200 22 305 337 401 273), lower := (rows 35 70 44 200 22 32 64 128 256), losses := [] }

theorem u35935 : Upper (D 6) (R 6) [34,68,40,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35936 : Route 9 := (fun mask => (mask,id))

def c35936 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35936 : Upper (D 6) (R 6) [34,68,40,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,257] 13 (by decide) (choices 1) [1,2,4,16] r35936 c35936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20110
  · exact u20111
  · exact u20112
  · exact u20113

def r35937 : Route 9 := (fun mask => (mask,id))

def c35937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35937 : Upper (D 6) (R 6) [34,68,40,192,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,258] 13 (by decide) (choices 1) [1,4,16] r35937 c35937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20114
  · exact u20115
  · exact u20116

def r35938 : Route 9 := (fun mask => (mask,id))

def c35938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35938 : Upper (D 6) (R 6) [34,68,40,192,260] 13 := by
  apply FastRouting.sound _ _ [34,68,40,192,260] 13 (by decide) (choices 1) [1,2,16] r35938 c35938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20117
  · exact u20118
  · exact u20119

def b35939 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 44 392 19 117 85 213 341), lower := (rows 35 70 44 392 19 32 64 128 256), losses := [] }

theorem u35939 : Upper (D 6) (R 6) [34,68,40,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35939
end Delivery.IrregularNine14.P06
