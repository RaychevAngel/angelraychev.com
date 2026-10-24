import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0057

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15900 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 13 35 70 296 145 48 194 194 450), lower := (rows 13 35 70 296 145 48 64 128 256), losses := [] }

theorem u15900 : Upper (D 7) (R 7) [12,33,66,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15900 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15901 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 70 296 145 96 210 146 402), lower := (rows 13 35 70 296 145 96 64 128 256), losses := [] }

theorem u15901 : Upper (D 7) (R 7) [12,33,66,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15902 : Route 9 := (fun mask => (mask,id))

def c15902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15902 : Upper (D 7) (R 7) [12,33,66,288,129,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,288,129,128] 13 (by decide) (choices 1) [2,16] r15902 c15902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3432
  · exact u3433

def b15903 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 296 146 33 208 208 464), lower := (rows 13 35 70 296 146 33 64 128 256), losses := [] }

theorem u15903 : Upper (D 7) (R 7) [12,33,66,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15904 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 456, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 13 35 70 296 146 48 193 193 449), lower := (rows 13 35 70 296 146 48 64 128 256), losses := [] }

theorem u15904 : Upper (D 7) (R 7) [12,33,66,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15904 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15905 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 70 296 146 96 209 145 401), lower := (rows 13 35 70 296 146 96 64 128 256), losses := [] }

theorem u15905 : Upper (D 7) (R 7) [12,33,66,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15906 : Route 9 := (fun mask => (mask,id))

def c15906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15906 : Upper (D 7) (R 7) [12,33,66,288,130,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,288,130,128] 13 (by decide) (choices 1) [1,16] r15906 c15906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3434
  · exact u3435

def b15907 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 296 208 33 210 146 402), lower := (rows 13 35 70 296 208 33 64 128 256), losses := [] }

theorem u15907 : Upper (D 7) (R 7) [12,33,66,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15908 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 70 296 208 34 209 145 401), lower := (rows 13 35 70 296 208 34 64 128 256), losses := [] }

theorem u15908 : Upper (D 7) (R 7) [12,33,66,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15909 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,5),(3,6),(4,5)], upper := (rows 13 35 70 296 208 48 195 131 387), lower := (rows 13 35 70 296 208 48 64 128 256), losses := [] }

theorem u15909 : Upper (D 7) (R 7) [12,33,66,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15909 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15910 : Route 9 := (fun mask => (mask,id))

def c15910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15910 : Upper (D 7) (R 7) [12,33,66,288,192,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,288,192,128] 13 (by decide) (choices 1) [1,2,16] r15910 c15910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3436
  · exact u3437
  · exact u3438

def b15911 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 328 145 34 240 176 432), lower := (rows 13 35 70 328 145 34 64 128 256), losses := [] }

theorem u15911 : Upper (D 7) (R 7) [12,33,66,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15912 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 13 35 70 328 145 48 226 162 418), lower := (rows 13 35 70 328 145 48 64 128 256), losses := [] }

theorem u15912 : Upper (D 7) (R 7) [12,33,66,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15912 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15913 : Route 9 := (fun mask => (mask,id))

def c15913 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15913 : Upper (D 7) (R 7) [12,33,66,320,129,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,320,129,128] 13 (by decide) (choices 1) [2,16,32] r15913 c15913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3439
  · exact u3440
  · exact u3441

def b15914 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 328 146 33 240 176 432), lower := (rows 13 35 70 328 146 33 64 128 256), losses := [] }

theorem u15914 : Upper (D 7) (R 7) [12,33,66,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15915 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 456, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 13 35 70 328 146 48 225 161 417), lower := (rows 13 35 70 328 146 48 64 128 256), losses := [] }

theorem u15915 : Upper (D 7) (R 7) [12,33,66,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15915 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15916 : Route 9 := (fun mask => (mask,id))

def c15916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15916 : Upper (D 7) (R 7) [12,33,66,320,130,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,320,130,128] 13 (by decide) (choices 1) [1,16,32] r15916 c15916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3442
  · exact u3443
  · exact u3444

def b15917 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 328 176 33 210 146 402), lower := (rows 13 35 70 328 176 33 64 128 256), losses := [] }

theorem u15917 : Upper (D 7) (R 7) [12,33,66,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15918 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 328 176 34 209 145 401), lower := (rows 13 35 70 328 176 34 64 128 256), losses := [] }

theorem u15918 : Upper (D 7) (R 7) [12,33,66,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15919 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 328 176 48 195 131 387), lower := (rows 13 35 70 328 176 48 64 128 256), losses := [] }

theorem u15919 : Upper (D 7) (R 7) [12,33,66,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15919 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15920 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 328 176 160 83 147 275), lower := (rows 13 35 70 328 176 160 64 128 256), losses := [] }

theorem u15920 : Upper (D 7) (R 7) [12,33,66,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15921 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 392 81 34 240 176 432), lower := (rows 13 35 70 392 81 34 64 128 256), losses := [] }

theorem u15921 : Upper (D 7) (R 7) [12,33,66,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15922 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 13 35 70 392 81 48 226 162 418), lower := (rows 13 35 70 392 81 48 64 128 256), losses := [] }

theorem u15922 : Upper (D 7) (R 7) [12,33,66,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15923 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,7),(3,6),(4,7)], upper := (rows 13 35 70 392 81 160 114 178 306), lower := (rows 13 35 70 392 81 160 64 128 256), losses := [] }

theorem u15923 : Upper (D 7) (R 7) [12,33,66,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15924 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 392 112 33 210 146 402), lower := (rows 13 35 70 392 112 33 64 128 256), losses := [] }

theorem u15924 : Upper (D 7) (R 7) [12,33,66,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15925 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 392 112 34 209 145 401), lower := (rows 13 35 70 392 112 34 64 128 256), losses := [] }

theorem u15925 : Upper (D 7) (R 7) [12,33,66,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15926 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 392 112 48 195 131 387), lower := (rows 13 35 70 392 112 48 64 128 256), losses := [] }

theorem u15926 : Upper (D 7) (R 7) [12,33,66,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15926 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15927 : Route 9 := (fun mask => (mask,id))

def c15927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15927 : Upper (D 7) (R 7) [12,33,66,384,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384,96,128] 13 (by decide) (choices 1) [1,2,16] r15927 c15927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3445
  · exact u3446
  · exact u3447

def b15928 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 392 145 34 112 240 368), lower := (rows 13 35 70 392 145 34 64 128 256), losses := [] }

theorem u15928 : Upper (D 7) (R 7) [12,33,66,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15929 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7),(2,0),(3,0)], upper := (rows 13 35 70 392 145 48 98 226 354), lower := (rows 13 35 70 392 145 48 64 128 256), losses := [] }

theorem u15929 : Upper (D 7) (R 7) [12,33,66,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15929 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15930 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,7),(2,7),(3,6),(4,6)], upper := (rows 13 35 70 392 145 96 114 178 306), lower := (rows 13 35 70 392 145 96 64 128 256), losses := [] }

theorem u15930 : Upper (D 7) (R 7) [12,33,66,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15931 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 392 146 33 112 240 368), lower := (rows 13 35 70 392 146 33 64 128 256), losses := [] }

theorem u15931 : Upper (D 7) (R 7) [12,33,66,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15932 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 456, targets := 2 },{ cop := 1, region := 68, targets := 128 }], pairs := [(0,1),(2,7),(3,1)], upper := (rows 13 35 70 392 146 48 97 225 353), lower := (rows 13 35 70 392 146 48 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 30 16 48 66 130 258), good := (rows 13 489 461 392 504 56 64 128 256) }] }

theorem u15932 : Upper (D 7) (R 7) [12,33,66,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15932 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15933 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(0,6),(1,7),(3,6),(4,6)], upper := (rows 13 35 70 392 146 96 113 177 305), lower := (rows 13 35 70 392 146 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 30 22 32 0 130 258), good := (rows 29 443 415 392 410 32 0 128 256) },{ target := 7, region := (rows 1 3 4 8 16 100 64 0 256), good := (rows 47 35 102 264 18 96 96 0 256) }] }

theorem u15933 : Upper (D 7) (R 7) [12,33,66,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15934 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 392 176 33 82 210 338), lower := (rows 13 35 70 392 176 33 64 128 256), losses := [] }

theorem u15934 : Upper (D 7) (R 7) [12,33,66,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15935 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 392 176 34 81 209 337), lower := (rows 13 35 70 392 176 34 64 128 256), losses := [] }

theorem u15935 : Upper (D 7) (R 7) [12,33,66,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15936 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 392 176 48 67 195 323), lower := (rows 13 35 70 392 176 48 64 128 256), losses := [] }

theorem u15936 : Upper (D 7) (R 7) [12,33,66,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15936 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15937 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(0,6),(1,7),(3,6),(4,6)], upper := (rows 13 35 70 392 176 96 83 147 275), lower := (rows 13 35 70 392 176 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 15 18 32 0 134 262), good := (rows 397 443 415 392 176 32 0 128 256) },{ target := 7, region := (rows 1 3 4 8 16 100 64 0 256), good := (rows 47 35 102 264 48 96 96 0 256) }] }

theorem u15937 : Upper (D 7) (R 7) [12,33,66,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15938 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 392 208 33 114 178 306), lower := (rows 13 35 70 392 208 33 64 128 256), losses := [] }

theorem u15938 : Upper (D 7) (R 7) [12,33,66,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15939 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 392 208 34 113 177 305), lower := (rows 13 35 70 392 208 34 64 128 256), losses := [] }

theorem u15939 : Upper (D 7) (R 7) [12,33,66,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15940 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 392, targets := 64 },{ cop := 1, region := 68, targets := 128 }], pairs := [(0,6),(2,7),(3,6)], upper := (rows 13 35 70 392 208 48 99 163 291), lower := (rows 13 35 70 392 208 48 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 16 48 0 130 258), good := (rows 13 427 399 392 176 48 0 128 256) }] }

theorem u15940 : Upper (D 7) (R 7) [12,33,66,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15940 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15941 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 468, targets := 32 }], pairs := [(1,6),(1,7),(2,5),(4,5)], upper := (rows 13 35 84 168 273 34 194 194 450), lower := (rows 13 35 84 168 273 34 64 128 256), losses := [] }

theorem u15941 : Upper (D 7) (R 7) [12,33,80,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15942 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 84 168 273 96 194 130 386), lower := (rows 13 35 84 168 273 96 64 128 256), losses := [] }

theorem u15942 : Upper (D 7) (R 7) [12,33,80,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15943 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 84 168 273 160 66 194 322), lower := (rows 13 35 84 168 273 160 64 128 256), losses := [] }

theorem u15943 : Upper (D 7) (R 7) [12,33,80,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15944 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 168 274 33 194 194 450), lower := (rows 13 35 84 168 274 33 64 128 256), losses := [] }

theorem u15944 : Upper (D 7) (R 7) [12,33,80,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15945 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 468, targets := 32 }], pairs := [(1,6),(1,7),(2,5),(4,5)], upper := (rows 13 35 84 168 274 34 193 193 449), lower := (rows 13 35 84 168 274 34 64 128 256), losses := [] }

theorem u15945 : Upper (D 7) (R 7) [12,33,80,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15946 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 84 168 274 96 195 131 387), lower := (rows 13 35 84 168 274 96 64 128 256), losses := [] }

theorem u15946 : Upper (D 7) (R 7) [12,33,80,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15947 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 84 168 274 160 67 195 323), lower := (rows 13 35 84 168 274 160 64 128 256), losses := [] }

theorem u15947 : Upper (D 7) (R 7) [12,33,80,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15948 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 1, region := 468, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0)], upper := (rows 13 35 84 168 400 33 66 194 322), lower := (rows 13 35 84 168 400 33 64 128 256), losses := [] }

theorem u15948 : Upper (D 7) (R 7) [12,33,80,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15949 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(2,5),(4,5)], upper := (rows 13 35 84 168 400 34 67 195 323), lower := (rows 13 35 84 168 400 34 64 128 256), losses := [] }

theorem u15949 : Upper (D 7) (R 7) [12,33,80,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15950 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 84 168 400 96 67 131 259), lower := (rows 13 35 84 168 400 96 64 128 256), losses := [] }

theorem u15950 : Upper (D 7) (R 7) [12,33,80,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15951 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 200, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,6)], upper := (rows 13 35 84 200 273 34 226 162 418), lower := (rows 13 35 84 200 273 34 64 128 256), losses := [] }

theorem u15951 : Upper (D 7) (R 7) [12,33,80,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15952 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 340, targets := 128 }], pairs := [(1,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 84 200 273 160 98 162 290), lower := (rows 13 35 84 200 273 160 64 128 256), losses := [] }

theorem u15952 : Upper (D 7) (R 7) [12,33,80,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15953 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 200 274 33 226 162 418), lower := (rows 13 35 84 200 274 33 64 128 256), losses := [] }

theorem u15953 : Upper (D 7) (R 7) [12,33,80,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15954 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 200, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,6)], upper := (rows 13 35 84 200 274 34 225 161 417), lower := (rows 13 35 84 200 274 34 64 128 256), losses := [] }

theorem u15954 : Upper (D 7) (R 7) [12,33,80,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15955 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 340, targets := 128 }], pairs := [(1,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 84 200 274 160 99 163 291), lower := (rows 13 35 84 200 274 160 64 128 256), losses := [] }

theorem u15955 : Upper (D 7) (R 7) [12,33,80,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15956 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 200 304 33 194 130 386), lower := (rows 13 35 84 200 304 33 64 128 256), losses := [] }

theorem u15956 : Upper (D 7) (R 7) [12,33,80,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15957 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 0, region := 34, targets := 128 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,6),(1,7),(3,5),(4,6)], upper := (rows 13 35 84 200 304 34 195 131 387), lower := (rows 13 35 84 200 304 34 64 128 256), losses := [] }

theorem u15957 : Upper (D 7) (R 7) [12,33,80,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15958 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 340, targets := 128 }], pairs := [(1,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 84 200 304 160 67 131 259), lower := (rows 13 35 84 200 304 160 64 128 256), losses := [] }

theorem u15958 : Upper (D 7) (R 7) [12,33,80,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15959 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 84 200 400 33 98 162 290), lower := (rows 13 35 84 200 400 33 64 128 256), losses := [] }

theorem u15959 : Upper (D 7) (R 7) [12,33,80,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15959
end Delivery.IrregularNine14.P07
