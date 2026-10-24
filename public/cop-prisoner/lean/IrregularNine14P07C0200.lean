import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0017
import IrregularNine14P07C0018

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12000 : Route 9 := (fun mask => (mask,id))

def c12000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12000 : Upper (D 7) (R 7) [6,33,9,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,288,128] 13 (by decide) (choices 1) [2,128] r12000 c12000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1060
  · exact u1061

def b12001 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 88 400 34 224 224 480), lower := (rows 7 35 13 88 400 34 64 128 256), losses := [] }

theorem u12001 : Upper (D 7) (R 7) [6,33,9,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12002 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 88 400 96 226 162 418), lower := (rows 7 35 13 88 400 96 64 128 256), losses := [] }

theorem u12002 : Upper (D 7) (R 7) [6,33,9,80,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12003 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 7 35 13 88 400 160 98 226 354), lower := (rows 7 35 13 88 400 160 64 128 256), losses := [{ target := 6, region := (rows 13 10 12 8 16 176 0 128 256), good := (rows 7 35 15 63 432 160 0 160 256) }] }

theorem u12003 : Upper (D 7) (R 7) [6,33,9,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12004 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 200 82 48 480 416 416), lower := (rows 7 35 13 200 82 48 64 128 256), losses := [] }

theorem u12004 : Upper (D 7) (R 7) [6,33,9,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12004 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12005 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 13 200 82 160 368 432 304), lower := (rows 7 35 13 200 82 160 64 128 256), losses := [] }

theorem u12005 : Upper (D 7) (R 7) [6,33,9,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12006 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 424, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 13 200 82 288 240 176 432), lower := (rows 7 35 13 200 82 288 64 128 256), losses := [] }

theorem u12006 : Upper (D 7) (R 7) [6,33,9,192,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12006 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12007 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 200 112 34 464 400 400), lower := (rows 7 35 13 200 112 34 64 128 256), losses := [] }

theorem u12007 : Upper (D 7) (R 7) [6,33,9,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12008 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 200 112 48 450 386 386), lower := (rows 7 35 13 200 112 48 64 128 256), losses := [] }

theorem u12008 : Upper (D 7) (R 7) [6,33,9,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12008 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12009 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 13 200 112 160 338 402 274), lower := (rows 7 35 13 200 112 160 64 128 256), losses := [] }

theorem u12009 : Upper (D 7) (R 7) [6,33,9,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12010 : Route 9 := (fun mask => (mask,id))

def c12010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12010 : Upper (D 7) (R 7) [6,33,9,192,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192,96,256] 13 (by decide) (choices 1) [2,16,128] r12010 c12010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1062
  · exact u1063
  · exact u1064

def b12011 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 13 200 274 48 224 224 480), lower := (rows 7 35 13 200 274 48 64 128 256), losses := [] }

theorem u12011 : Upper (D 7) (R 7) [6,33,9,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12011 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12012 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 200 274 96 240 176 432), lower := (rows 7 35 13 200 274 96 64 128 256), losses := [] }

theorem u12012 : Upper (D 7) (R 7) [6,33,9,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12013 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 200 304 34 208 208 464), lower := (rows 7 35 13 200 304 34 64 128 256), losses := [] }

theorem u12013 : Upper (D 7) (R 7) [6,33,9,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12014 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 13 200 304 48 194 194 450), lower := (rows 7 35 13 200 304 48 64 128 256), losses := [] }

theorem u12014 : Upper (D 7) (R 7) [6,33,9,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12014 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12015 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 200 304 96 210 146 402), lower := (rows 7 35 13 200 304 96 64 128 256), losses := [] }

theorem u12015 : Upper (D 7) (R 7) [6,33,9,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12016 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 200 336 34 240 176 432), lower := (rows 7 35 13 200 336 34 64 128 256), losses := [] }

theorem u12016 : Upper (D 7) (R 7) [6,33,9,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12017 : Route 9 := (fun mask => (mask,id))

def c12017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12017 : Upper (D 7) (R 7) [6,33,9,192,320,16] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192,320,16] 13 (by decide) (choices 1) [2,32,128] r12017 c12017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1065
  · exact u1066
  · exact u1067

def b12018 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 39, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 13 200 336 160 114 178 306), lower := (rows 7 35 13 200 336 160 64 128 256), losses := [] }

theorem u12018 : Upper (D 7) (R 7) [6,33,9,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12019 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 424, targets := 2 }], pairs := [(0,6),(3,0),(3,1),(4,0)], upper := (rows 7 35 13 280 82 96 224 160 416), lower := (rows 7 35 13 280 82 96 64 128 256), losses := [{ target := 6, region := (rows 17 2 28 24 16 32 0 162 290), good := (rows 391 419 13 285 415 416 0 128 256) }] }

theorem u12019 : Upper (D 7) (R 7) [6,33,9,272,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12020 : Route 9 := (fun mask => (mask,id))

def c12020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12020 : Upper (D 7) (R 7) [6,33,9,272,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,272,66,128] 13 (by decide) (choices 1) [32,128] r12020 c12020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1068
  · exact u1069

def b12021 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 280 112 34 192 192 448), lower := (rows 7 35 13 280 112 34 64 128 256), losses := [] }

theorem u12021 : Upper (D 7) (R 7) [6,33,9,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12022 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 35 13 280 112 96 194 130 386), lower := (rows 7 35 13 280 112 96 64 128 256), losses := [] }

theorem u12022 : Upper (D 7) (R 7) [6,33,9,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12023 : Route 9 := (fun mask => (mask,id))

def c12023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12023 : Upper (D 7) (R 7) [6,33,9,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,272,96,128] 13 (by decide) (choices 1) [2,128] r12023 c12023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1070
  · exact u1071

def b12024 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 280 208 34 224 224 480), lower := (rows 7 35 13 280 208 34 64 128 256), losses := [] }

theorem u12024 : Upper (D 7) (R 7) [6,33,9,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12025 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 7 35 13 280 208 96 226 162 418), lower := (rows 7 35 13 280 208 96 64 128 256), losses := [{ target := 7, region := (rows 13 10 12 8 16 112 64 0 256), good := (rows 7 35 15 319 112 96 96 0 256) }] }

theorem u12025 : Upper (D 7) (R 7) [6,33,9,272,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12026 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 328 82 48 224 160 416), lower := (rows 7 35 13 328 82 48 64 128 256), losses := [] }

theorem u12026 : Upper (D 7) (R 7) [6,33,9,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12026 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12027 : Route 9 := (fun mask => (mask,id))

def c12027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12027 : Upper (D 7) (R 7) [6,33,9,320,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,66,128] 13 (by decide) (choices 1) [16,32,128] r12027 c12027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1072
  · exact u1073
  · exact u1074

def b12028 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 328 112 34 208 144 400), lower := (rows 7 35 13 328 112 34 64 128 256), losses := [] }

theorem u12028 : Upper (D 7) (R 7) [6,33,9,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12029 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 328 112 48 194 130 386), lower := (rows 7 35 13 328 112 48 64 128 256), losses := [] }

theorem u12029 : Upper (D 7) (R 7) [6,33,9,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12029 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12030 : Route 9 := (fun mask => (mask,id))

def c12030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12030 : Upper (D 7) (R 7) [6,33,9,320,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,96,128] 13 (by decide) (choices 1) [2,16,128] r12030 c12030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1075
  · exact u1076
  · exact u1077

def b12031 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 13 328 146 48 224 224 480), lower := (rows 7 35 13 328 146 48 64 128 256), losses := [] }

theorem u12031 : Upper (D 7) (R 7) [6,33,9,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12031 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12032 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 328 146 96 240 176 432), lower := (rows 7 35 13 328 146 96 64 128 256), losses := [] }

theorem u12032 : Upper (D 7) (R 7) [6,33,9,320,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12033 : Route 9 := (fun mask => (mask,id))

def c12033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12033 : Upper (D 7) (R 7) [6,33,9,320,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,130,128] 13 (by decide) (choices 1) [16,32] r12033 c12033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1078
  · exact u1079

def b12034 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 328 176 34 208 208 464), lower := (rows 7 35 13 328 176 34 64 128 256), losses := [] }

theorem u12034 : Upper (D 7) (R 7) [6,33,9,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12035 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 13 328 176 48 194 194 450), lower := (rows 7 35 13 328 176 48 64 128 256), losses := [] }

theorem u12035 : Upper (D 7) (R 7) [6,33,9,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12035 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12036 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 328 176 96 210 146 402), lower := (rows 7 35 13 328 176 96 64 128 256), losses := [] }

theorem u12036 : Upper (D 7) (R 7) [6,33,9,320,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12037 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 13 328 176 160 82 210 338), lower := (rows 7 35 13 328 176 160 64 128 256), losses := [] }

theorem u12037 : Upper (D 7) (R 7) [6,33,9,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12038 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 328 208 34 240 176 432), lower := (rows 7 35 13 328 208 34 64 128 256), losses := [] }

theorem u12038 : Upper (D 7) (R 7) [6,33,9,320,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12039 : Route 9 := (fun mask => (mask,id))

def c12039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12039 : Upper (D 7) (R 7) [6,33,9,320,192,16] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,192,16] 13 (by decide) (choices 1) [2,32,128] r12039 c12039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1080
  · exact u1081
  · exact u1082

def r12040 : Route 9 := (fun mask => (mask,id))

def c12040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12040 : Upper (D 7) (R 7) [6,33,9,320,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,192,128] 13 (by decide) (choices 1) [2,16,32] r12040 c12040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1083
  · exact u1084
  · exact u1085

def b12041 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 73 176 34 448 448 448), lower := (rows 7 35 28 73 176 34 64 128 256), losses := [] }

theorem u12041 : Upper (D 7) (R 7) [6,33,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12042 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 456, targets := 32 },{ cop := 1, region := 400, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(3,5),(4,0),(4,6)], upper := (rows 7 35 28 73 176 96 450 386 386), lower := (rows 7 35 28 73 176 96 64 128 256), losses := [] }

theorem u12042 : Upper (D 7) (R 7) [6,33,24,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12043 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 73 176 160 322 450 322), lower := (rows 7 35 28 73 176 160 64 128 256), losses := [] }

theorem u12043 : Upper (D 7) (R 7) [6,33,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12044 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,0),(3,5),(4,0)], upper := (rows 7 35 28 73 176 288 194 194 450), lower := (rows 7 35 28 73 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 299 67 131 259), good := (rows 502 498 60 508 176 288 64 128 288) }] }

theorem u12044 : Upper (D 7) (R 7) [6,33,24,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12044 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12045 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 73 304 34 192 192 448), lower := (rows 7 35 28 73 304 34 64 128 256), losses := [] }

theorem u12045 : Upper (D 7) (R 7) [6,33,24,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12046 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 200, targets := 32 },{ cop := 1, region := 400, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(3,5),(4,0),(4,6)], upper := (rows 7 35 28 73 304 96 194 130 386), lower := (rows 7 35 28 73 304 96 64 128 256), losses := [] }

theorem u12046 : Upper (D 7) (R 7) [6,33,24,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12047 : Route 9 := (fun mask => (mask,id))

def c12047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12047 : Upper (D 7) (R 7) [6,33,24,65,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,24,65,288,128] 13 (by decide) (choices 1) [2,128] r12047 c12047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1086
  · exact u1087

def b12048 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 73 400 34 224 224 480), lower := (rows 7 35 28 73 400 34 64 128 256), losses := [] }

theorem u12048 : Upper (D 7) (R 7) [6,33,24,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12049 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 400, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(2,0),(4,0),(4,6)], upper := (rows 7 35 28 73 400 96 226 162 418), lower := (rows 7 35 28 73 400 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 107 67 131 259), good := (rows 502 498 60 508 400 96 96 128 256) }] }

theorem u12049 : Upper (D 7) (R 7) [6,33,24,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12050 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 1, region := 72, targets := 128 }], pairs := [(0,6),(2,0),(3,7),(4,0)], upper := (rows 7 35 28 73 400 160 98 226 354), lower := (rows 7 35 28 73 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 187 67 131 259), good := (rows 502 498 60 508 432 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 176 0 128 256), good := (rows 7 35 63 9 432 160 0 160 256) }] }

theorem u12050 : Upper (D 7) (R 7) [6,33,24,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12051 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 74 176 33 448 448 448), lower := (rows 7 35 28 74 176 33 64 128 256), losses := [] }

theorem u12051 : Upper (D 7) (R 7) [6,33,24,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12052 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 456, targets := 32 },{ cop := 1, region := 400, targets := 64 }], pairs := [(2,1),(3,5),(4,1),(4,6)], upper := (rows 7 35 28 74 176 96 449 385 385), lower := (rows 7 35 28 74 176 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 107 67 131 259), good := (rows 501 497 60 508 176 96 96 128 256) }] }

theorem u12052 : Upper (D 7) (R 7) [6,33,24,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12053 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 74 176 160 321 449 321), lower := (rows 7 35 28 74 176 160 64 128 256), losses := [] }

theorem u12053 : Upper (D 7) (R 7) [6,33,24,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12054 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 35 28 74 176 288 193 193 449), lower := (rows 7 35 28 74 176 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 299 67 131 259), good := (rows 501 497 60 508 176 288 64 128 288) }] }

theorem u12054 : Upper (D 7) (R 7) [6,33,24,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12054 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12055 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 74 304 33 192 192 448), lower := (rows 7 35 28 74 304 33 64 128 256), losses := [] }

theorem u12055 : Upper (D 7) (R 7) [6,33,24,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12056 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 200, targets := 32 },{ cop := 1, region := 400, targets := 64 }], pairs := [(2,1),(3,5),(4,1),(4,6)], upper := (rows 7 35 28 74 304 96 193 129 385), lower := (rows 7 35 28 74 304 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 107 67 131 259), good := (rows 501 497 60 508 304 96 96 128 256) }] }

theorem u12056 : Upper (D 7) (R 7) [6,33,24,66,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12057 : Route 9 := (fun mask => (mask,id))

def c12057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12057 : Upper (D 7) (R 7) [6,33,24,66,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,24,66,288,128] 13 (by decide) (choices 1) [1,128] r12057 c12057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1088
  · exact u1089

def b12058 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 74 400 33 224 224 480), lower := (rows 7 35 28 74 400 33 64 128 256), losses := [] }

theorem u12058 : Upper (D 7) (R 7) [6,33,24,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12059 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,6),(2,1),(4,1),(4,6)], upper := (rows 7 35 28 74 400 96 225 161 417), lower := (rows 7 35 28 74 400 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 107 67 131 259), good := (rows 501 497 60 508 400 96 96 128 256) },{ target := 6, region := (rows 9 2 12 8 27 32 0 130 258), good := (rows 407 435 29 415 400 32 0 128 256) }] }

theorem u12059 : Upper (D 7) (R 7) [6,33,24,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12059
end Delivery.IrregularNine14.P07
