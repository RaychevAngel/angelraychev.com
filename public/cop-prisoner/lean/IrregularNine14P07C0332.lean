import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0090
import IrregularNine14P07C0091

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19920 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 268 73 146 33 240 176 432), lower := (rows 35 70 268 73 146 33 64 128 256), losses := [] }

theorem u19920 : Upper (D 7) (R 7) [34,68,264,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19921 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 268 73 146 48 225 161 417), lower := (rows 35 70 268 73 146 48 64 128 256), losses := [] }

theorem u19921 : Upper (D 7) (R 7) [34,68,264,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19921 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19922 : Route 9 := (fun mask => (mask,id))

def c19922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19922 : Upper (D 7) (R 7) [34,68,264,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,65,130,128] 13 (by decide) (choices 1) [1,16,32] r19922 c19922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5451
  · exact u5452
  · exact u5453

def b19923 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 268 73 176 33 210 146 402), lower := (rows 35 70 268 73 176 33 64 128 256), losses := [] }

theorem u19923 : Upper (D 7) (R 7) [34,68,264,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19924 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 73 176 34 209 145 401), lower := (rows 35 70 268 73 176 34 64 128 256), losses := [] }

theorem u19924 : Upper (D 7) (R 7) [34,68,264,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19925 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 268 73 176 48 195 131 387), lower := (rows 35 70 268 73 176 48 64 128 256), losses := [] }

theorem u19925 : Upper (D 7) (R 7) [34,68,264,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19925 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19926 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 268 73 176 160 83 147 275), lower := (rows 35 70 268 73 176 160 64 128 256), losses := [] }

theorem u19926 : Upper (D 7) (R 7) [34,68,264,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19927 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 70 268 88 145 33 226 162 418), lower := (rows 35 70 268 88 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 26 20 24 16 32 65 129 257), good := (rows 482 70 270 94 478 480 64 128 256) }] }

theorem u19927 : Upper (D 7) (R 7) [34,68,264,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19928 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 88 145 34 225 161 417), lower := (rows 35 70 268 88 145 34 64 128 256), losses := [] }

theorem u19928 : Upper (D 7) (R 7) [34,68,264,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19929 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(1,7),(2,7),(4,6)], upper := (rows 35 70 268 88 145 160 99 163 291), lower := (rows 35 70 268 88 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 26 20 24 16 32 65 0 257), good := (rows 355 70 270 94 351 32 64 0 256) }] }

theorem u19929 : Upper (D 7) (R 7) [34,68,264,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19930 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 70 268 88 146 33 225 161 417), lower := (rows 35 70 268 88 146 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 59 0 187 315), good := (rows 435 439 428 445 435 433 0 128 256) }] }

theorem u19930 : Upper (D 7) (R 7) [34,68,264,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19931 : Route 9 := (fun mask => (mask,id))

def c19931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19931 : Upper (D 7) (R 7) [34,68,264,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,80,130,128] 13 (by decide) (choices 1) [1,32] r19931 c19931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5454
  · exact u5455

def r19932 : Route 9 := (fun mask => (mask,id))

def c19932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19932 : Upper (D 7) (R 7) [34,68,264,80,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,80,160,1] 13 (by decide) (choices 1) [1,2,128] r19932 c19932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5456
  · exact u5457
  · exact u5458

def b19933 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 88 176 34 193 129 385), lower := (rows 35 70 268 88 176 34 64 128 256), losses := [] }

theorem u19933 : Upper (D 7) (R 7) [34,68,264,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19934 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 268 88 176 160 67 131 259), lower := (rows 35 70 268 88 176 160 64 128 256), losses := [] }

theorem u19934 : Upper (D 7) (R 7) [34,68,264,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19935 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 268 104 145 33 210 146 402), lower := (rows 35 70 268 104 145 33 64 128 256), losses := [] }

theorem u19935 : Upper (D 7) (R 7) [34,68,264,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19936 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 104 145 34 209 145 401), lower := (rows 35 70 268 104 145 34 64 128 256), losses := [] }

theorem u19936 : Upper (D 7) (R 7) [34,68,264,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19937 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 70 268 104 145 48 195 131 387), lower := (rows 35 70 268 104 145 48 64 128 256), losses := [] }

theorem u19937 : Upper (D 7) (R 7) [34,68,264,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19937 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19938 : Route 9 := (fun mask => (mask,id))

def c19938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19938 : Upper (D 7) (R 7) [34,68,264,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,96,129,128] 13 (by decide) (choices 1) [1,2,16] r19938 c19938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5459
  · exact u5460
  · exact u5461

def b19939 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 268 104 146 33 209 145 401), lower := (rows 35 70 268 104 146 33 64 128 256), losses := [] }

theorem u19939 : Upper (D 7) (R 7) [34,68,264,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19940 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 268 104 146 48 193 129 385), lower := (rows 35 70 268 104 146 48 64 128 256), losses := [] }

theorem u19940 : Upper (D 7) (R 7) [34,68,264,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19940 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19941 : Route 9 := (fun mask => (mask,id))

def c19941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19941 : Upper (D 7) (R 7) [34,68,264,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,96,130,128] 13 (by decide) (choices 1) [1,16] r19941 c19941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5462
  · exact u5463

def b19942 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 137 81 34 240 176 432), lower := (rows 35 70 268 137 81 34 64 128 256), losses := [] }

theorem u19942 : Upper (D 7) (R 7) [34,68,264,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19943 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 268 137 81 48 226 162 418), lower := (rows 35 70 268 137 81 48 64 128 256), losses := [] }

theorem u19943 : Upper (D 7) (R 7) [34,68,264,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19943 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19944 : Route 9 := (fun mask => (mask,id))

def c19944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19944 : Upper (D 7) (R 7) [34,68,264,129,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,65,128] 13 (by decide) (choices 1) [2,16,32] r19944 c19944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5464
  · exact u5465
  · exact u5466

def b19945 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,0),(4,7)], upper := (rows 35 70 268 137 112 33 210 146 402), lower := (rows 35 70 268 137 112 33 64 128 256), losses := [] }

theorem u19945 : Upper (D 7) (R 7) [34,68,264,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19946 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 137 112 34 209 145 401), lower := (rows 35 70 268 137 112 34 64 128 256), losses := [] }

theorem u19946 : Upper (D 7) (R 7) [34,68,264,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19947 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 268 137 112 48 195 131 387), lower := (rows 35 70 268 137 112 48 64 128 256), losses := [] }

theorem u19947 : Upper (D 7) (R 7) [34,68,264,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19947 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19948 : Route 9 := (fun mask => (mask,id))

def c19948 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19948 : Upper (D 7) (R 7) [34,68,264,129,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129,96,128] 13 (by decide) (choices 1) [1,2,16] r19948 c19948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5467
  · exact u5468
  · exact u5469

def b19949 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(0,7),(3,6),(4,0)], upper := (rows 35 70 268 137 146 33 112 240 368), lower := (rows 35 70 268 137 146 33 64 128 256), losses := [] }

theorem u19949 : Upper (D 7) (R 7) [34,68,264,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19950 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 268 137 146 48 97 225 353), lower := (rows 35 70 268 137 146 48 64 128 256), losses := [] }

theorem u19950 : Upper (D 7) (R 7) [34,68,264,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19950 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19951 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 268 137 146 96 113 177 305), lower := (rows 35 70 268 137 146 96 64 128 256), losses := [] }

theorem u19951 : Upper (D 7) (R 7) [34,68,264,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19952 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 3, region := 48, targets := 66 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 70 268 137 176 33 82 210 338), lower := (rows 35 70 268 137 176 33 64 128 256), losses := [] }

theorem u19952 : Upper (D 7) (R 7) [34,68,264,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19953 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 137 176 34 81 209 337), lower := (rows 35 70 268 137 176 34 64 128 256), losses := [] }

theorem u19953 : Upper (D 7) (R 7) [34,68,264,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19954 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 268 137 176 48 67 195 323), lower := (rows 35 70 268 137 176 48 64 128 256), losses := [] }

theorem u19954 : Upper (D 7) (R 7) [34,68,264,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19954 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19955 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 268 137 176 96 83 147 275), lower := (rows 35 70 268 137 176 96 64 128 256), losses := [] }

theorem u19955 : Upper (D 7) (R 7) [34,68,264,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19956 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 70 268 137 208 33 114 178 306), lower := (rows 35 70 268 137 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 65 129 257), good := (rows 498 70 286 478 208 496 64 128 256) }] }

theorem u19956 : Upper (D 7) (R 7) [34,68,264,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19957 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 137 208 34 113 177 305), lower := (rows 35 70 268 137 208 34 64 128 256), losses := [] }

theorem u19957 : Upper (D 7) (R 7) [34,68,264,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19958 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(1,7),(2,6),(3,6)], upper := (rows 35 70 268 137 208 48 99 163 291), lower := (rows 35 70 268 137 208 48 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 48 65 0 257), good := (rows 355 70 270 335 112 48 64 0 256) }] }

theorem u19958 : Upper (D 7) (R 7) [34,68,264,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19958 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19959 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 70 268 138 81 33 240 176 432), lower := (rows 35 70 268 138 81 33 64 128 256), losses := [] }

theorem u19959 : Upper (D 7) (R 7) [34,68,264,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19960 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 268 138 81 48 225 161 417), lower := (rows 35 70 268 138 81 48 64 128 256), losses := [] }

theorem u19960 : Upper (D 7) (R 7) [34,68,264,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19960 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19961 : Route 9 := (fun mask => (mask,id))

def c19961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19961 : Upper (D 7) (R 7) [34,68,264,130,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,65,128] 13 (by decide) (choices 1) [1,16,32] r19961 c19961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5470
  · exact u5471
  · exact u5472

def b19962 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 70 268 138 112 33 209 145 401), lower := (rows 35 70 268 138 112 33 64 128 256), losses := [] }

theorem u19962 : Upper (D 7) (R 7) [34,68,264,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19963 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 268 138 112 48 193 129 385), lower := (rows 35 70 268 138 112 48 64 128 256), losses := [] }

theorem u19963 : Upper (D 7) (R 7) [34,68,264,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19963 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19964 : Route 9 := (fun mask => (mask,id))

def c19964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19964 : Upper (D 7) (R 7) [34,68,264,130,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,96,128] 13 (by decide) (choices 1) [1,16] r19964 c19964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5473
  · exact u5474

def b19965 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 70 268 138 145 33 112 240 368), lower := (rows 35 70 268 138 145 33 64 128 256), losses := [] }

theorem u19965 : Upper (D 7) (R 7) [34,68,264,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19966 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 70 268 138 145 48 97 225 353), lower := (rows 35 70 268 138 145 48 64 128 256), losses := [] }

theorem u19966 : Upper (D 7) (R 7) [34,68,264,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19966 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19967 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 268 138 145 96 113 177 305), lower := (rows 35 70 268 138 145 96 64 128 256), losses := [] }

theorem u19967 : Upper (D 7) (R 7) [34,68,264,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19968 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 70 268 138 176 33 81 209 337), lower := (rows 35 70 268 138 176 33 64 128 256), losses := [] }

theorem u19968 : Upper (D 7) (R 7) [34,68,264,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19969 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 268 138 176 48 65 193 321), lower := (rows 35 70 268 138 176 48 64 128 256), losses := [] }

theorem u19969 : Upper (D 7) (R 7) [34,68,264,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19969 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19970 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 268 138 176 96 81 145 273), lower := (rows 35 70 268 138 176 96 64 128 256), losses := [] }

theorem u19970 : Upper (D 7) (R 7) [34,68,264,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19971 : Route 9 := (fun mask => (mask,id))

def c19971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19971 : Upper (D 7) (R 7) [34,68,264,130,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,130,192,1] 13 (by decide) (choices 1) [1,16,32] r19971 c19971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5475
  · exact u5476
  · exact u5477

def b19972 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 70 268 138 208 48 97 161 289), lower := (rows 35 70 268 138 208 48 64 128 256), losses := [] }

theorem u19972 : Upper (D 7) (R 7) [34,68,264,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19972 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19973 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(4,7)], upper := (rows 35 70 268 152 81 33 226 162 418), lower := (rows 35 70 268 152 81 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 65 129 257), good := (rows 482 70 268 158 478 480 64 128 256) }] }

theorem u19973 : Upper (D 7) (R 7) [34,68,264,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19974 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 152 81 34 225 161 417), lower := (rows 35 70 268 152 81 34 64 128 256), losses := [] }

theorem u19974 : Upper (D 7) (R 7) [34,68,264,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19975 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 80, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,7)], upper := (rows 35 70 268 152 81 160 99 163 291), lower := (rows 35 70 268 152 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 187 0 131 259), good := (rows 419 423 300 188 445 160 0 160 256) }] }

theorem u19975 : Upper (D 7) (R 7) [34,68,264,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19976 : Route 9 := (fun mask => (mask,id))

def c19976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19976 : Upper (D 7) (R 7) [34,68,264,144,96,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,144,96,1] 13 (by decide) (choices 1) [1,2,128] r19976 c19976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5478
  · exact u5479
  · exact u5480

def b19977 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 152 112 34 193 129 385), lower := (rows 35 70 268 152 112 34 64 128 256), losses := [] }

theorem u19977 : Upper (D 7) (R 7) [34,68,264,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19978 : Route 9 := (fun mask => (mask,id))

def c19978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19978 : Upper (D 7) (R 7) [34,68,264,144,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,264,144,96,128] 13 (by decide) (choices 1) [1,2] r19978 c19978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5481
  · exact u5482

def b19979 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,5),(4,7)], upper := (rows 35 70 268 168 81 33 210 146 402), lower := (rows 35 70 268 168 81 33 64 128 256), losses := [] }

theorem u19979 : Upper (D 7) (R 7) [34,68,264,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19979
end Delivery.IrregularNine14.P07
