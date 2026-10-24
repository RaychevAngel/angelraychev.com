import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0103

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r21000 : Route 9 := (fun mask => (mask,id))

def c21000 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21000 : Upper (D 6) (R 6) [34,72,96,144,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,257,4] 13 (by decide) (choices 1) [1,2,4] r21000 c21000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6216
  · exact u6217
  · exact u6218

def b21001 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 74 100 152 274 33 69 133 261), lower := (rows 35 74 100 152 274 33 64 128 256), losses := [] }

theorem u21001 : Upper (D 6) (R 6) [34,72,96,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21002 : Route 9 := (fun mask => (mask,id))

def c21002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21002 : Upper (D 6) (R 6) [34,72,96,144,258,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,258,4] 13 (by decide) (choices 1) [1,4] r21002 c21002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6219
  · exact u6220

def r21003 : Route 9 := (fun mask => (mask,id))

def c21003 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21003 : Upper (D 6) (R 6) [34,72,96,144,260,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,260,1] 13 (by decide) (choices 1) [1,2,4] r21003 c21003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6221
  · exact u6222
  · exact u6223

def b21004 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 152 276 34 69 133 261), lower := (rows 35 74 100 152 276 34 64 128 256), losses := [] }

theorem u21004 : Upper (D 6) (R 6) [34,72,96,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21005 : Route 9 := (fun mask => (mask,id))

def c21005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21005 : Upper (D 6) (R 6) [34,72,96,144,260,4] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,260,4] 13 (by decide) (choices 1) [1,2] r21005 c21005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6224
  · exact u6225

def b21006 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 392 21 33 86 150 278), lower := (rows 35 74 100 392 21 33 64 128 256), losses := [] }

theorem u21006 : Upper (D 6) (R 6) [34,72,96,384,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21007 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 100 392 21 34 85 149 277), lower := (rows 35 74 100 392 21 34 64 128 256), losses := [] }

theorem u21007 : Upper (D 6) (R 6) [34,72,96,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21008 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 100 392 21 36 83 147 275), lower := (rows 35 74 100 392 21 36 64 128 256), losses := [] }

theorem u21008 : Upper (D 6) (R 6) [34,72,96,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21009 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 100 392 21 48 71 135 263), lower := (rows 35 74 100 392 21 48 64 128 256), losses := [] }

theorem u21009 : Upper (D 6) (R 6) [34,72,96,384,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21009 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21010 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 425, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 74 100 392 22 33 85 149 277), lower := (rows 35 74 100 392 22 33 64 128 256), losses := [] }

theorem u21010 : Upper (D 6) (R 6) [34,72,96,384,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21011 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 52, targets := 1 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 35 74 100 392 22 36 81 145 273), lower := (rows 35 74 100 392 22 36 64 128 256), losses := [] }

theorem u21011 : Upper (D 6) (R 6) [34,72,96,384,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21012 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 100 392 22 48 69 133 261), lower := (rows 35 74 100 392 22 48 64 128 256), losses := [] }

theorem u21012 : Upper (D 6) (R 6) [34,72,96,384,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21012 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21013 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 14 52 33 336 464 336), lower := (rows 35 74 133 14 52 33 64 128 256), losses := [] }

theorem u21013 : Upper (D 6) (R 6) [34,72,129,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21014 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 14 52 48 321 449 321), lower := (rows 35 74 133 14 52 48 64 128 256), losses := [] }

theorem u21014 : Upper (D 6) (R 6) [34,72,129,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21014 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21015 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 14 52 96 337 401 273), lower := (rows 35 74 133 14 52 96 64 128 256), losses := [] }

theorem u21015 : Upper (D 6) (R 6) [34,72,129,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21016 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 133 14 52 288 81 209 337), lower := (rows 35 74 133 14 52 288 64 128 256), losses := [] }

theorem u21016 : Upper (D 6) (R 6) [34,72,129,6,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21016 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21017 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 133 14 112 33 340 404 276), lower := (rows 35 74 133 14 112 33 64 128 256), losses := [] }

theorem u21017 : Upper (D 6) (R 6) [34,72,129,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21018 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 133 14 112 36 337 401 273), lower := (rows 35 74 133 14 112 36 64 128 256), losses := [] }

theorem u21018 : Upper (D 6) (R 6) [34,72,129,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21019 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 14 112 48 325 389 261), lower := (rows 35 74 133 14 112 48 64 128 256), losses := [] }

theorem u21019 : Upper (D 6) (R 6) [34,72,129,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21019 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21020 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 133 14 112 288 85 149 277), lower := (rows 35 74 133 14 112 288 64 128 256), losses := [] }

theorem u21020 : Upper (D 6) (R 6) [34,72,129,6,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21020 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21021 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 133 14 273 36 112 240 368), lower := (rows 35 74 133 14 273 36 64 128 256), losses := [] }

theorem u21021 : Upper (D 6) (R 6) [34,72,129,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21022 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 133 14 273 48 100 228 356), lower := (rows 35 74 133 14 273 48 64 128 256), losses := [] }

theorem u21022 : Upper (D 6) (R 6) [34,72,129,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21022 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21023 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 14 273 96 116 180 308), lower := (rows 35 74 133 14 273 96 64 128 256), losses := [] }

theorem u21023 : Upper (D 6) (R 6) [34,72,129,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21024 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 133 14 276 33 112 240 368), lower := (rows 35 74 133 14 276 33 64 128 256), losses := [] }

theorem u21024 : Upper (D 6) (R 6) [34,72,129,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21025 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 133 14 276 48 97 225 353), lower := (rows 35 74 133 14 276 48 64 128 256), losses := [] }

theorem u21025 : Upper (D 6) (R 6) [34,72,129,6,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21025 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21026 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 14 276 96 113 177 305), lower := (rows 35 74 133 14 276 96 64 128 256), losses := [] }

theorem u21026 : Upper (D 6) (R 6) [34,72,129,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21027 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 133 14 304 33 84 212 340), lower := (rows 35 74 133 14 304 33 64 128 256), losses := [] }

theorem u21027 : Upper (D 6) (R 6) [34,72,129,6,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21028 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 133 14 304 36 81 209 337), lower := (rows 35 74 133 14 304 36 64 128 256), losses := [] }

theorem u21028 : Upper (D 6) (R 6) [34,72,129,6,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21029 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 74 133 14 304 48 69 197 325), lower := (rows 35 74 133 14 304 48 64 128 256), losses := [] }

theorem u21029 : Upper (D 6) (R 6) [34,72,129,6,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21029 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21030 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 14 304 96 85 149 277), lower := (rows 35 74 133 14 304 96 64 128 256), losses := [] }

theorem u21030 : Upper (D 6) (R 6) [34,72,129,6,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21031 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 133 14 336 33 116 180 308), lower := (rows 35 74 133 14 336 33 64 128 256), losses := [] }

theorem u21031 : Upper (D 6) (R 6) [34,72,129,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21032 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 133 14 336 36 113 177 305), lower := (rows 35 74 133 14 336 36 64 128 256), losses := [] }

theorem u21032 : Upper (D 6) (R 6) [34,72,129,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21033 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 133 14 336 48 101 165 293), lower := (rows 35 74 133 14 336 48 64 128 256), losses := [] }

theorem u21033 : Upper (D 6) (R 6) [34,72,129,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21033 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21034 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 0, region := 452, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 74 133 25 22 36 352 480 352), lower := (rows 35 74 133 25 22 36 64 128 256), losses := [] }

theorem u21034 : Upper (D 6) (R 6) [34,72,129,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21035 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 25 22 96 356 420 292), lower := (rows 35 74 133 25 22 96 64 128 256), losses := [] }

theorem u21035 : Upper (D 6) (R 6) [34,72,129,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21036 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1)], upper := (rows 35 74 133 25 22 288 100 228 356), lower := (rows 35 74 133 25 22 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 316 84 148 276), good := (rows 34 106 484 506 502 288 64 128 288) }] }

theorem u21036 : Upper (D 6) (R 6) [34,72,129,17,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21036 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21037 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 25 52 34 324 452 324), lower := (rows 35 74 133 25 52 34 64 128 256), losses := [] }

theorem u21037 : Upper (D 6) (R 6) [34,72,129,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21038 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 74 133 25 52 36 322 450 322), lower := (rows 35 74 133 25 52 36 64 128 256), losses := [] }

theorem u21038 : Upper (D 6) (R 6) [34,72,129,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21039 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 25 52 96 326 390 262), lower := (rows 35 74 133 25 52 96 64 128 256), losses := [] }

theorem u21039 : Upper (D 6) (R 6) [34,72,129,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21040 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 133 25 52 288 70 198 326), lower := (rows 35 74 133 25 52 288 64 128 256), losses := [] }

theorem u21040 : Upper (D 6) (R 6) [34,72,129,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21040 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21041 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 25 84 34 356 420 292), lower := (rows 35 74 133 25 84 34 64 128 256), losses := [] }

theorem u21041 : Upper (D 6) (R 6) [34,72,129,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21042 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 35 74 133 25 84 36 354 418 290), lower := (rows 35 74 133 25 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 52 73 137 265), good := (rows 482 458 500 506 116 52 64 128 256) }] }

theorem u21042 : Upper (D 6) (R 6) [34,72,129,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21043 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 25 84 288 102 166 294), lower := (rows 35 74 133 25 84 288 64 128 256), losses := [] }

theorem u21043 : Upper (D 6) (R 6) [34,72,129,17,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21043 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21044 : Route 9 := (fun mask => (mask,id))

def c21044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21044 : Upper (D 6) (R 6) [34,72,129,17,258,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,258,4] 13 (by decide) (choices 1) [4,32] r21044 c21044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6226
  · exact u6227

def b21045 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 25 274 96 100 164 292), lower := (rows 35 74 133 25 274 96 64 128 256), losses := [] }

theorem u21045 : Upper (D 6) (R 6) [34,72,129,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21046 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 25 276 34 100 228 356), lower := (rows 35 74 133 25 276 34 64 128 256), losses := [] }

theorem u21046 : Upper (D 6) (R 6) [34,72,129,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21047 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(1,2),(4,0)], upper := (rows 35 74 133 25 276 36 98 226 354), lower := (rows 35 74 133 25 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 52 73 137 265), good := (rows 482 458 500 506 308 52 64 128 256) },{ target := 2, region := (rows 1 10 0 8 16 32 65 129 257), good := (rows 483 74 449 475 272 32 64 128 256) }] }

theorem u21047 : Upper (D 6) (R 6) [34,72,129,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21048 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 25 276 96 102 166 294), lower := (rows 35 74 133 25 276 96 64 128 256), losses := [] }

theorem u21048 : Upper (D 6) (R 6) [34,72,129,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21049 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 25 304 34 68 196 324), lower := (rows 35 74 133 25 304 34 64 128 256), losses := [] }

theorem u21049 : Upper (D 6) (R 6) [34,72,129,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21050 : Route 9 := (fun mask => (mask,id))

def c21050 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21050 : Upper (D 6) (R 6) [34,72,129,17,288,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,288,4] 13 (by decide) (choices 1) [2,4] r21050 c21050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6228
  · exact u6229

def b21051 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 25 304 96 70 134 262), lower := (rows 35 74 133 25 304 96 64 128 256), losses := [] }

theorem u21051 : Upper (D 6) (R 6) [34,72,129,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21052 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 25 336 34 100 164 292), lower := (rows 35 74 133 25 336 34 64 128 256), losses := [] }

theorem u21052 : Upper (D 6) (R 6) [34,72,129,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21053 : Route 9 := (fun mask => (mask,id))

def c21053 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21053 : Upper (D 6) (R 6) [34,72,129,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,320,4] 13 (by decide) (choices 1) [2,4,32] r21053 c21053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6230
  · exact u6231
  · exact u6232

def r21054 : Route 9 := (fun mask => (mask,id))

def c21054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21054 : Upper (D 6) (R 6) [34,72,129,18,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,129,18,257,4] 13 (by decide) (choices 1) [4,32] r21054 c21054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6233
  · exact u6234

def b21055 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 26 273 96 100 164 292), lower := (rows 35 74 133 26 273 96 64 128 256), losses := [] }

theorem u21055 : Upper (D 6) (R 6) [34,72,129,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21056 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 133 26 276 33 100 228 356), lower := (rows 35 74 133 26 276 33 64 128 256), losses := [] }

theorem u21056 : Upper (D 6) (R 6) [34,72,129,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21057 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 133 26 276 36 97 225 353), lower := (rows 35 74 133 26 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 35 11 165 59 308 36 0 128 256) }] }

theorem u21057 : Upper (D 6) (R 6) [34,72,129,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21058 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 133 26 276 96 101 165 293), lower := (rows 35 74 133 26 276 96 64 128 256), losses := [] }

theorem u21058 : Upper (D 6) (R 6) [34,72,129,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21059 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 133 28 273 34 100 228 356), lower := (rows 35 74 133 28 273 34 64 128 256), losses := [] }

theorem u21059 : Upper (D 6) (R 6) [34,72,129,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21059
end Delivery.IrregularNine14.P06
