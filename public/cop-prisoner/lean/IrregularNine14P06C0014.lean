import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0000

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 88 276 34 65 224 352), lower := (rows 7 11 164 88 276 34 65 128 256), losses := [] }

theorem u840 : Upper (D 6) (R 6) [6,9,160,80,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 65, camps := [], pairs := [(3,0),(3,1),(4,1)], upper := (rows 7 11 164 88 276 34 96 193 321), lower := (rows 7 11 164 88 276 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 103 128 256), good := (rows 102 106 228 88 348 98 96 128 256) },{ target := 1, region := (rows 1 0 4 25 17 32 100 129 257), good := (rows 477 409 228 88 348 96 96 128 256) }] }

theorem u841 : Upper (D 6) (R 6) [6,9,160,80,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 88 276 96 65 162 290), lower := (rows 7 11 164 88 276 96 65 128 256), losses := [] }

theorem u842 : Upper (D 6) (R 6) [6,9,160,80,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 88 276 96 66 161 289), lower := (rows 7 11 164 88 276 96 66 128 256), losses := [] }

theorem u843 : Upper (D 6) (R 6) [6,9,160,80,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 164 88 276 96 96 131 259), lower := (rows 7 11 164 88 276 96 96 128 256), losses := [] }

theorem u844 : Upper (D 6) (R 6) [6,9,160,80,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 164 88 304 34 65 196 324), lower := (rows 7 11 164 88 304 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 72 82 35 64 200 328), good := (rows 54 446 164 476 304 54 508 128 256) }] }

theorem u845 : Upper (D 6) (R 6) [6,9,160,80,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 65, camps := [], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 11 164 88 304 34 68 193 321), lower := (rows 7 11 164 88 304 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 36 60 48 32 117 131 259), good := (rows 461 457 252 88 380 508 76 128 256) }] }

theorem u846 : Upper (D 6) (R 6) [6,9,160,80,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 164 88 304 96 65 134 262), lower := (rows 7 11 164 88 304 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 104 82 104 64 131 259), good := (rows 406 446 172 124 312 124 508 128 256) }] }

theorem u847 : Upper (D 6) (R 6) [6,9,160,80,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 5, camps := [], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 11 164 88 304 96 66 133 261), lower := (rows 7 11 164 88 304 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 70 104 82 104 64 131 259), good := (rows 405 445 172 124 312 124 508 128 256) }] }

theorem u848 : Upper (D 6) (R 6) [6,9,160,80,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,2)], upper := (rows 7 11 164 88 304 96 68 131 259), lower := (rows 7 11 164 88 304 96 68 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 18 104 64 131 259), good := (rows 403 443 160 120 304 96 96 128 256) }] }

theorem u849 : Upper (D 6) (R 6) [6,9,160,80,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b850 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 104 81 288 66 148 276), lower := (rows 7 11 164 104 81 288 66 128 256), losses := [] }

theorem u850 : Upper (D 6) (R 6) [6,9,160,96,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b850 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 164 104 81 288 68 146 274), lower := (rows 7 11 164 104 81 288 68 128 256), losses := [] }

theorem u851 : Upper (D 6) (R 6) [6,9,160,96,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b851 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 164 104 81 288 80 134 262), lower := (rows 7 11 164 104 81 288 80 128 256), losses := [] }

theorem u852 : Upper (D 6) (R 6) [6,9,160,96,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b852 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,1),(4,5)], upper := (rows 7 11 164 104 84 288 65 146 274), lower := (rows 7 11 164 104 84 288 65 128 256), losses := [] }

theorem u853 : Upper (D 6) (R 6) [6,9,160,96,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b853 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 7 11 164 104 84 288 66 145 273), lower := (rows 7 11 164 104 84 288 66 128 256), losses := [] }

theorem u854 : Upper (D 6) (R 6) [6,9,160,96,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b854 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 164 104 84 288 80 131 259), lower := (rows 7 11 164 104 84 288 80 128 256), losses := [] }

theorem u855 : Upper (D 6) (R 6) [6,9,160,96,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b855 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 104 274 48 65 196 324), lower := (rows 7 11 164 104 274 48 65 128 256), losses := [] }

theorem u856 : Upper (D 6) (R 6) [6,9,160,96,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b856 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 164 104 274 48 68 193 321), lower := (rows 7 11 164 104 274 48 68 128 256), losses := [] }

theorem u857 : Upper (D 6) (R 6) [6,9,160,96,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b857 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r858 : Route 9 := (fun mask => (mask,id))

def c858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u858 : Upper (D 6) (R 6) [6,9,160,96,260,16,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,260,16,1] 13 (by decide) (choices 1) [2,64] r858 c858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u38
  · exact u39

def r859 : Route 9 := (fun mask => (mask,id))

def c859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u859 : Upper (D 6) (R 6) [6,9,160,96,260,16,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,260,16,2] 13 (by decide) (choices 1) [1,64] r859 c859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u40
  · exact u41

def b860 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 104 336 34 65 148 276), lower := (rows 7 11 164 104 336 34 65 128 256), losses := [] }

theorem u860 : Upper (D 6) (R 6) [6,9,160,96,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 2, region := 72, targets := 1 }], pairs := [(3,0),(4,1),(4,5)], upper := (rows 7 11 164 104 336 34 68 145 273), lower := (rows 7 11 164 104 336 34 68 128 256), losses := [] }

theorem u861 : Upper (D 6) (R 6) [6,9,160,96,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 164 104 336 34 80 133 261), lower := (rows 7 11 164 104 336 34 80 128 256), losses := [] }

theorem u862 : Upper (D 6) (R 6) [6,9,160,96,320,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b862 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 148, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 266 84 96 65 176 304), lower := (rows 7 11 164 266 84 96 65 128 256), losses := [] }

theorem u863 : Upper (D 6) (R 6) [6,9,160,258,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b864 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 266 84 96 80 161 289), lower := (rows 7 11 164 266 84 96 80 128 256), losses := [] }

theorem u864 : Upper (D 6) (R 6) [6,9,160,258,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b864 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b865 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 267, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 266 84 96 96 145 273), lower := (rows 7 11 164 266 84 96 96 128 256), losses := [] }

theorem u865 : Upper (D 6) (R 6) [6,9,160,258,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 132, targets := 3 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,0),(2,1),(4,2)], upper := (rows 7 11 164 280 50 96 65 196 324), lower := (rows 7 11 164 280 50 96 65 128 256), losses := [] }

theorem u866 : Upper (D 6) (R 6) [6,9,160,272,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b867 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 0, region := 112, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 280 50 96 68 193 321), lower := (rows 7 11 164 280 50 96 68 128 256), losses := [] }

theorem u867 : Upper (D 6) (R 6) [6,9,160,272,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b868 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 280 81 96 66 164 292), lower := (rows 7 11 164 280 81 96 66 128 256), losses := [] }

theorem u868 : Upper (D 6) (R 6) [6,9,160,272,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 4 },{ cop := 7, region := 100, targets := 1 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 11 164 280 81 96 68 162 290), lower := (rows 7 11 164 280 81 96 68 128 256), losses := [] }

theorem u869 : Upper (D 6) (R 6) [6,9,160,272,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b870 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 7 11 164 280 81 96 96 134 262), lower := (rows 7 11 164 280 81 96 96 128 256), losses := [] }

theorem u870 : Upper (D 6) (R 6) [6,9,160,272,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 280 82 96 65 164 292), lower := (rows 7 11 164 280 82 96 65 128 256), losses := [] }

theorem u871 : Upper (D 6) (R 6) [6,9,160,272,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 280 82 96 68 161 289), lower := (rows 7 11 164 280 82 96 68 128 256), losses := [] }

theorem u872 : Upper (D 6) (R 6) [6,9,160,272,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 7 11 164 280 82 96 96 133 261), lower := (rows 7 11 164 280 82 96 96 128 256), losses := [] }

theorem u873 : Upper (D 6) (R 6) [6,9,160,272,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b874 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 280 84 33 66 224 352), lower := (rows 7 11 164 280 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 49 32 67 160 288), good := (rows 94 90 444 280 92 508 66 128 256) }] }

theorem u874 : Upper (D 6) (R 6) [6,9,160,272,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b875 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 267, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 280 84 33 96 194 322), lower := (rows 7 11 164 280 84 33 96 128 256), losses := [] }

theorem u875 : Upper (D 6) (R 6) [6,9,160,272,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 11 164 280 84 34 65 224 352), lower := (rows 7 11 164 280 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 88 80 35 64 192 320), good := (rows 38 42 164 280 476 34 508 128 256) }] }

theorem u876 : Upper (D 6) (R 6) [6,9,160,272,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 267, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 280 84 34 96 193 321), lower := (rows 7 11 164 280 84 34 96 128 256), losses := [] }

theorem u877 : Upper (D 6) (R 6) [6,9,160,272,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r878 : Route 9 := (fun mask => (mask,id))

def c878 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u878 : Upper (D 6) (R 6) [6,9,160,272,68,64,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,68,64,1] 13 (by decide) (choices 1) [2,32] r878 c878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u42
  · exact u43

def r879 : Route 9 := (fun mask => (mask,id))

def c879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u879 : Upper (D 6) (R 6) [6,9,160,272,68,64,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,272,68,64,2] 13 (by decide) (choices 1) [1,32] r879 c879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u44
  · exact u45

def b880 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 267, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 164 280 84 96 96 131 259), lower := (rows 7 11 164 280 84 96 96 128 256), losses := [] }

theorem u880 : Upper (D 6) (R 6) [6,9,160,272,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b881 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 280 112 34 65 196 324), lower := (rows 7 11 164 280 112 34 65 128 256), losses := [] }

theorem u881 : Upper (D 6) (R 6) [6,9,160,272,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b882 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 7 11 164 280 112 34 68 193 321), lower := (rows 7 11 164 280 112 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 36 41 52 32 117 131 259), good := (rows 477 457 252 344 124 508 84 128 256) }] }

theorem u882 : Upper (D 6) (R 6) [6,9,160,272,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 296 81 96 66 148 276), lower := (rows 7 11 164 296 81 96 66 128 256), losses := [] }

theorem u883 : Upper (D 6) (R 6) [6,9,160,288,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b884 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 4 },{ cop := 7, region := 100, targets := 1 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 11 164 296 81 96 68 146 274), lower := (rows 7 11 164 296 81 96 68 128 256), losses := [] }

theorem u884 : Upper (D 6) (R 6) [6,9,160,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b885 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 296 81 96 80 134 262), lower := (rows 7 11 164 296 81 96 80 128 256), losses := [] }

theorem u885 : Upper (D 6) (R 6) [6,9,160,288,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b885 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 296 82 48 65 196 324), lower := (rows 7 11 164 296 82 48 65 128 256), losses := [] }

theorem u886 : Upper (D 6) (R 6) [6,9,160,288,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b886 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 7 11 164 296 82 48 68 193 321), lower := (rows 7 11 164 296 82 48 68 128 256), losses := [] }

theorem u887 : Upper (D 6) (R 6) [6,9,160,288,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b887 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b888 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 296 82 96 65 148 276), lower := (rows 7 11 164 296 82 96 65 128 256), losses := [] }

theorem u888 : Upper (D 6) (R 6) [6,9,160,288,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 296 82 96 68 145 273), lower := (rows 7 11 164 296 82 96 68 128 256), losses := [] }

theorem u889 : Upper (D 6) (R 6) [6,9,160,288,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 296 82 96 80 133 261), lower := (rows 7 11 164 296 82 96 80 128 256), losses := [] }

theorem u890 : Upper (D 6) (R 6) [6,9,160,288,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b890 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b891 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,1),(4,5)], upper := (rows 7 11 164 296 84 48 65 194 322), lower := (rows 7 11 164 296 84 48 65 128 256), losses := [] }

theorem u891 : Upper (D 6) (R 6) [6,9,160,288,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b891 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 7 11 164 296 84 48 66 193 321), lower := (rows 7 11 164 296 84 48 66 128 256), losses := [] }

theorem u892 : Upper (D 6) (R 6) [6,9,160,288,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b892 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r893 : Route 9 := (fun mask => (mask,id))

def c893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u893 : Upper (D 6) (R 6) [6,9,160,288,68,64,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,68,64,1] 13 (by decide) (choices 1) [2,16] r893 c893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u46
  · exact u47

def r894 : Route 9 := (fun mask => (mask,id))

def c894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u894 : Upper (D 6) (R 6) [6,9,160,288,68,64,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,288,68,64,2] 13 (by decide) (choices 1) [1,16] r894 c894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u48
  · exact u49

def b895 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 296 84 96 80 131 259), lower := (rows 7 11 164 296 84 96 80 128 256), losses := [] }

theorem u895 : Upper (D 6) (R 6) [6,9,160,288,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b895 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b896 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 328 49 96 66 148 276), lower := (rows 7 11 164 328 49 96 66 128 256), losses := [] }

theorem u896 : Upper (D 6) (R 6) [6,9,160,320,33,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b897 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 164 328 49 96 68 146 274), lower := (rows 7 11 164 328 49 96 68 128 256), losses := [] }

theorem u897 : Upper (D 6) (R 6) [6,9,160,320,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 164 328 49 96 80 134 262), lower := (rows 7 11 164 328 49 96 80 128 256), losses := [] }

theorem u898 : Upper (D 6) (R 6) [6,9,160,320,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b898 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b899 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 328 81 48 66 164 292), lower := (rows 7 11 164 328 81 48 66 128 256), losses := [] }

theorem u899 : Upper (D 6) (R 6) [6,9,160,320,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b899 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P06
