import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 321 7 38 104 152 160 80 161 289), lower := (rows 321 7 38 104 152 160 80 128 256), losses := [] }

theorem u840 : Upper (D 8) (R 8) [320,5,34,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b840 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 104 152 160 96 145 273), lower := (rows 321 7 38 104 152 160 96 128 256), losses := [] }

theorem u841 : Upper (D 8) (R 8) [320,5,34,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 26 176 96 65 160 416), lower := (rows 321 7 44 26 176 96 65 128 256), losses := [] }

theorem u842 : Upper (D 8) (R 8) [320,5,40,18,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 26 176 96 96 129 385), lower := (rows 321 7 44 26 176 96 96 128 256), losses := [] }

theorem u843 : Upper (D 8) (R 8) [320,5,40,18,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 257, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 26 176 96 192 161 289), lower := (rows 321 7 44 26 176 96 192 128 256), losses := [] }

theorem u844 : Upper (D 8) (R 8) [320,5,40,18,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 321 7 164 56 208 33 66 168 296), lower := (rows 321 7 164 56 208 33 66 128 256), losses := [] }

theorem u845 : Upper (D 8) (R 8) [320,5,160,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b845 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 321 7 164 56 208 33 72 162 290), lower := (rows 321 7 164 56 208 33 72 128 256), losses := [] }

theorem u846 : Upper (D 8) (R 8) [320,5,160,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b846 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 164 56 208 33 96 138 266), lower := (rows 321 7 164 56 208 33 96 128 256), losses := [] }

theorem u847 : Upper (D 8) (R 8) [320,5,160,48,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 104 146 160 65 176 304), lower := (rows 321 14 37 104 146 160 65 128 256), losses := [] }

theorem u848 : Upper (D 8) (R 8) [320,12,33,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 321 14 37 104 146 160 80 161 289), lower := (rows 321 14 37 104 146 160 80 128 256), losses := [] }

theorem u849 : Upper (D 8) (R 8) [320,12,33,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b849 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b850 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 74, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 37 104 146 160 96 145 273), lower := (rows 321 14 37 104 146 160 96 128 256), losses := [] }

theorem u850 : Upper (D 8) (R 8) [320,12,33,96,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 321 14 37 152 112 160 65 162 290), lower := (rows 321 14 37 152 112 160 65 128 256), losses := [] }

theorem u851 : Upper (D 8) (R 8) [320,12,33,144,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 321 14 37 152 112 160 66 161 289), lower := (rows 321 14 37 152 112 160 66 128 256), losses := [] }

theorem u852 : Upper (D 8) (R 8) [320,12,33,144,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b852 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 321 14 37 152 112 160 96 131 259), lower := (rows 321 14 37 152 112 160 96 128 256), losses := [] }

theorem u853 : Upper (D 8) (R 8) [320,12,33,144,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 321 14 100 152 49 160 65 162 290), lower := (rows 321 14 100 152 49 160 65 128 256), losses := [] }

theorem u854 : Upper (D 8) (R 8) [320,12,96,144,33,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 321 14 100 152 49 160 66 161 289), lower := (rows 321 14 100 152 49 160 66 128 256), losses := [] }

theorem u855 : Upper (D 8) (R 8) [320,12,96,144,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b855 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 100 152 49 160 96 131 259), lower := (rows 321 14 100 152 49 160 96 128 256), losses := [] }

theorem u856 : Upper (D 8) (R 8) [320,12,96,144,33,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 74 148 160 65 176 304), lower := (rows 321 35 44 74 148 160 65 128 256), losses := [] }

theorem u857 : Upper (D 8) (R 8) [320,33,40,66,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 321 35 44 74 148 160 80 161 289), lower := (rows 321 35 44 74 148 160 80 128 256), losses := [] }

theorem u858 : Upper (D 8) (R 8) [320,33,40,66,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b858 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 74 148 160 96 145 273), lower := (rows 321 35 44 74 148 160 96 128 256), losses := [] }

theorem u859 : Upper (D 8) (R 8) [320,33,40,66,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 208 33 480 416 416), lower := (rows 7 11 52 104 208 33 64 128 256), losses := [] }

theorem u860 : Upper (D 8) (R 8) [6,9,48,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 208 160 353 417 289), lower := (rows 7 11 52 104 208 160 64 128 256), losses := [] }

theorem u861 : Upper (D 8) (R 8) [6,9,48,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 52 104 208 288 225 161 417), lower := (rows 7 11 52 104 208 288 64 128 256), losses := [] }

theorem u862 : Upper (D 8) (R 8) [6,9,48,96,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b862 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 336 33 224 160 416), lower := (rows 7 11 52 104 336 33 64 128 256), losses := [] }

theorem u863 : Upper (D 8) (R 8) [6,9,48,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r864 : Route 9 := (fun mask => (mask,id))

def c864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u864 : Upper (D 8) (R 8) [6,9,48,96,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,320,128] 13 (by decide) (choices 1) [1,32,128] r864 c864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6
  · exact u7
  · exact u8

def b865 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 104 400 33 224 224 480), lower := (rows 7 11 52 104 400 33 64 128 256), losses := [] }

theorem u865 : Upper (D 8) (R 8) [6,9,48,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 52 104 400 96 225 161 417), lower := (rows 7 11 52 104 400 96 64 128 256), losses := [] }

theorem u866 : Upper (D 8) (R 8) [6,9,48,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b867 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 400 160 97 225 353), lower := (rows 7 11 52 104 400 160 64 128 256), losses := [] }

theorem u867 : Upper (D 8) (R 8) [6,9,48,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b868 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 336 33 224 160 416), lower := (rows 7 11 52 200 336 33 64 128 256), losses := [] }

theorem u868 : Upper (D 8) (R 8) [6,9,48,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r869 : Route 9 := (fun mask => (mask,id))

def c869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u869 : Upper (D 8) (R 8) [6,9,48,192,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,128] 13 (by decide) (choices 1) [1,32] r869 c869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9
  · exact u10

def b870 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 296 208 33 224 224 480), lower := (rows 7 11 52 296 208 33 64 128 256), losses := [] }

theorem u870 : Upper (D 8) (R 8) [6,9,48,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 52 296 208 96 225 161 417), lower := (rows 7 11 52 296 208 96 64 128 256), losses := [] }

theorem u871 : Upper (D 8) (R 8) [6,9,48,288,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 328 208 33 224 160 416), lower := (rows 7 11 52 328 208 33 64 128 256), losses := [] }

theorem u872 : Upper (D 8) (R 8) [6,9,48,320,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 328 208 160 97 161 289), lower := (rows 7 11 52 328 208 160 64 128 256), losses := [] }

theorem u873 : Upper (D 8) (R 8) [6,9,48,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b874 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 304 33 224 224 480), lower := (rows 7 11 84 168 304 33 64 128 256), losses := [] }

theorem u874 : Upper (D 8) (R 8) [6,9,80,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r875 : Route 9 := (fun mask => (mask,id))

def c875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u875 : Upper (D 8) (R 8) [6,9,80,160,288,64] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288,64] 13 (by decide) (choices 1) [1,32,128] r875 c875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11
  · exact u12
  · exact u13

def b876 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 84 168 304 160 97 225 353), lower := (rows 7 11 84 168 304 160 64 128 256), losses := [] }

theorem u876 : Upper (D 8) (R 8) [6,9,80,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 400 33 96 224 352), lower := (rows 7 11 84 168 400 33 64 128 256), losses := [] }

theorem u877 : Upper (D 8) (R 8) [6,9,80,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r878 : Route 9 := (fun mask => (mask,id))

def c878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u878 : Upper (D 8) (R 8) [6,9,80,160,384,64] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,384,64] 13 (by decide) (choices 1) [1,32] r878 c878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14
  · exact u15

def b879 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 296 176 33 224 224 480), lower := (rows 7 11 84 296 176 33 64 128 256), losses := [] }

theorem u879 : Upper (D 8) (R 8) [6,9,80,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r880 : Route 9 := (fun mask => (mask,id))

def c880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u880 : Upper (D 8) (R 8) [6,9,80,288,160,64] 13 := by
  apply FastRouting.sound _ _ [6,9,80,288,160,64] 13 (by decide) (choices 1) [1,32,128] r880 c880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16
  · exact u17
  · exact u18

def b881 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 84 296 176 160 97 225 353), lower := (rows 7 11 84 296 176 160 64 128 256), losses := [] }

theorem u881 : Upper (D 8) (R 8) [6,9,80,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b882 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 392 176 33 96 224 352), lower := (rows 7 11 84 392 176 33 64 128 256), losses := [] }

theorem u882 : Upper (D 8) (R 8) [6,9,80,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r883 : Route 9 := (fun mask => (mask,id))

def c883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u883 : Upper (D 8) (R 8) [6,9,80,384,160,64] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384,160,64] 13 (by decide) (choices 1) [1,32] r883 c883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19
  · exact u20

def b884 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 208 33 480 416 416), lower := (rows 7 11 100 56 208 33 64 128 256), losses := [] }

theorem u884 : Upper (D 8) (R 8) [6,9,96,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b885 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 208 160 353 417 289), lower := (rows 7 11 100 56 208 160 64 128 256), losses := [] }

theorem u885 : Upper (D 8) (R 8) [6,9,96,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 100 56 208 288 225 161 417), lower := (rows 7 11 100 56 208 288 64 128 256), losses := [] }

theorem u886 : Upper (D 8) (R 8) [6,9,96,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b886 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 336 33 224 160 416), lower := (rows 7 11 100 56 336 33 64 128 256), losses := [] }

theorem u887 : Upper (D 8) (R 8) [6,9,96,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r888 : Route 9 := (fun mask => (mask,id))

def c888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u888 : Upper (D 8) (R 8) [6,9,96,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,320,128] 13 (by decide) (choices 1) [1,32,128] r888 c888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21
  · exact u22
  · exact u23

def b889 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 56 400 33 224 224 480), lower := (rows 7 11 100 56 400 33 64 128 256), losses := [] }

theorem u889 : Upper (D 8) (R 8) [6,9,96,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 56 400 96 225 161 417), lower := (rows 7 11 100 56 400 96 64 128 256), losses := [] }

theorem u890 : Upper (D 8) (R 8) [6,9,96,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b891 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 400 160 97 225 353), lower := (rows 7 11 100 56 400 160 64 128 256), losses := [] }

theorem u891 : Upper (D 8) (R 8) [6,9,96,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 304 33 224 224 480), lower := (rows 7 11 100 152 304 33 64 128 256), losses := [] }

theorem u892 : Upper (D 8) (R 8) [6,9,96,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 152 304 96 225 161 417), lower := (rows 7 11 100 152 304 96 64 128 256), losses := [] }

theorem u893 : Upper (D 8) (R 8) [6,9,96,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r894 : Route 9 := (fun mask => (mask,id))

def c894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u894 : Upper (D 8) (R 8) [6,9,96,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,128] 13 (by decide) (choices 1) [1,32] r894 c894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24
  · exact u25

def b895 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 336 33 224 160 416), lower := (rows 7 11 100 152 336 33 64 128 256), losses := [] }

theorem u895 : Upper (D 8) (R 8) [6,9,96,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r896 : Route 9 := (fun mask => (mask,id))

def c896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u896 : Upper (D 8) (R 8) [6,9,96,144,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,320,128] 13 (by decide) (choices 1) [1,32] r896 c896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26
  · exact u27

def b897 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 208 33 368 432 304), lower := (rows 7 11 100 168 208 33 64 128 256), losses := [] }

theorem u897 : Upper (D 8) (R 8) [6,9,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 11 100 168 208 48 353 417 289), lower := (rows 7 11 100 168 208 48 64 128 256), losses := [] }

theorem u898 : Upper (D 8) (R 8) [6,9,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b898 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b899 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 11 100 168 208 288 113 177 305), lower := (rows 7 11 100 168 208 288 64 128 256), losses := [] }

theorem u899 : Upper (D 8) (R 8) [6,9,96,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b899 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P08
