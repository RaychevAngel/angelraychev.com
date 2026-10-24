import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0003

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 296 273 160 112 240 368), lower := (rows 35 70 140 296 273 160 64 128 256), losses := [] }

theorem u840 : Upper (D 10) (R 10) [34,68,136,288,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b840 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 296 336 33 240 176 432), lower := (rows 35 70 140 296 336 33 64 128 256), losses := [] }

theorem u841 : Upper (D 10) (R 10) [34,68,136,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b841 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 140 296 336 48 225 161 417), lower := (rows 35 70 140 296 336 48 64 128 256), losses := [] }

theorem u842 : Upper (D 10) (R 10) [34,68,136,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b842 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 140 296 336 160 113 177 305), lower := (rows 35 70 140 296 336 160 64 128 256), losses := [] }

theorem u843 : Upper (D 10) (R 10) [34,68,136,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b843 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 296 400 33 112 240 368), lower := (rows 35 70 140 296 400 33 64 128 256), losses := [] }

theorem u844 : Upper (D 10) (R 10) [34,68,136,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b844 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 140 296 400 48 97 225 353), lower := (rows 35 70 140 296 400 48 64 128 256), losses := [] }

theorem u845 : Upper (D 10) (R 10) [34,68,136,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b845 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 296 400 96 113 177 305), lower := (rows 35 70 140 296 400 96 64 128 256), losses := [] }

theorem u846 : Upper (D 10) (R 10) [34,68,136,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b846 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 39, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 56 208 33 328 392 264), lower := (rows 35 70 164 56 208 33 64 128 256), losses := [] }

theorem u847 : Upper (D 10) (R 10) [34,68,160,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b847 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 56 208 40 321 385 257), lower := (rows 35 70 164 56 208 40 64 128 256), losses := [] }

theorem u848 : Upper (D 10) (R 10) [34,68,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b848 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r849 : Route 9 := (fun mask => (mask,id))

def c849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u849 : Upper (D 10) (R 10) [34,68,160,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,192,256] 13 (by decide) (choices 1) [1,8,256] r849 c849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u186
  · exact u187
  · exact u188

def b850 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 336 33 456 392 392), lower := (rows 35 70 164 56 336 33 64 128 256), losses := [] }

theorem u850 : Upper (D 10) (R 10) [34,68,160,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b850 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 56 336 40 449 385 385), lower := (rows 35 70 164 56 336 40 64 128 256), losses := [] }

theorem u851 : Upper (D 10) (R 10) [34,68,160,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b851 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 56 336 160 329 393 265), lower := (rows 35 70 164 56 336 160 64 128 256), losses := [] }

theorem u852 : Upper (D 10) (R 10) [34,68,160,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b852 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 56 336 288 201 137 393), lower := (rows 35 70 164 56 336 288 64 128 256), losses := [] }

theorem u853 : Upper (D 10) (R 10) [34,68,160,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b853 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 56 400 33 328 456 328), lower := (rows 35 70 164 56 400 33 64 128 256), losses := [] }

theorem u854 : Upper (D 10) (R 10) [34,68,160,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b854 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 56 400 40 321 449 321), lower := (rows 35 70 164 56 400 40 64 128 256), losses := [] }

theorem u855 : Upper (D 10) (R 10) [34,68,160,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b855 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 56 400 96 329 393 265), lower := (rows 35 70 164 56 400 96 64 128 256), losses := [] }

theorem u856 : Upper (D 10) (R 10) [34,68,160,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b856 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 56 400 288 73 201 329), lower := (rows 35 70 164 56 400 288 64 128 256), losses := [] }

theorem u857 : Upper (D 10) (R 10) [34,68,160,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b857 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 88 273 40 480 416 416), lower := (rows 35 70 164 88 273 40 64 128 256), losses := [] }

theorem u858 : Upper (D 10) (R 10) [34,68,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b858 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 88 273 160 360 424 296), lower := (rows 35 70 164 88 273 160 64 128 256), losses := [] }

theorem u859 : Upper (D 10) (R 10) [34,68,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b859 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r860 : Route 9 := (fun mask => (mask,id))

def c860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u860 : Upper (D 10) (R 10) [34,68,160,80,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257,256] 13 (by decide) (choices 1) [8,32,128] r860 c860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u189
  · exact u190
  · exact u191

def b861 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 304 33 456 392 392), lower := (rows 35 70 164 88 304 33 64 128 256), losses := [] }

theorem u861 : Upper (D 10) (R 10) [34,68,160,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b861 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 88 304 40 449 385 385), lower := (rows 35 70 164 88 304 40 64 128 256), losses := [] }

theorem u862 : Upper (D 10) (R 10) [34,68,160,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b862 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 88 304 160 329 393 265), lower := (rows 35 70 164 88 304 160 64 128 256), losses := [] }

theorem u863 : Upper (D 10) (R 10) [34,68,160,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b863 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b864 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 88 304 288 201 137 393), lower := (rows 35 70 164 88 304 288 64 128 256), losses := [] }

theorem u864 : Upper (D 10) (R 10) [34,68,160,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b864 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b865 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 400 33 360 424 296), lower := (rows 35 70 164 88 400 33 64 128 256), losses := [] }

theorem u865 : Upper (D 10) (R 10) [34,68,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b865 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 88 400 40 353 417 289), lower := (rows 35 70 164 88 400 40 64 128 256), losses := [] }

theorem u866 : Upper (D 10) (R 10) [34,68,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b866 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r867 : Route 9 := (fun mask => (mask,id))

def c867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u867 : Upper (D 10) (R 10) [34,68,160,80,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,384,256] 13 (by decide) (choices 1) [1,8,32] r867 c867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u192
  · exact u193
  · exact u194

def b868 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 145 40 336 400 272), lower := (rows 35 70 164 104 145 40 64 128 256), losses := [] }

theorem u868 : Upper (D 10) (R 10) [34,68,160,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b868 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 145 48 328 392 264), lower := (rows 35 70 164 104 145 48 64 128 256), losses := [] }

theorem u869 : Upper (D 10) (R 10) [34,68,160,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b869 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r870 : Route 9 := (fun mask => (mask,id))

def c870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u870 : Upper (D 10) (R 10) [34,68,160,96,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,129,256] 13 (by decide) (choices 1) [8,16,256] r870 c870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u195
  · exact u196
  · exact u197

def b871 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 152 33 336 400 272), lower := (rows 35 70 164 104 152 33 64 128 256), losses := [] }

theorem u871 : Upper (D 10) (R 10) [34,68,160,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b871 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 152 48 321 385 257), lower := (rows 35 70 164 104 152 48 64 128 256), losses := [] }

theorem u872 : Upper (D 10) (R 10) [34,68,160,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b872 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r873 : Route 9 := (fun mask => (mask,id))

def c873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u873 : Upper (D 10) (R 10) [34,68,160,96,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,136,256] 13 (by decide) (choices 1) [1,16,256] r873 c873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u198
  · exact u199
  · exact u200

def b874 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 273 40 464 400 400), lower := (rows 35 70 164 104 273 40 64 128 256), losses := [] }

theorem u874 : Upper (D 10) (R 10) [34,68,160,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b874 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b875 : PairBound 9 := { available := 392, camps := [{ cop := 3, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 104 273 48 456 392 392), lower := (rows 35 70 164 104 273 48 64 128 256), losses := [] }

theorem u875 : Upper (D 10) (R 10) [34,68,160,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b875 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 104 273 160 344 408 280), lower := (rows 35 70 164 104 273 160 64 128 256), losses := [] }

theorem u876 : Upper (D 10) (R 10) [34,68,160,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b876 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r877 : Route 9 := (fun mask => (mask,id))

def c877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u877 : Upper (D 10) (R 10) [34,68,160,96,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,257,256] 13 (by decide) (choices 1) [8,16,128] r877 c877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u201
  · exact u202
  · exact u203

def b878 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 280 33 464 400 400), lower := (rows 35 70 164 104 280 33 64 128 256), losses := [] }

theorem u878 : Upper (D 10) (R 10) [34,68,160,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b878 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b879 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 104 280 48 449 385 385), lower := (rows 35 70 164 104 280 48 64 128 256), losses := [] }

theorem u879 : Upper (D 10) (R 10) [34,68,160,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b879 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b880 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 104 280 160 337 401 273), lower := (rows 35 70 164 104 280 160 64 128 256), losses := [] }

theorem u880 : Upper (D 10) (R 10) [34,68,160,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b880 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r881 : Route 9 := (fun mask => (mask,id))

def c881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u881 : Upper (D 10) (R 10) [34,68,160,96,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,264,256] 13 (by decide) (choices 1) [1,16,128] r881 c881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u204
  · exact u205
  · exact u206

def b882 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 400 33 344 408 280), lower := (rows 35 70 164 104 400 33 64 128 256), losses := [] }

theorem u882 : Upper (D 10) (R 10) [34,68,160,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b882 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 400 40 337 401 273), lower := (rows 35 70 164 104 400 40 64 128 256), losses := [] }

theorem u883 : Upper (D 10) (R 10) [34,68,160,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b883 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b884 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 400 48 329 393 265), lower := (rows 35 70 164 104 400 48 64 128 256), losses := [] }

theorem u884 : Upper (D 10) (R 10) [34,68,160,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b884 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r885 : Route 9 := (fun mask => (mask,id))

def c885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u885 : Upper (D 10) (R 10) [34,68,160,96,384,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,384,256] 13 (by decide) (choices 1) [1,8,16] r885 c885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u207
  · exact u208
  · exact u209

def b886 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 137 280 48 352 480 352), lower := (rows 35 70 164 137 280 48 64 128 256), losses := [] }

theorem u886 : Upper (D 10) (R 10) [34,68,160,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b886 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 137 280 96 368 432 304), lower := (rows 35 70 164 137 280 96 64 128 256), losses := [] }

theorem u887 : Upper (D 10) (R 10) [34,68,160,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b887 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r888 : Route 9 := (fun mask => (mask,id))

def c888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u888 : Upper (D 10) (R 10) [34,68,160,129,264,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,264,256] 13 (by decide) (choices 1) [16,32] r888 c888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u210
  · exact u211

def b889 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 137 304 40 336 464 336), lower := (rows 35 70 164 137 304 40 64 128 256), losses := [] }

theorem u889 : Upper (D 10) (R 10) [34,68,160,129,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b889 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 328, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 164 137 304 48 328 456 328), lower := (rows 35 70 164 137 304 48 64 128 256), losses := [] }

theorem u890 : Upper (D 10) (R 10) [34,68,160,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b890 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b891 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 137 304 96 344 408 280), lower := (rows 35 70 164 137 304 96 64 128 256), losses := [] }

theorem u891 : Upper (D 10) (R 10) [34,68,160,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b891 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 137 304 288 88 216 344), lower := (rows 35 70 164 137 304 288 64 128 256), losses := [] }

theorem u892 : Upper (D 10) (R 10) [34,68,160,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b892 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 137 336 40 368 432 304), lower := (rows 35 70 164 137 336 40 64 128 256), losses := [] }

theorem u893 : Upper (D 10) (R 10) [34,68,160,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b893 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b894 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 137 336 48 360 424 296), lower := (rows 35 70 164 137 336 48 64 128 256), losses := [] }

theorem u894 : Upper (D 10) (R 10) [34,68,160,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b894 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r895 : Route 9 := (fun mask => (mask,id))

def c895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u895 : Upper (D 10) (R 10) [34,68,160,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,320,256] 13 (by decide) (choices 1) [8,16,32] r895 c895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u212
  · exact u213
  · exact u214

def b896 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 152 273 40 352 480 352), lower := (rows 35 70 164 152 273 40 64 128 256), losses := [] }

theorem u896 : Upper (D 10) (R 10) [34,68,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b896 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b897 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 164 152 273 96 360 424 296), lower := (rows 35 70 164 152 273 96 64 128 256), losses := [] }

theorem u897 : Upper (D 10) (R 10) [34,68,160,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b897 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r898 : Route 9 := (fun mask => (mask,id))

def c898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u898 : Upper (D 10) (R 10) [34,68,160,144,257,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,257,256] 13 (by decide) (choices 1) [8,32] r898 c898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u215
  · exact u216

def b899 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 152 304 33 328 456 328), lower := (rows 35 70 164 152 304 33 64 128 256), losses := [] }

theorem u899 : Upper (D 10) (R 10) [34,68,160,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b899 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P10
