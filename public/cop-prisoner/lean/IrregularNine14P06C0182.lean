import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0024
import IrregularNine14P06C0025

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10920 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 28 273 33 74 202 330), lower := (rows 7 98 164 28 273 33 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 49 72 136 264), good := (rows 35 98 160 506 305 33 64 128 256) }] }

theorem u10920 : Upper (D 6) (R 6) [6,96,160,20,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10920
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10921 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 28 273 34 73 201 329), lower := (rows 7 98 164 28 273 34 64 128 256), losses := [] }

theorem u10921 : Upper (D 6) (R 6) [6,96,160,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10921
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10922 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 28 273 40 67 195 323), lower := (rows 7 98 164 28 273 40 64 128 256), losses := [] }

theorem u10922 : Upper (D 6) (R 6) [6,96,160,20,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10922
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10923 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 164 28 273 96 75 139 267), lower := (rows 7 98 164 28 273 96 64 128 256), losses := [] }

theorem u10923 : Upper (D 6) (R 6) [6,96,160,20,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10923
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10924 : Route 9 := (fun mask => (mask,id))

def c10924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10924 : Upper (D 6) (R 6) [6,96,160,20,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,20,258,1] 13 (by decide) (choices 1) [1,8] r10924 c10924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1498
  · exact u1499

def b10925 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 28 274 40 65 193 321), lower := (rows 7 98 164 28 274 40 64 128 256), losses := [] }

theorem u10925 : Upper (D 6) (R 6) [6,96,160,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10925
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10926 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 164 28 274 96 73 137 265), lower := (rows 7 98 164 28 274 96 64 128 256), losses := [] }

theorem u10926 : Upper (D 6) (R 6) [6,96,160,20,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10926
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10927 : Route 9 := (fun mask => (mask,id))

def c10927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10927 : Upper (D 6) (R 6) [6,96,160,20,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,20,320,1] 13 (by decide) (choices 1) [1,2,8] r10927 c10927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1500
  · exact u1501
  · exact u1502

def b10928 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 28 336 34 73 137 265), lower := (rows 7 98 164 28 336 34 64 128 256), losses := [] }

theorem u10928 : Upper (D 6) (R 6) [6,96,160,20,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10928
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10929 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 28 336 40 67 131 259), lower := (rows 7 98 164 28 336 40 64 128 256), losses := [] }

theorem u10929 : Upper (D 6) (R 6) [6,96,160,20,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10929
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10930 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 73 273 34 92 156 284), lower := (rows 7 98 164 73 273 34 64 128 256), losses := [] }

theorem u10930 : Upper (D 6) (R 6) [6,96,160,65,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10930
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10931 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 73 273 36 90 154 282), lower := (rows 7 98 164 73 273 36 64 128 256), losses := [] }

theorem u10931 : Upper (D 6) (R 6) [6,96,160,65,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10931
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10932 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 73 273 40 86 150 278), lower := (rows 7 98 164 73 273 40 64 128 256), losses := [] }

theorem u10932 : Upper (D 6) (R 6) [6,96,160,65,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10932
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10933 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 73 273 48 78 142 270), lower := (rows 7 98 164 73 273 48 64 128 256), losses := [] }

theorem u10933 : Upper (D 6) (R 6) [6,96,160,65,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10933
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10934 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 73 274 33 92 156 284), lower := (rows 7 98 164 73 274 33 64 128 256), losses := [] }

theorem u10934 : Upper (D 6) (R 6) [6,96,160,65,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10934
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10935 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 73 274 36 89 153 281), lower := (rows 7 98 164 73 274 36 64 128 256), losses := [] }

theorem u10935 : Upper (D 6) (R 6) [6,96,160,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10935
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10936 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 73 274 40 85 149 277), lower := (rows 7 98 164 73 274 40 64 128 256), losses := [] }

theorem u10936 : Upper (D 6) (R 6) [6,96,160,65,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10936
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10937 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 73 274 48 77 141 269), lower := (rows 7 98 164 73 274 48 64 128 256), losses := [] }

theorem u10937 : Upper (D 6) (R 6) [6,96,160,65,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10937
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10938 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 73 276 33 90 154 282), lower := (rows 7 98 164 73 276 33 64 128 256), losses := [] }

theorem u10938 : Upper (D 6) (R 6) [6,96,160,65,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10938
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10939 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 73 276 34 89 153 281), lower := (rows 7 98 164 73 276 34 64 128 256), losses := [] }

theorem u10939 : Upper (D 6) (R 6) [6,96,160,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10939
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10940 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 73 276 40 83 147 275), lower := (rows 7 98 164 73 276 40 64 128 256), losses := [] }

theorem u10940 : Upper (D 6) (R 6) [6,96,160,65,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10940
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10941 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 73 276 48 75 139 267), lower := (rows 7 98 164 73 276 48 64 128 256), losses := [] }

theorem u10941 : Upper (D 6) (R 6) [6,96,160,65,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10941
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10942 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 73 280 33 86 150 278), lower := (rows 7 98 164 73 280 33 64 128 256), losses := [] }

theorem u10942 : Upper (D 6) (R 6) [6,96,160,65,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10942
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10943 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 73 280 34 85 149 277), lower := (rows 7 98 164 73 280 34 64 128 256), losses := [] }

theorem u10943 : Upper (D 6) (R 6) [6,96,160,65,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10943
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10944 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 73 280 36 83 147 275), lower := (rows 7 98 164 73 280 36 64 128 256), losses := [] }

theorem u10944 : Upper (D 6) (R 6) [6,96,160,65,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10944
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10945 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 73 280 48 71 135 263), lower := (rows 7 98 164 73 280 48 64 128 256), losses := [] }

theorem u10945 : Upper (D 6) (R 6) [6,96,160,65,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10945
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10946 : Route 9 := (fun mask => (mask,id))

def c10946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10946 : Upper (D 6) (R 6) [6,96,160,68,257,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,68,257,1] 13 (by decide) (choices 1) [2,8,16] r10946 c10946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1503
  · exact u1504
  · exact u1505

def b10947 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 76 273 34 89 153 281), lower := (rows 7 98 164 76 273 34 64 128 256), losses := [] }

theorem u10947 : Upper (D 6) (R 6) [6,96,160,68,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10947
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10948 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 76 273 40 83 147 275), lower := (rows 7 98 164 76 273 40 64 128 256), losses := [] }

theorem u10948 : Upper (D 6) (R 6) [6,96,160,68,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10948
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10949 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 76 273 48 75 139 267), lower := (rows 7 98 164 76 273 48 64 128 256), losses := [] }

theorem u10949 : Upper (D 6) (R 6) [6,96,160,68,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10949
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10950 : Route 9 := (fun mask => (mask,id))

def c10950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10950 : Upper (D 6) (R 6) [6,96,160,68,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,68,258,1] 13 (by decide) (choices 1) [1,8,16] r10950 c10950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1506
  · exact u1507
  · exact u1508

def b10951 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 76 274 40 81 145 273), lower := (rows 7 98 164 76 274 40 64 128 256), losses := [] }

theorem u10951 : Upper (D 6) (R 6) [6,96,160,68,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10951
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10952 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 76 274 48 73 137 265), lower := (rows 7 98 164 76 274 48 64 128 256), losses := [] }

theorem u10952 : Upper (D 6) (R 6) [6,96,160,68,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10952
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10953 : Route 9 := (fun mask => (mask,id))

def c10953 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10953 : Upper (D 6) (R 6) [6,96,160,68,264,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,68,264,1] 13 (by decide) (choices 1) [1,2,16] r10953 c10953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1509
  · exact u1510
  · exact u1511

def b10954 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 76 280 34 81 145 273), lower := (rows 7 98 164 76 280 34 64 128 256), losses := [] }

theorem u10954 : Upper (D 6) (R 6) [6,96,160,68,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10954
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10955 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 76 280 48 67 131 259), lower := (rows 7 98 164 76 280 48 64 128 256), losses := [] }

theorem u10955 : Upper (D 6) (R 6) [6,96,160,68,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10955
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10956 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 88 273 33 78 142 270), lower := (rows 7 98 164 88 273 33 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 49 64 128 256), good := (rows 35 98 160 122 305 33 64 128 256) }] }

theorem u10956 : Upper (D 6) (R 6) [6,96,160,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10956
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10957 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 88 273 34 77 141 269), lower := (rows 7 98 164 88 273 34 64 128 256), losses := [] }

theorem u10957 : Upper (D 6) (R 6) [6,96,160,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10957
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10958 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 88 273 36 75 139 267), lower := (rows 7 98 164 88 273 36 64 128 256), losses := [] }

theorem u10958 : Upper (D 6) (R 6) [6,96,160,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10958
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10959 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 88 273 40 71 135 263), lower := (rows 7 98 164 88 273 40 64 128 256), losses := [] }

theorem u10959 : Upper (D 6) (R 6) [6,96,160,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10959
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10960 : Route 9 := (fun mask => (mask,id))

def c10960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10960 : Upper (D 6) (R 6) [6,96,160,80,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,258,1] 13 (by decide) (choices 1) [1,4,8] r10960 c10960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1512
  · exact u1513
  · exact u1514

def b10961 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 88 274 36 73 137 265), lower := (rows 7 98 164 88 274 36 64 128 256), losses := [] }

theorem u10961 : Upper (D 6) (R 6) [6,96,160,80,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10961
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10962 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 88 274 40 69 133 261), lower := (rows 7 98 164 88 274 40 64 128 256), losses := [] }

theorem u10962 : Upper (D 6) (R 6) [6,96,160,80,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10962
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10963 : Route 9 := (fun mask => (mask,id))

def c10963 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10963 : Upper (D 6) (R 6) [6,96,160,80,260,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,260,1] 13 (by decide) (choices 1) [1,2,8] r10963 c10963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1515
  · exact u1516
  · exact u1517

def b10964 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 88 276 34 73 137 265), lower := (rows 7 98 164 88 276 34 64 128 256), losses := [] }

theorem u10964 : Upper (D 6) (R 6) [6,96,160,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10964
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10965 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 88 276 40 67 131 259), lower := (rows 7 98 164 88 276 40 64 128 256), losses := [] }

theorem u10965 : Upper (D 6) (R 6) [6,96,160,80,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10965
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10966 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 388 25 52 33 74 202 330), lower := (rows 7 98 388 25 52 33 64 128 256), losses := [] }

theorem u10966 : Upper (D 6) (R 6) [6,96,384,17,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10966
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10967 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 452, targets := 2 }], pairs := [(2,1),(3,6),(4,6)], upper := (rows 7 98 388 25 52 34 73 201 329), lower := (rows 7 98 388 25 52 34 64 128 256), losses := [] }

theorem u10967 : Upper (D 6) (R 6) [6,96,384,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10967
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10968 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 7 98 388 25 52 40 67 195 323), lower := (rows 7 98 388 25 52 40 64 128 256), losses := [] }

theorem u10968 : Upper (D 6) (R 6) [6,96,384,17,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10968
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10969 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 25 52 96 75 139 267), lower := (rows 7 98 388 25 52 96 64 128 256), losses := [] }

theorem u10969 : Upper (D 6) (R 6) [6,96,384,17,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10969
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10970 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 56, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 388 25 56 33 70 198 326), lower := (rows 7 98 388 25 56 33 64 128 256), losses := [] }

theorem u10970 : Upper (D 6) (R 6) [6,96,384,17,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10970
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10971 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 98 388 25 56 34 69 197 325), lower := (rows 7 98 388 25 56 34 64 128 256), losses := [] }

theorem u10971 : Upper (D 6) (R 6) [6,96,384,17,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10971
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10972 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 388 25 56 36 67 195 323), lower := (rows 7 98 388 25 56 36 64 128 256), losses := [] }

theorem u10972 : Upper (D 6) (R 6) [6,96,384,17,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10972
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10973 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 25 56 96 71 135 263), lower := (rows 7 98 388 25 56 96 64 128 256), losses := [] }

theorem u10973 : Upper (D 6) (R 6) [6,96,384,17,40,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10973
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10974 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 98 388 26 49 33 76 204 332), lower := (rows 7 98 388 26 49 33 64 128 256), losses := [] }

theorem u10974 : Upper (D 6) (R 6) [6,96,384,18,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10974
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10975 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(3,6),(4,6)], upper := (rows 7 98 388 26 49 36 73 201 329), lower := (rows 7 98 388 26 49 36 64 128 256), losses := [] }

theorem u10975 : Upper (D 6) (R 6) [6,96,384,18,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10975
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10976 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 98 388 26 49 40 69 197 325), lower := (rows 7 98 388 26 49 40 64 128 256), losses := [] }

theorem u10976 : Upper (D 6) (R 6) [6,96,384,18,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10976
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10977 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 26 49 96 77 141 269), lower := (rows 7 98 388 26 49 96 64 128 256), losses := [] }

theorem u10977 : Upper (D 6) (R 6) [6,96,384,18,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10977
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10978 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(3,6),(4,6)], upper := (rows 7 98 388 26 52 33 73 201 329), lower := (rows 7 98 388 26 52 33 64 128 256), losses := [] }

theorem u10978 : Upper (D 6) (R 6) [6,96,384,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10978
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10979 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 98 388 26 52 40 65 193 321), lower := (rows 7 98 388 26 52 40 64 128 256), losses := [] }

theorem u10979 : Upper (D 6) (R 6) [6,96,384,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10979
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10979
end Delivery.IrregularNine14.P06
