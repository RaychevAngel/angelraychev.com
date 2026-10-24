import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0024

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10860 : Route 9 := (fun mask => (mask,id))

def c10860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10860 : Upper (D 6) (R 6) [6,96,136,48,258,4] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,258,4] 13 (by decide) (choices 1) [1] r10860 c10860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u1477

def b10861 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 56 274 96 69 133 261), lower := (rows 7 98 140 56 274 96 64 128 256), losses := [] }

theorem u10861 : Upper (D 6) (R 6) [6,96,136,48,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10861
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10862 : Route 9 := (fun mask => (mask,id))

def c10862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10862 : Upper (D 6) (R 6) [6,96,136,48,260,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,260,1] 13 (by decide) (choices 1) [1,2] r10862 c10862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1478
  · exact u1479

def b10863 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 7 98 140 56 276 34 65 193 321), lower := (rows 7 98 140 56 276 34 64 128 256), losses := [] }

theorem u10863 : Upper (D 6) (R 6) [6,96,136,48,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10863
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10864 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 56 276 96 67 131 259), lower := (rows 7 98 140 56 276 96 64 128 256), losses := [] }

theorem u10864 : Upper (D 6) (R 6) [6,96,136,48,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10864
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10865 : Route 9 := (fun mask => (mask,id))

def c10865 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10865 : Upper (D 6) (R 6) [6,96,136,48,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320,1] 13 (by decide) (choices 1) [1,2,4] r10865 c10865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1480
  · exact u1481
  · exact u1482

def b10866 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 140 56 336 34 69 133 261), lower := (rows 7 98 140 56 336 34 64 128 256), losses := [] }

theorem u10866 : Upper (D 6) (R 6) [6,96,136,48,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10866
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10867 : Route 9 := (fun mask => (mask,id))

def c10867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10867 : Upper (D 6) (R 6) [6,96,136,48,320,4] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320,4] 13 (by decide) (choices 1) [1,2] r10867 c10867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1483
  · exact u1484

def b10868 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 98 140 265 49 34 84 212 340), lower := (rows 7 98 140 265 49 34 64 128 256), losses := [] }

theorem u10868 : Upper (D 6) (R 6) [6,96,136,257,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10868
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10869 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 98 140 265 49 36 82 210 338), lower := (rows 7 98 140 265 49 36 64 128 256), losses := [] }

theorem u10869 : Upper (D 6) (R 6) [6,96,136,257,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10869
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10870 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 98 140 265 49 48 70 198 326), lower := (rows 7 98 140 265 49 48 64 128 256), losses := [] }

theorem u10870 : Upper (D 6) (R 6) [6,96,136,257,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10870
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10871 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 265 49 96 86 150 278), lower := (rows 7 98 140 265 49 96 64 128 256), losses := [] }

theorem u10871 : Upper (D 6) (R 6) [6,96,136,257,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10871
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10872 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 7 98 140 265 52 33 82 210 338), lower := (rows 7 98 140 265 52 33 64 128 256), losses := [] }

theorem u10872 : Upper (D 6) (R 6) [6,96,136,257,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10872
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10873 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 0, region := 48, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 140 265 52 34 81 209 337), lower := (rows 7 98 140 265 52 34 64 128 256), losses := [] }

theorem u10873 : Upper (D 6) (R 6) [6,96,136,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10873
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10874 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 140 265 52 48 67 195 323), lower := (rows 7 98 140 265 52 48 64 128 256), losses := [] }

theorem u10874 : Upper (D 6) (R 6) [6,96,136,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10874
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10875 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 265 52 96 83 147 275), lower := (rows 7 98 140 265 52 96 64 128 256), losses := [] }

theorem u10875 : Upper (D 6) (R 6) [6,96,136,257,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10875
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10876 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 98 140 266 49 33 84 212 340), lower := (rows 7 98 140 266 49 33 64 128 256), losses := [] }

theorem u10876 : Upper (D 6) (R 6) [6,96,136,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10876
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10877 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 330, targets := 4 },{ cop := 0, region := 48, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 98 140 266 49 36 81 209 337), lower := (rows 7 98 140 266 49 36 64 128 256), losses := [] }

theorem u10877 : Upper (D 6) (R 6) [6,96,136,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10877
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10878 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 140 266 49 48 69 197 325), lower := (rows 7 98 140 266 49 48 64 128 256), losses := [] }

theorem u10878 : Upper (D 6) (R 6) [6,96,136,258,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10878
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10879 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 266 49 96 85 149 277), lower := (rows 7 98 140 266 49 96 64 128 256), losses := [] }

theorem u10879 : Upper (D 6) (R 6) [6,96,136,258,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10879
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10880 : Route 9 := (fun mask => (mask,id))

def c10880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10880 : Upper (D 6) (R 6) [6,96,136,258,36,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258,36,1] 13 (by decide) (choices 1) [1,16] r10880 c10880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1485
  · exact u1486

def b10881 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 140 266 52 48 65 193 321), lower := (rows 7 98 140 266 52 48 64 128 256), losses := [] }

theorem u10881 : Upper (D 6) (R 6) [6,96,136,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10881
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10882 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 266 52 96 81 145 273), lower := (rows 7 98 140 266 52 96 64 128 256), losses := [] }

theorem u10882 : Upper (D 6) (R 6) [6,96,136,258,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10882
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10883 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 98 140 268 49 33 82 210 338), lower := (rows 7 98 140 268 49 33 64 128 256), losses := [] }

theorem u10883 : Upper (D 6) (R 6) [6,96,136,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10883
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10884 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 98 140 268 49 34 81 209 337), lower := (rows 7 98 140 268 49 34 64 128 256), losses := [] }

theorem u10884 : Upper (D 6) (R 6) [6,96,136,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10884
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10885 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 140 268 49 48 67 195 323), lower := (rows 7 98 140 268 49 48 64 128 256), losses := [] }

theorem u10885 : Upper (D 6) (R 6) [6,96,136,260,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10885
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10886 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 268 49 96 83 147 275), lower := (rows 7 98 140 268 49 96 64 128 256), losses := [] }

theorem u10886 : Upper (D 6) (R 6) [6,96,136,260,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10886
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10887 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 7 98 140 280 49 33 70 198 326), lower := (rows 7 98 140 280 49 33 64 128 256), losses := [] }

theorem u10887 : Upper (D 6) (R 6) [6,96,136,272,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10887
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10888 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 98 140 280 49 34 69 197 325), lower := (rows 7 98 140 280 49 34 64 128 256), losses := [] }

theorem u10888 : Upper (D 6) (R 6) [6,96,136,272,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10888
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10889 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 98 140 280 49 36 67 195 323), lower := (rows 7 98 140 280 49 36 64 128 256), losses := [] }

theorem u10889 : Upper (D 6) (R 6) [6,96,136,272,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10889
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10890 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 280 49 96 71 135 263), lower := (rows 7 98 140 280 49 96 64 128 256), losses := [] }

theorem u10890 : Upper (D 6) (R 6) [6,96,136,272,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10890
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10891 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 98 140 280 52 33 67 195 323), lower := (rows 7 98 140 280 52 33 64 128 256), losses := [] }

theorem u10891 : Upper (D 6) (R 6) [6,96,136,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10891
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10892 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 0, region := 48, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 140 280 52 34 65 193 321), lower := (rows 7 98 140 280 52 34 64 128 256), losses := [] }

theorem u10892 : Upper (D 6) (R 6) [6,96,136,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10892
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10893 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 280 52 96 67 131 259), lower := (rows 7 98 140 280 52 96 64 128 256), losses := [] }

theorem u10893 : Upper (D 6) (R 6) [6,96,136,272,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10893
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10894 : Route 9 := (fun mask => (mask,id))

def c10894 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10894 : Upper (D 6) (R 6) [6,96,136,288,65,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,65,1] 13 (by decide) (choices 1) [2,4,16] r10894 c10894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1487
  · exact u1488
  · exact u1489

def b10895 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 7 98 140 296 81 34 85 149 277), lower := (rows 7 98 140 296 81 34 64 128 256), losses := [] }

theorem u10895 : Upper (D 6) (R 6) [6,96,136,288,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10895
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10896 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 7 98 140 296 81 36 83 147 275), lower := (rows 7 98 140 296 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 98 172 296 114 36 64 128 256) }] }

theorem u10896 : Upper (D 6) (R 6) [6,96,136,288,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10896
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10897 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 296 81 48 71 135 263), lower := (rows 7 98 140 296 81 48 64 128 256), losses := [] }

theorem u10897 : Upper (D 6) (R 6) [6,96,136,288,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10897
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10898 : Route 9 := (fun mask => (mask,id))

def c10898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10898 : Upper (D 6) (R 6) [6,96,136,288,68,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,68,1] 13 (by decide) (choices 1) [1,2,16] r10898 c10898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1490
  · exact u1491
  · exact u1492

def b10899 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 7 98 140 296 84 34 81 145 273), lower := (rows 7 98 140 296 84 34 64 128 256), losses := [] }

theorem u10899 : Upper (D 6) (R 6) [6,96,136,288,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10899
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10900 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 296 84 48 67 131 259), lower := (rows 7 98 140 296 84 48 64 128 256), losses := [] }

theorem u10900 : Upper (D 6) (R 6) [6,96,136,288,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10900
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10901 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 25 280 33 70 198 326), lower := (rows 7 98 164 25 280 33 64 128 256), losses := [] }

theorem u10901 : Upper (D 6) (R 6) [6,96,160,17,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10901
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10902 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 25 280 34 69 197 325), lower := (rows 7 98 164 25 280 34 64 128 256), losses := [] }

theorem u10902 : Upper (D 6) (R 6) [6,96,160,17,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10902
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10903 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 25 280 36 67 195 323), lower := (rows 7 98 164 25 280 36 64 128 256), losses := [] }

theorem u10903 : Upper (D 6) (R 6) [6,96,160,17,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10903
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10904 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 164 25 280 96 71 135 263), lower := (rows 7 98 164 25 280 96 64 128 256), losses := [] }

theorem u10904 : Upper (D 6) (R 6) [6,96,160,17,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10904
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10905 : Route 9 := (fun mask => (mask,id))

def c10905 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10905 : Upper (D 6) (R 6) [6,96,160,17,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,320,1] 13 (by decide) (choices 1) [2,4,8] r10905 c10905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1493
  · exact u1494
  · exact u1495

def b10906 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 25 336 34 77 141 269), lower := (rows 7 98 164 25 336 34 64 128 256), losses := [] }

theorem u10906 : Upper (D 6) (R 6) [6,96,160,17,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10906
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10907 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 25 336 36 75 139 267), lower := (rows 7 98 164 25 336 36 64 128 256), losses := [] }

theorem u10907 : Upper (D 6) (R 6) [6,96,160,17,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10907
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10908 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 25 336 40 71 135 263), lower := (rows 7 98 164 25 336 40 64 128 256), losses := [] }

theorem u10908 : Upper (D 6) (R 6) [6,96,160,17,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10908
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10909 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 164 26 273 33 76 204 332), lower := (rows 7 98 164 26 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 37 96 164 508 305 33 64 128 256) }] }

theorem u10909 : Upper (D 6) (R 6) [6,96,160,18,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10909
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10910 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 98 164 26 273 36 73 201 329), lower := (rows 7 98 164 26 273 36 64 128 256), losses := [] }

theorem u10910 : Upper (D 6) (R 6) [6,96,160,18,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10910
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10911 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 26 273 40 69 197 325), lower := (rows 7 98 164 26 273 40 64 128 256), losses := [] }

theorem u10911 : Upper (D 6) (R 6) [6,96,160,18,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10911
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10912 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 164 26 273 96 77 141 269), lower := (rows 7 98 164 26 273 96 64 128 256), losses := [] }

theorem u10912 : Upper (D 6) (R 6) [6,96,160,18,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10912
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10913 : Route 9 := (fun mask => (mask,id))

def c10913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10913 : Upper (D 6) (R 6) [6,96,160,18,260,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,260,1] 13 (by decide) (choices 1) [1,8] r10913 c10913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1496
  · exact u1497

def b10914 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 26 276 40 65 193 321), lower := (rows 7 98 164 26 276 40 64 128 256), losses := [] }

theorem u10914 : Upper (D 6) (R 6) [6,96,160,18,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10914
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10915 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 164 26 276 96 73 137 265), lower := (rows 7 98 164 26 276 96 64 128 256), losses := [] }

theorem u10915 : Upper (D 6) (R 6) [6,96,160,18,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10915
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10916 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 28 81 33 330 394 266), lower := (rows 7 98 164 28 81 33 64 128 256), losses := [] }

theorem u10916 : Upper (D 6) (R 6) [6,96,160,20,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10916
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10917 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 98 164 28 81 34 329 393 265), lower := (rows 7 98 164 28 81 34 64 128 256), losses := [] }

theorem u10917 : Upper (D 6) (R 6) [6,96,160,20,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10917
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10918 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 28 81 40 323 387 259), lower := (rows 7 98 164 28 81 40 64 128 256), losses := [] }

theorem u10918 : Upper (D 6) (R 6) [6,96,160,20,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10918
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10919 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 28 81 288 75 139 267), lower := (rows 7 98 164 28 81 288 64 128 256), losses := [] }

theorem u10919 : Upper (D 6) (R 6) [6,96,160,20,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10919
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10919
end Delivery.IrregularNine14.P06
