import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0011

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 263 11 52 88 48 225 193 193 449), lower := (rows 263 11 52 88 48 32 64 128 256), losses := [] }

theorem u1860 : Upper (D 0) (R 0) [262,9,48,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1860
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1861 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 263 11 52 88 80 161 225 161 417), lower := (rows 263 11 52 88 80 32 64 128 256), losses := [] }

theorem u1861 : Upper (D 0) (R 0) [262,9,48,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1861
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1862 : Route 9 := (fun mask => (mask,id))

def c1862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1862 : Upper (D 0) (R 0) [262,9,48,80,128] 13 := by
  apply FastRouting.sound _ _ [262,9,48,80,128] 13 (by decide) (choices 1) [1,64,128] r1862 c1862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u666
  · exact u667
  · exact u668

def b1863 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 263 11 52 200 17 240 240 240 496), lower := (rows 263 11 52 200 17 32 64 128 256), losses := [] }

theorem u1863 : Upper (D 0) (R 0) [262,9,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1863
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 263 11 52 200 48 241 209 209 465), lower := (rows 263 11 52 200 48 32 64 128 256), losses := [] }

theorem u1864 : Upper (D 0) (R 0) [262,9,48,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1864
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1865_1 : Upper (D 0) (R 0) [262,9,48,192,64,1] 13 :=
  permutation_upper _ _ _ [262,9,48,192,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u669

theorem m1865_16 : Upper (D 0) (R 0) [262,9,48,192,64,16] 13 :=
  permutation_upper _ _ _ [262,9,48,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u670

def r1865 : Route 9 := (fun mask => (mask,id))

def c1865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1865 : Upper (D 0) (R 0) [262,9,48,192,64] 13 := by
  apply FastRouting.sound _ _ [262,9,48,192,64] 13 (by decide) (choices 1) [1,16,128] r1865 c1865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1865_1
  · exact m1865_16
  · exact u671

def b1866 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 44 88 17 224 224 224 480), lower := (rows 263 19 44 88 17 32 64 128 256), losses := [] }

theorem u1866 : Upper (D 0) (R 0) [262,17,40,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1866
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 44 88 48 225 193 193 449), lower := (rows 263 19 44 88 48 32 64 128 256), losses := [] }

theorem u1867 : Upper (D 0) (R 0) [262,17,40,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1867
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1868 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 263 19 44 88 80 161 225 161 417), lower := (rows 263 19 44 88 80 32 64 128 256), losses := [] }

theorem u1868 : Upper (D 0) (R 0) [262,17,40,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1868
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1869 : Route 9 := (fun mask => (mask,id))

def c1869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1869 : Upper (D 0) (R 0) [262,17,40,80,128] 13 := by
  apply FastRouting.sound _ _ [262,17,40,80,128] 13 (by decide) (choices 1) [1,64,128] r1869 c1869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u672
  · exact u673
  · exact u674

def b1870 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 44 200 17 240 240 240 496), lower := (rows 263 19 44 200 17 32 64 128 256), losses := [] }

theorem u1870 : Upper (D 0) (R 0) [262,17,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1870
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 44 200 48 241 209 209 465), lower := (rows 263 19 44 200 48 32 64 128 256), losses := [] }

theorem u1871 : Upper (D 0) (R 0) [262,17,40,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1871
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1872 : Route 9 := (fun mask => (mask,id))

def c1872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1872 : Upper (D 0) (R 0) [262,17,40,192,64] 13 := by
  apply FastRouting.sound _ _ [262,17,40,192,64] 13 (by decide) (choices 1) [1,16,128] r1872 c1872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u675
  · exact u676
  · exact u677

def b1873 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 100 56 17 232 200 200 456), lower := (rows 263 19 100 56 17 32 64 128 256), losses := [] }

theorem u1873 : Upper (D 0) (R 0) [262,17,96,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1873
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1874 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 263 19 100 56 24 225 193 193 449), lower := (rows 263 19 100 56 24 32 64 128 256), losses := [] }

theorem u1874 : Upper (D 0) (R 0) [262,17,96,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1874
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 263 19 100 56 80 169 201 137 393), lower := (rows 263 19 100 56 80 32 64 128 256), losses := [] }

theorem u1875 : Upper (D 0) (R 0) [262,17,96,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1875
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1876 : Route 9 := (fun mask => (mask,id))

def c1876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1876 : Upper (D 0) (R 0) [262,17,96,48,128] 13 := by
  apply FastRouting.sound _ _ [262,17,96,48,128] 13 (by decide) (choices 1) [1,8,64,128] r1876 c1876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u678
  · exact u679
  · exact u680
  · exact u681

def b1877 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 100 152 17 232 232 232 488), lower := (rows 263 19 100 152 17 32 64 128 256), losses := [] }

theorem u1877 : Upper (D 0) (R 0) [262,17,96,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1877
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 263 19 100 152 24 225 225 225 481), lower := (rows 263 19 100 152 24 32 64 128 256), losses := [] }

theorem u1878 : Upper (D 0) (R 0) [262,17,96,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1878
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 100 152 48 233 201 201 457), lower := (rows 263 19 100 152 48 32 64 128 256), losses := [] }

theorem u1879 : Upper (D 0) (R 0) [262,17,96,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1879
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 263 19 100 152 144 105 105 233 361), lower := (rows 263 19 100 152 144 32 64 128 256), losses := [] }

theorem u1880 : Upper (D 0) (R 0) [262,17,96,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1880
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1881 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 100 168 17 248 216 216 472), lower := (rows 263 19 100 168 17 32 64 128 256), losses := [] }

theorem u1881 : Upper (D 0) (R 0) [262,17,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1881
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1882 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 263 19 100 168 24 241 209 209 465), lower := (rows 263 19 100 168 24 32 64 128 256), losses := [] }

theorem u1882 : Upper (D 0) (R 0) [262,17,96,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1882
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 263 19 100 168 80 185 217 153 409), lower := (rows 263 19 100 168 80 32 64 128 256), losses := [] }

theorem u1883 : Upper (D 0) (R 0) [262,17,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1883
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1884 : Route 9 := (fun mask => (mask,id))

def c1884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1884 : Upper (D 0) (R 0) [262,17,96,160,128] 13 := by
  apply FastRouting.sound _ _ [262,17,96,160,128] 13 (by decide) (choices 1) [1,8,16,64] r1884 c1884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u682
  · exact u683
  · exact u684
  · exact u685

def b1885 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 137 17 240 240 240 496), lower := (rows 263 26 100 137 17 32 64 128 256), losses := [] }

theorem u1885 : Upper (D 0) (R 0) [262,24,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1885
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1886 : Route 9 := (fun mask => (mask,id))

def c1886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1886 : Upper (D 0) (R 0) [262,24,96,129,32] 13 := by
  apply FastRouting.sound _ _ [262,24,96,129,32] 13 (by decide) (choices 1) [1,16,64,128] r1886 c1886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u686
  · exact u687
  · exact u688
  · exact u689

def b1887 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 263 26 100 137 144 113 113 241 369), lower := (rows 263 26 100 137 144 32 64 128 256), losses := [] }

theorem u1887 : Upper (D 0) (R 0) [262,24,96,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1887
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1888 : Route 9 := (fun mask => (mask,id))

def c1888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1888 : Upper (D 0) (R 0) [262,24,96,160,1] 13 := by
  apply FastRouting.sound _ _ [262,24,96,160,1] 13 (by decide) (choices 1) [1,16,64,128] r1888 c1888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u690
  · exact u691
  · exact u692
  · exact u693

def r1889 : Route 9 := (fun mask => (mask,id))

def c1889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1889 : Upper (D 0) (R 0) [262,24,96,160,64] 13 := by
  apply FastRouting.sound _ _ [262,24,96,160,64] 13 (by decide) (choices 1) [1,16,128] r1889 c1889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u694
  · exact u695
  · exact u696

def b1890 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 263 26 100 168 144 113 81 209 337), lower := (rows 263 26 100 168 144 32 64 128 256), losses := [] }

theorem u1890 : Upper (D 0) (R 0) [262,24,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1890
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1891 : Route 9 := (fun mask => (mask,id))

def c1891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1891 : Upper (D 0) (R 0) [262,48,192,80,1] 13 := by
  apply FastRouting.sound _ _ [262,48,192,80,1] 13 (by decide) (choices 1) [1,8,128] r1891 c1891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u697
  · exact u698
  · exact u699

def b1892 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 263 50 196 88 24 161 225 161 417), lower := (rows 263 50 196 88 24 32 64 128 256), losses := [] }

theorem u1892 : Upper (D 0) (R 0) [262,48,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1892
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 196 88 48 169 201 137 393), lower := (rows 263 50 196 88 48 32 64 128 256), losses := [] }

theorem u1893 : Upper (D 0) (R 0) [262,48,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1893
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 263 50 196 88 144 41 105 169 297), lower := (rows 263 50 196 88 144 32 64 128 256), losses := [] }

theorem u1894 : Upper (D 0) (R 0) [262,48,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1894
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1895 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 88 17 224 224 224 480), lower := (rows 275 7 44 88 17 32 64 128 256), losses := [] }

theorem u1895 : Upper (D 0) (R 0) [274,5,40,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1895
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1896 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 44 88 48 225 193 193 449), lower := (rows 275 7 44 88 48 32 64 128 256), losses := [] }

theorem u1896 : Upper (D 0) (R 0) [274,5,40,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1896
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1897 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 275 7 44 88 80 161 225 161 417), lower := (rows 275 7 44 88 80 32 64 128 256), losses := [] }

theorem u1897 : Upper (D 0) (R 0) [274,5,40,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1897
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1898 : Route 9 := (fun mask => (mask,id))

def c1898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1898 : Upper (D 0) (R 0) [274,5,40,80,128] 13 := by
  apply FastRouting.sound _ _ [274,5,40,80,128] 13 (by decide) (choices 1) [1,64,128] r1898 c1898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u700
  · exact u701
  · exact u702

def b1899 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 200 17 240 240 240 496), lower := (rows 275 7 44 200 17 32 64 128 256), losses := [] }

theorem u1899 : Upper (D 0) (R 0) [274,5,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1899
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1900 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 44 200 48 241 209 209 465), lower := (rows 275 7 44 200 48 32 64 128 256), losses := [] }

theorem u1900 : Upper (D 0) (R 0) [274,5,40,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1900
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1901 : Route 9 := (fun mask => (mask,id))

def c1901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1901 : Upper (D 0) (R 0) [274,5,40,192,64] 13 := by
  apply FastRouting.sound _ _ [274,5,40,192,64] 13 (by decide) (choices 1) [1,16,128] r1901 c1901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u703
  · exact u704
  · exact u705

def b1902 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 100 56 17 232 200 200 456), lower := (rows 275 7 100 56 17 32 64 128 256), losses := [] }

theorem u1902 : Upper (D 0) (R 0) [274,5,96,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1902
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 7 100 56 24 225 193 193 449), lower := (rows 275 7 100 56 24 32 64 128 256), losses := [] }

theorem u1903 : Upper (D 0) (R 0) [274,5,96,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1903
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1904 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 275 7 100 56 80 169 201 137 393), lower := (rows 275 7 100 56 80 32 64 128 256), losses := [] }

theorem u1904 : Upper (D 0) (R 0) [274,5,96,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1904
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1905 : Route 9 := (fun mask => (mask,id))

def c1905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1905 : Upper (D 0) (R 0) [274,5,96,48,128] 13 := by
  apply FastRouting.sound _ _ [274,5,96,48,128] 13 (by decide) (choices 1) [1,8,64,128] r1905 c1905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u706
  · exact u707
  · exact u708
  · exact u709

def b1906 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 100 152 17 232 232 232 488), lower := (rows 275 7 100 152 17 32 64 128 256), losses := [] }

theorem u1906 : Upper (D 0) (R 0) [274,5,96,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1906
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1907 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 275 7 100 152 24 225 225 225 481), lower := (rows 275 7 100 152 24 32 64 128 256), losses := [] }

theorem u1907 : Upper (D 0) (R 0) [274,5,96,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1907
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 100 152 48 233 201 201 457), lower := (rows 275 7 100 152 48 32 64 128 256), losses := [] }

theorem u1908 : Upper (D 0) (R 0) [274,5,96,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1908
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 7 100 152 144 105 105 233 361), lower := (rows 275 7 100 152 144 32 64 128 256), losses := [] }

theorem u1909 : Upper (D 0) (R 0) [274,5,96,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1909
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 100 168 17 248 216 216 472), lower := (rows 275 7 100 168 17 32 64 128 256), losses := [] }

theorem u1910 : Upper (D 0) (R 0) [274,5,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1910
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 275 7 100 168 24 241 209 209 465), lower := (rows 275 7 100 168 24 32 64 128 256), losses := [] }

theorem u1911 : Upper (D 0) (R 0) [274,5,96,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1911
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 7 100 168 80 185 217 153 409), lower := (rows 275 7 100 168 80 32 64 128 256), losses := [] }

theorem u1912 : Upper (D 0) (R 0) [274,5,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1912
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1913 : Route 9 := (fun mask => (mask,id))

def c1913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1913 : Upper (D 0) (R 0) [274,5,96,160,128] 13 := by
  apply FastRouting.sound _ _ [274,5,96,160,128] 13 (by decide) (choices 1) [1,8,16,64] r1913 c1913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u710
  · exact u711
  · exact u712
  · exact u713

def b1914 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 14 37 73 48 240 208 208 464), lower := (rows 275 14 37 73 48 32 64 128 256), losses := [] }

theorem u1914 : Upper (D 0) (R 0) [274,12,33,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1914
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1915 : Route 9 := (fun mask => (mask,id))

def c1915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1915 : Upper (D 0) (R 0) [274,12,33,65,128] 13 := by
  apply FastRouting.sound _ _ [274,12,33,65,128] 13 (by decide) (choices 1) [16,64,128] r1915 c1915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u714
  · exact u715
  · exact u716

def b1916 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 275 14 37 200 17 240 240 240 496), lower := (rows 275 14 37 200 17 32 64 128 256), losses := [] }

theorem u1916 : Upper (D 0) (R 0) [274,12,33,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1916
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 14 37 200 48 241 209 209 465), lower := (rows 275 14 37 200 48 32 64 128 256), losses := [] }

theorem u1917 : Upper (D 0) (R 0) [274,12,33,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1917
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 275 14 37 200 80 177 241 177 433), lower := (rows 275 14 37 200 80 32 64 128 256), losses := [] }

theorem u1918 : Upper (D 0) (R 0) [274,12,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1918
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1919 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 28 104 17 228 196 196 452), lower := (rows 275 35 28 104 17 32 64 128 256), losses := [] }

theorem u1919 : Upper (D 0) (R 0) [274,33,24,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1919
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1919
end Delivery.IrregularNine14.P00
