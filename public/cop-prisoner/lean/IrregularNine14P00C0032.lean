import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0011
import IrregularNine14P00C0012

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 35 28 104 20 225 193 193 449), lower := (rows 275 35 28 104 20 32 64 128 256), losses := [] }

theorem u1920 : Upper (D 0) (R 0) [274,33,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1920
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 28 104 80 165 197 133 389), lower := (rows 275 35 28 104 80 32 64 128 256), losses := [] }

theorem u1921 : Upper (D 0) (R 0) [274,33,24,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1921
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1922 : Route 9 := (fun mask => (mask,id))

def c1922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1922 : Upper (D 0) (R 0) [274,33,24,96,128] 13 := by
  apply FastRouting.sound _ _ [274,33,24,96,128] 13 (by decide) (choices 1) [1,4,64,128] r1922 c1922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u717
  · exact u718
  · exact u719
  · exact u720

def b1923 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 28 200 17 228 228 228 484), lower := (rows 275 35 28 200 17 32 64 128 256), losses := [] }

theorem u1923 : Upper (D 0) (R 0) [274,33,24,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1923
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 275 35 28 200 20 225 225 225 481), lower := (rows 275 35 28 200 20 32 64 128 256), losses := [] }

theorem u1924 : Upper (D 0) (R 0) [274,33,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1924
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 28 200 48 229 197 197 453), lower := (rows 275 35 28 200 48 32 64 128 256), losses := [] }

theorem u1925 : Upper (D 0) (R 0) [274,33,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1925
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 28 200 80 165 229 165 421), lower := (rows 275 35 28 200 80 32 64 128 256), losses := [] }

theorem u1926 : Upper (D 0) (R 0) [274,33,24,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1926
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 44 88 17 228 196 196 452), lower := (rows 275 35 44 88 17 32 64 128 256), losses := [] }

theorem u1927 : Upper (D 0) (R 0) [274,33,40,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1927
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 35 44 88 20 225 193 193 449), lower := (rows 275 35 44 88 20 32 64 128 256), losses := [] }

theorem u1928 : Upper (D 0) (R 0) [274,33,40,80,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1928
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 44 88 80 165 197 133 389), lower := (rows 275 35 44 88 80 32 64 128 256), losses := [] }

theorem u1929 : Upper (D 0) (R 0) [274,33,40,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1929
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1930 : Route 9 := (fun mask => (mask,id))

def c1930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1930 : Upper (D 0) (R 0) [274,33,40,80,128] 13 := by
  apply FastRouting.sound _ _ [274,33,40,80,128] 13 (by decide) (choices 1) [1,4,64,128] r1930 c1930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u721
  · exact u722
  · exact u723
  · exact u724

def b1931 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 44 200 17 244 212 212 468), lower := (rows 275 35 44 200 17 32 64 128 256), losses := [] }

theorem u1931 : Upper (D 0) (R 0) [274,33,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1931
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1932 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 275 35 44 200 20 241 209 209 465), lower := (rows 275 35 44 200 20 32 64 128 256), losses := [] }

theorem u1932 : Upper (D 0) (R 0) [274,33,40,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1932
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1933 : Route 9 := (fun mask => (mask,id))

def c1933 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1933 : Upper (D 0) (R 0) [274,33,40,192,64] 13 := by
  apply FastRouting.sound _ _ [274,33,40,192,64] 13 (by decide) (choices 1) [1,4,16,128] r1933 c1933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u725
  · exact u726
  · exact u727
  · exact u728

def b1934 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 52 76 17 232 200 200 456), lower := (rows 275 35 52 76 17 32 64 128 256), losses := [] }

theorem u1934 : Upper (D 0) (R 0) [274,33,48,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1934
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 35 52 76 24 225 193 193 449), lower := (rows 275 35 52 76 24 32 64 128 256), losses := [] }

theorem u1935 : Upper (D 0) (R 0) [274,33,48,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1935
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1936 : Route 9 := (fun mask => (mask,id))

def c1936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1936 : Upper (D 0) (R 0) [274,33,48,68,64] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,64] 13 (by decide) (choices 1) [1,8,128] r1936 c1936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u729
  · exact u730
  · exact u731

def r1937 : Route 9 := (fun mask => (mask,id))

def c1937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1937 : Upper (D 0) (R 0) [274,33,48,68,128] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,128] 13 (by decide) (choices 1) [1,8,64,128] r1937 c1937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u732
  · exact u733
  · exact u734
  · exact u735

def b1938 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 52 200 17 236 204 204 460), lower := (rows 275 35 52 200 17 32 64 128 256), losses := [] }

theorem u1938 : Upper (D 0) (R 0) [274,33,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1938
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 275 35 52 200 20 233 201 201 457), lower := (rows 275 35 52 200 20 32 64 128 256), losses := [] }

theorem u1939 : Upper (D 0) (R 0) [274,33,48,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1939
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1940 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 275 35 52 200 24 229 197 197 453), lower := (rows 275 35 52 200 24 32 64 128 256), losses := [] }

theorem u1940 : Upper (D 0) (R 0) [274,33,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1940
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1941 : Route 9 := (fun mask => (mask,id))

def c1941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1941 : Upper (D 0) (R 0) [274,33,48,192,64] 13 := by
  apply FastRouting.sound _ _ [274,33,48,192,64] 13 (by decide) (choices 1) [1,4,8,128] r1941 c1941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u736
  · exact u737
  · exact u738
  · exact u739

def b1942 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 140 17 240 240 240 496), lower := (rows 275 35 76 140 17 32 64 128 256), losses := [] }

theorem u1942 : Upper (D 0) (R 0) [274,33,72,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1942
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1943 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 76 140 48 241 209 209 465), lower := (rows 275 35 76 140 48 32 64 128 256), losses := [] }

theorem u1943 : Upper (D 0) (R 0) [274,33,72,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1943
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 76 140 80 177 241 177 433), lower := (rows 275 35 76 140 80 32 64 128 256), losses := [] }

theorem u1944 : Upper (D 0) (R 0) [274,33,72,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1944
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 152 17 228 228 228 484), lower := (rows 275 35 76 152 17 32 64 128 256), losses := [] }

theorem u1945 : Upper (D 0) (R 0) [274,33,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1945
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 275 35 76 152 20 225 225 225 481), lower := (rows 275 35 76 152 20 32 64 128 256), losses := [] }

theorem u1946 : Upper (D 0) (R 0) [274,33,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1946
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1947 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 76 152 48 229 197 197 453), lower := (rows 275 35 76 152 48 32 64 128 256), losses := [] }

theorem u1947 : Upper (D 0) (R 0) [274,33,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1947
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1948 : Route 9 := (fun mask => (mask,id))

def c1948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1948 : Upper (D 0) (R 0) [274,33,72,144,64] 13 := by
  apply FastRouting.sound _ _ [274,33,72,144,64] 13 (by decide) (choices 1) [1,4,128] r1948 c1948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u740
  · exact u741
  · exact u742

def b1949 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 76 152 144 101 101 229 357), lower := (rows 275 35 76 152 144 32 64 128 256), losses := [] }

theorem u1949 : Upper (D 0) (R 0) [274,33,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1949
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1950 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 76 168 17 244 212 212 468), lower := (rows 275 35 76 168 17 32 64 128 256), losses := [] }

theorem u1950 : Upper (D 0) (R 0) [274,33,72,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1950
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 275 35 76 168 20 241 209 209 465), lower := (rows 275 35 76 168 20 32 64 128 256), losses := [] }

theorem u1951 : Upper (D 0) (R 0) [274,33,72,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1951
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1952 : Route 9 := (fun mask => (mask,id))

def c1952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1952 : Upper (D 0) (R 0) [274,33,72,160,64] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160,64] 13 (by decide) (choices 1) [1,4,16,128] r1952 c1952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u743
  · exact u744
  · exact u745
  · exact u746

def r1953 : Route 9 := (fun mask => (mask,id))

def c1953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1953 : Upper (D 0) (R 0) [274,33,72,160,128] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160,128] 13 (by decide) (choices 1) [1,4,16,64] r1953 c1953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u747
  · exact u748
  · exact u749
  · exact u750

def b1954 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 84 104 17 172 204 140 396), lower := (rows 275 35 84 104 17 32 64 128 256), losses := [] }

theorem u1954 : Upper (D 0) (R 0) [274,33,80,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1954
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1955 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 275 35 84 104 20 169 201 137 393), lower := (rows 275 35 84 104 20 32 64 128 256), losses := [] }

theorem u1955 : Upper (D 0) (R 0) [274,33,80,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1955
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 275 35 84 104 24 165 197 133 389), lower := (rows 275 35 84 104 24 32 64 128 256), losses := [] }

theorem u1956 : Upper (D 0) (R 0) [274,33,80,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1956
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1957 : Route 9 := (fun mask => (mask,id))

def c1957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1957 : Upper (D 0) (R 0) [274,33,80,96,128] 13 := by
  apply FastRouting.sound _ _ [274,33,80,96,128] 13 (by decide) (choices 1) [1,4,8,128] r1957 c1957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u751
  · exact u752
  · exact u753
  · exact u754

def b1958 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 84 168 17 236 204 204 460), lower := (rows 275 35 84 168 17 32 64 128 256), losses := [] }

theorem u1958 : Upper (D 0) (R 0) [274,33,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1958
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 275 35 84 168 20 233 201 201 457), lower := (rows 275 35 84 168 20 32 64 128 256), losses := [] }

theorem u1959 : Upper (D 0) (R 0) [274,33,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1959
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 275 35 84 168 24 229 197 197 453), lower := (rows 275 35 84 168 24 32 64 128 256), losses := [] }

theorem u1960 : Upper (D 0) (R 0) [274,33,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1960
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1961 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 84 168 80 173 205 141 397), lower := (rows 275 35 84 168 80 32 64 128 256), losses := [] }

theorem u1961 : Upper (D 0) (R 0) [274,33,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1961
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1962 : Route 9 := (fun mask => (mask,id))

def c1962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1962 : Upper (D 0) (R 0) [274,33,80,160,128] 13 := by
  apply FastRouting.sound _ _ [274,33,80,160,128] 13 (by decide) (choices 1) [1,4,8,64] r1962 c1962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u755
  · exact u756
  · exact u757
  · exact u758

def b1963 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 84 200 17 172 236 172 428), lower := (rows 275 35 84 200 17 32 64 128 256), losses := [] }

theorem u1963 : Upper (D 0) (R 0) [274,33,80,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1963
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1964 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 275 35 84 200 20 169 233 169 425), lower := (rows 275 35 84 200 20 32 64 128 256), losses := [] }

theorem u1964 : Upper (D 0) (R 0) [274,33,80,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1964
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 275 35 84 200 24 165 229 165 421), lower := (rows 275 35 84 200 24 32 64 128 256), losses := [] }

theorem u1965 : Upper (D 0) (R 0) [274,33,80,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1965
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1966 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 84 200 48 173 205 141 397), lower := (rows 275 35 84 200 48 32 64 128 256), losses := [] }

theorem u1966 : Upper (D 0) (R 0) [274,33,80,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1966
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1967 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 84 200 144 45 109 173 301), lower := (rows 275 35 84 200 144 32 64 128 256), losses := [] }

theorem u1967 : Upper (D 0) (R 0) [274,33,80,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1967
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1968 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 100 200 17 188 220 156 412), lower := (rows 275 35 100 200 17 32 64 128 256), losses := [] }

theorem u1968 : Upper (D 0) (R 0) [274,33,96,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1968
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1969 : PairBound 9 := { available := 153, camps := [], pairs := [], upper := (rows 275 35 100 200 20 185 217 153 409), lower := (rows 275 35 100 200 20 32 64 128 256), losses := [] }

theorem u1969 : Upper (D 0) (R 0) [274,33,96,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1969
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1970 : PairBound 9 := { available := 149, camps := [], pairs := [], upper := (rows 275 35 100 200 24 181 213 149 405), lower := (rows 275 35 100 200 24 32 64 128 256), losses := [] }

theorem u1970 : Upper (D 0) (R 0) [274,33,96,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1970
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1971 : Route 9 := (fun mask => (mask,id))

def c1971 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1971 : Upper (D 0) (R 0) [274,33,96,192,128] 13 := by
  apply FastRouting.sound _ _ [274,33,96,192,128] 13 (by decide) (choices 1) [1,4,8,16] r1971 c1971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u759
  · exact u760
  · exact u761
  · exact u762

def b1972 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 13 200 17 240 240 240 496), lower := (rows 275 38 13 200 17 32 64 128 256), losses := [] }

theorem u1972 : Upper (D 0) (R 0) [274,36,9,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1972
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1973 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 13 200 48 241 209 209 465), lower := (rows 275 38 13 200 48 32 64 128 256), losses := [] }

theorem u1973 : Upper (D 0) (R 0) [274,36,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1973
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 177, camps := [], pairs := [(1,6)], upper := (rows 275 38 13 200 80 177 241 177 433), lower := (rows 275 38 13 200 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 33 0 129 257), good := (rows 435 38 431 136 16 32 0 128 256) }] }

theorem u1974 : Upper (D 0) (R 0) [274,36,9,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1974
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 69 56 17 232 200 200 456), lower := (rows 275 38 69 56 17 32 64 128 256), losses := [] }

theorem u1975 : Upper (D 0) (R 0) [274,36,65,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1975
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 38 69 56 24 225 193 193 449), lower := (rows 275 38 69 56 24 32 64 128 256), losses := [] }

theorem u1976 : Upper (D 0) (R 0) [274,36,65,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1976
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 56 80 169 201 137 393), lower := (rows 275 38 69 56 80 32 64 128 256), losses := [] }

theorem u1977 : Upper (D 0) (R 0) [274,36,65,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1977
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1978 : Route 9 := (fun mask => (mask,id))

def c1978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1978 : Upper (D 0) (R 0) [274,36,65,48,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,48,128] 13 (by decide) (choices 1) [1,8,64,128] r1978 c1978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u763
  · exact u764
  · exact u765
  · exact u766

def b1979 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 69 88 17 168 232 168 424), lower := (rows 275 38 69 88 17 32 64 128 256), losses := [] }

theorem u1979 : Upper (D 0) (R 0) [274,36,65,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1979
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P00
