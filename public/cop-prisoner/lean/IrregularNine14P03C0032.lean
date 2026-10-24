import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0005

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 35 13 76 145 48 224 224 480), lower := (rows 259 35 13 76 145 48 64 128 256), losses := [] }

theorem u1920 : Upper (D 3) (R 3) [258,33,9,68,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1920
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 76 145 96 240 176 432), lower := (rows 259 35 13 76 145 96 64 128 256), losses := [] }

theorem u1921 : Upper (D 3) (R 3) [258,33,9,68,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1921
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1922 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 13 76 145 160 112 240 368), lower := (rows 259 35 13 76 145 160 64 128 256), losses := [] }

theorem u1922 : Upper (D 3) (R 3) [258,33,9,68,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1922
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1923 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 76 176 33 208 208 464), lower := (rows 259 35 13 76 176 33 64 128 256), losses := [] }

theorem u1923 : Upper (D 3) (R 3) [258,33,9,68,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1923
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 13 76 176 48 193 193 449), lower := (rows 259 35 13 76 176 48 64 128 256), losses := [] }

theorem u1924 : Upper (D 3) (R 3) [258,33,9,68,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1924
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 76 176 96 209 145 401), lower := (rows 259 35 13 76 176 96 64 128 256), losses := [] }

theorem u1925 : Upper (D 3) (R 3) [258,33,9,68,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1925
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 13 76 176 160 81 209 337), lower := (rows 259 35 13 76 176 160 64 128 256), losses := [] }

theorem u1926 : Upper (D 3) (R 3) [258,33,9,68,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1926
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 35 13 88 145 36 224 224 480), lower := (rows 259 35 13 88 145 36 64 128 256), losses := [] }

theorem u1927 : Upper (D 3) (R 3) [258,33,9,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1927
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 164, camps := [], pairs := [(1,7)], upper := (rows 259 35 13 88 145 96 228 164 420), lower := (rows 259 35 13 88 145 96 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 104 64 0 256), good := (rows 259 35 47 120 17 96 96 0 256) }] }

theorem u1928 : Upper (D 3) (R 3) [258,33,9,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1928
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 13 88 145 160 100 228 356), lower := (rows 259 35 13 88 145 160 64 128 256), losses := [] }

theorem u1929 : Upper (D 3) (R 3) [258,33,9,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1929
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1930 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 88 148 33 224 224 480), lower := (rows 259 35 13 88 148 33 64 128 256), losses := [] }

theorem u1930 : Upper (D 3) (R 3) [258,33,9,80,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1930
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 88 148 96 225 161 417), lower := (rows 259 35 13 88 148 96 64 128 256), losses := [] }

theorem u1931 : Upper (D 3) (R 3) [258,33,9,80,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1931
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1932 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 13 88 148 160 97 225 353), lower := (rows 259 35 13 88 148 160 64 128 256), losses := [] }

theorem u1932 : Upper (D 3) (R 3) [258,33,9,80,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1932
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1933 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 88 176 33 196 196 452), lower := (rows 259 35 13 88 176 33 64 128 256), losses := [] }

theorem u1933 : Upper (D 3) (R 3) [258,33,9,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1933
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 13 88 176 36 193 193 449), lower := (rows 259 35 13 88 176 36 64 128 256), losses := [] }

theorem u1934 : Upper (D 3) (R 3) [258,33,9,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1934
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 133, camps := [], pairs := [(1,7)], upper := (rows 259 35 13 88 176 96 197 133 389), lower := (rows 259 35 13 88 176 96 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 104 64 0 256), good := (rows 259 35 47 120 48 96 96 0 256) }] }

theorem u1935 : Upper (D 3) (R 3) [258,33,9,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1935
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1936 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 13 88 176 160 69 197 325), lower := (rows 259 35 13 88 176 160 64 128 256), losses := [] }

theorem u1936 : Upper (D 3) (R 3) [258,33,9,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1936
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1937 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 13 200 52 33 208 208 464), lower := (rows 259 35 13 200 52 33 64 128 256), losses := [] }

theorem u1937 : Upper (D 3) (R 3) [258,33,9,192,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1937
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 13 200 52 48 193 193 449), lower := (rows 259 35 13 200 52 48 64 128 256), losses := [] }

theorem u1938 : Upper (D 3) (R 3) [258,33,9,192,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1938
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 200 52 96 209 145 401), lower := (rows 259 35 13 200 52 96 64 128 256), losses := [] }

theorem u1939 : Upper (D 3) (R 3) [258,33,9,192,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1939
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1940 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 259 35 13 200 81 36 240 176 432), lower := (rows 259 35 13 200 81 36 64 128 256), losses := [] }

theorem u1940 : Upper (D 3) (R 3) [258,33,9,192,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1940
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1941 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 259 35 13 200 81 48 228 164 420), lower := (rows 259 35 13 200 81 48 64 128 256), losses := [] }

theorem u1941 : Upper (D 3) (R 3) [258,33,9,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1941
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1942 : PairBound 9 := { available := 52, camps := [], pairs := [(1,6)], upper := (rows 259 35 13 200 81 160 116 180 308), lower := (rows 259 35 13 200 81 160 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 168 0 128 256), good := (rows 259 35 47 168 17 160 0 160 256) }] }

theorem u1942 : Upper (D 3) (R 3) [258,33,9,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1942
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1943 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 13 200 112 33 212 148 404), lower := (rows 259 35 13 200 112 33 64 128 256), losses := [] }

theorem u1943 : Upper (D 3) (R 3) [258,33,9,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1943
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 35 13 200 112 36 209 145 401), lower := (rows 259 35 13 200 112 36 64 128 256), losses := [] }

theorem u1944 : Upper (D 3) (R 3) [258,33,9,192,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1944
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 35 13 200 112 48 197 133 389), lower := (rows 259 35 13 200 112 48 64 128 256), losses := [] }

theorem u1945 : Upper (D 3) (R 3) [258,33,9,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1945
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 259 35 13 200 112 160 85 149 277), lower := (rows 259 35 13 200 112 160 64 128 256), losses := [] }

theorem u1946 : Upper (D 3) (R 3) [258,33,9,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1946
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1947 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 259 35 28 73 145 36 224 224 480), lower := (rows 259 35 28 73 145 36 64 128 256), losses := [] }

theorem u1947 : Upper (D 3) (R 3) [258,33,24,65,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1947
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1948 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 259 35 28 73 145 96 228 164 420), lower := (rows 259 35 28 73 145 96 64 128 256), losses := [] }

theorem u1948 : Upper (D 3) (R 3) [258,33,24,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1948
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1949 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 73 148 33 224 224 480), lower := (rows 259 35 28 73 148 33 64 128 256), losses := [] }

theorem u1949 : Upper (D 3) (R 3) [258,33,24,65,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1949
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1950 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 73 148 96 225 161 417), lower := (rows 259 35 28 73 148 96 64 128 256), losses := [] }

theorem u1950 : Upper (D 3) (R 3) [258,33,24,65,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1950
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 28 73 148 160 97 225 353), lower := (rows 259 35 28 73 148 160 64 128 256), losses := [] }

theorem u1951 : Upper (D 3) (R 3) [258,33,24,65,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1951
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1952 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 28 73 176 33 196 196 452), lower := (rows 259 35 28 73 176 33 64 128 256), losses := [] }

theorem u1952 : Upper (D 3) (R 3) [258,33,24,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1952
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1953 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 28 73 176 36 193 193 449), lower := (rows 259 35 28 73 176 36 64 128 256), losses := [] }

theorem u1953 : Upper (D 3) (R 3) [258,33,24,65,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1953
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1954 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 259 35 28 73 176 96 197 133 389), lower := (rows 259 35 28 73 176 96 64 128 256), losses := [] }

theorem u1954 : Upper (D 3) (R 3) [258,33,24,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1954
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1955 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 28 73 176 160 69 197 325), lower := (rows 259 35 28 73 176 160 64 128 256), losses := [] }

theorem u1955 : Upper (D 3) (R 3) [258,33,24,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1955
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 259 35 44 73 145 36 208 208 464), lower := (rows 259 35 44 73 145 36 64 128 256), losses := [] }

theorem u1956 : Upper (D 3) (R 3) [258,33,40,65,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1956
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 259 35 44 73 145 48 196 196 452), lower := (rows 259 35 44 73 145 48 64 128 256), losses := [] }

theorem u1957 : Upper (D 3) (R 3) [258,33,40,65,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1957
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 73 145 96 212 148 404), lower := (rows 259 35 44 73 145 96 64 128 256), losses := [] }

theorem u1958 : Upper (D 3) (R 3) [258,33,40,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1958
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 44 73 145 160 84 212 340), lower := (rows 259 35 44 73 145 160 64 128 256), losses := [] }

theorem u1959 : Upper (D 3) (R 3) [258,33,40,65,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1959
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 44 73 148 33 208 208 464), lower := (rows 259 35 44 73 148 33 64 128 256), losses := [] }

theorem u1960 : Upper (D 3) (R 3) [258,33,40,65,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1960
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1961 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 44 73 148 48 193 193 449), lower := (rows 259 35 44 73 148 48 64 128 256), losses := [] }

theorem u1961 : Upper (D 3) (R 3) [258,33,40,65,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1961
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1962 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 73 148 96 209 145 401), lower := (rows 259 35 44 73 148 96 64 128 256), losses := [] }

theorem u1962 : Upper (D 3) (R 3) [258,33,40,65,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1962
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1963 : Route 9 := (fun mask => (mask,id))

def c1963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1963 : Upper (D 3) (R 3) [258,33,40,65,132,128] 13 := by
  apply FastRouting.sound _ _ [258,33,40,65,132,128] 13 (by decide) (choices 1) [1,16] r1963 c1963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u317
  · exact u318

def b1964 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 44 73 208 33 212 148 404), lower := (rows 259 35 44 73 208 33 64 128 256), losses := [] }

theorem u1964 : Upper (D 3) (R 3) [258,33,40,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1964
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 35 44 73 208 36 209 145 401), lower := (rows 259 35 44 73 208 36 64 128 256), losses := [] }

theorem u1965 : Upper (D 3) (R 3) [258,33,40,65,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1965
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1966 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 35 44 73 208 48 197 133 389), lower := (rows 259 35 44 73 208 48 64 128 256), losses := [] }

theorem u1966 : Upper (D 3) (R 3) [258,33,40,65,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1966
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1967 : Route 9 := (fun mask => (mask,id))

def c1967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1967 : Upper (D 3) (R 3) [258,33,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [258,33,40,65,192,128] 13 (by decide) (choices 1) [1,4,16] r1967 c1967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u319
  · exact u320
  · exact u321

def b1968 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 145 33 196 196 452), lower := (rows 259 35 44 88 145 33 64 128 256), losses := [] }

theorem u1968 : Upper (D 3) (R 3) [258,33,40,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1968
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1969 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 259 35 44 88 145 36 193 193 449), lower := (rows 259 35 44 88 145 36 64 128 256), losses := [] }

theorem u1969 : Upper (D 3) (R 3) [258,33,40,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1969
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1970 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 145 96 197 133 389), lower := (rows 259 35 44 88 145 96 64 128 256), losses := [] }

theorem u1970 : Upper (D 3) (R 3) [258,33,40,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1970
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1971 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 44 88 145 160 69 197 325), lower := (rows 259 35 44 88 145 160 64 128 256), losses := [] }

theorem u1971 : Upper (D 3) (R 3) [258,33,40,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1971
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1972 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 200 81 33 212 148 404), lower := (rows 259 35 44 200 81 33 64 128 256), losses := [] }

theorem u1972 : Upper (D 3) (R 3) [258,33,40,192,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1972
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1973 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 35 44 200 81 36 209 145 401), lower := (rows 259 35 44 200 81 36 64 128 256), losses := [] }

theorem u1973 : Upper (D 3) (R 3) [258,33,40,192,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1973
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 259 35 44 200 81 48 197 133 389), lower := (rows 259 35 44 200 81 48 64 128 256), losses := [] }

theorem u1974 : Upper (D 3) (R 3) [258,33,40,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1974
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 44 200 81 160 85 149 277), lower := (rows 259 35 44 200 81 160 64 128 256), losses := [] }

theorem u1975 : Upper (D 3) (R 3) [258,33,40,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1975
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 259 35 69 88 145 36 232 168 424), lower := (rows 259 35 69 88 145 36 64 128 256), losses := [] }

theorem u1976 : Upper (D 3) (R 3) [258,33,65,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1976
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 259 35 69 88 145 40 228 164 420), lower := (rows 259 35 69 88 145 40 64 128 256), losses := [] }

theorem u1977 : Upper (D 3) (R 3) [258,33,65,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1977
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1978 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 35 69 88 145 160 108 172 300), lower := (rows 259 35 69 88 145 160 64 128 256), losses := [] }

theorem u1978 : Upper (D 3) (R 3) [258,33,65,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1978
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 140, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 88 176 33 204 140 396), lower := (rows 259 35 69 88 176 33 64 128 256), losses := [] }

theorem u1979 : Upper (D 3) (R 3) [258,33,65,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1979
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P03
