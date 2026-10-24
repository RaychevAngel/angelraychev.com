import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0004

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 328 148 33 240 176 432), lower := (rows 35 67 44 328 148 33 64 128 256), losses := [] }

theorem u1920 : Upper (D 8) (R 8) [34,65,40,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 328 148 48 225 161 417), lower := (rows 35 67 44 328 148 48 64 128 256), losses := [] }

theorem u1921 : Upper (D 8) (R 8) [34,65,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1921 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1922 : Route 9 := (fun mask => (mask,id))

def c1922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1922 : Upper (D 8) (R 8) [34,65,40,320,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,132,128] 13 (by decide) (choices 1) [1,16,32] r1922 c1922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u264
  · exact u265
  · exact u266

def b1923 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 328 176 33 212 148 404), lower := (rows 35 67 44 328 176 33 64 128 256), losses := [] }

theorem u1923 : Upper (D 8) (R 8) [34,65,40,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 44 328 176 36 209 145 401), lower := (rows 35 67 44 328 176 36 64 128 256), losses := [] }

theorem u1924 : Upper (D 8) (R 8) [34,65,40,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1924 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 328 176 48 197 133 389), lower := (rows 35 67 44 328 176 48 64 128 256), losses := [] }

theorem u1925 : Upper (D 8) (R 8) [34,65,40,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1925 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 328 176 160 85 149 277), lower := (rows 35 67 44 328 176 160 64 128 256), losses := [] }

theorem u1926 : Upper (D 8) (R 8) [34,65,40,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 392 84 33 240 176 432), lower := (rows 35 67 44 392 84 33 64 128 256), losses := [] }

theorem u1927 : Upper (D 8) (R 8) [34,65,40,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 392 84 48 225 161 417), lower := (rows 35 67 44 392 84 48 64 128 256), losses := [] }

theorem u1928 : Upper (D 8) (R 8) [34,65,40,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1928 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 392 84 160 113 177 305), lower := (rows 35 67 44 392 84 160 64 128 256), losses := [] }

theorem u1929 : Upper (D 8) (R 8) [34,65,40,384,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1930 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 392 176 33 84 212 340), lower := (rows 35 67 44 392 176 33 64 128 256), losses := [] }

theorem u1930 : Upper (D 8) (R 8) [34,65,40,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 44 392 176 36 81 209 337), lower := (rows 35 67 44 392 176 36 64 128 256), losses := [] }

theorem u1931 : Upper (D 8) (R 8) [34,65,40,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1931 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1932 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 44 392 176 48 69 197 325), lower := (rows 35 67 44 392 176 48 64 128 256), losses := [] }

theorem u1932 : Upper (D 8) (R 8) [34,65,40,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1932 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1933 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 392 176 96 85 149 277), lower := (rows 35 67 44 392 176 96 64 128 256), losses := [] }

theorem u1933 : Upper (D 8) (R 8) [34,65,40,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 392 208 33 116 180 308), lower := (rows 35 67 44 392 208 33 64 128 256), losses := [] }

theorem u1934 : Upper (D 8) (R 8) [34,65,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 44 392 208 36 113 177 305), lower := (rows 35 67 44 392 208 36 64 128 256), losses := [] }

theorem u1935 : Upper (D 8) (R 8) [34,65,40,384,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1935 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1936 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 44 392 208 48 101 165 293), lower := (rows 35 67 44 392 208 48 64 128 256), losses := [] }

theorem u1936 : Upper (D 8) (R 8) [34,65,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1936 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1937 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 152 304 33 228 164 420), lower := (rows 35 67 76 152 304 33 64 128 256), losses := [] }

theorem u1937 : Upper (D 8) (R 8) [34,65,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 152 304 36 225 161 417), lower := (rows 35 67 76 152 304 36 64 128 256), losses := [] }

theorem u1938 : Upper (D 8) (R 8) [34,65,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1938 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1939 : Route 9 := (fun mask => (mask,id))

def c1939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1939 : Upper (D 8) (R 8) [34,65,72,144,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,288,128] 13 (by decide) (choices 1) [1,4,32] r1939 c1939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u267
  · exact u268
  · exact u269

def b1940 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 168 276 33 240 176 432), lower := (rows 35 67 76 168 276 33 64 128 256), losses := [] }

theorem u1940 : Upper (D 8) (R 8) [34,65,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1941 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 168 276 48 225 161 417), lower := (rows 35 67 76 168 276 48 64 128 256), losses := [] }

theorem u1941 : Upper (D 8) (R 8) [34,65,72,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1941 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1942 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 168 276 160 113 177 305), lower := (rows 35 67 76 168 276 160 64 128 256), losses := [] }

theorem u1942 : Upper (D 8) (R 8) [34,65,72,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1943 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 168 304 33 212 148 404), lower := (rows 35 67 76 168 304 33 64 128 256), losses := [] }

theorem u1943 : Upper (D 8) (R 8) [34,65,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 76 168 304 36 209 145 401), lower := (rows 35 67 76 168 304 36 64 128 256), losses := [] }

theorem u1944 : Upper (D 8) (R 8) [34,65,72,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1944 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 76 168 304 48 197 133 389), lower := (rows 35 67 76 168 304 48 64 128 256), losses := [] }

theorem u1945 : Upper (D 8) (R 8) [34,65,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1945 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 168 304 160 85 149 277), lower := (rows 35 67 76 168 304 160 64 128 256), losses := [] }

theorem u1946 : Upper (D 8) (R 8) [34,65,72,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1947 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 168 400 33 116 180 308), lower := (rows 35 67 76 168 400 33 64 128 256), losses := [] }

theorem u1947 : Upper (D 8) (R 8) [34,65,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1948 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 76 168 400 36 113 177 305), lower := (rows 35 67 76 168 400 36 64 128 256), losses := [] }

theorem u1948 : Upper (D 8) (R 8) [34,65,72,160,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1948 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1949 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 76 168 400 48 101 165 293), lower := (rows 35 67 76 168 400 48 64 128 256), losses := [] }

theorem u1949 : Upper (D 8) (R 8) [34,65,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1949 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1950 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 280 176 33 228 164 420), lower := (rows 35 67 76 280 176 33 64 128 256), losses := [] }

theorem u1950 : Upper (D 8) (R 8) [34,65,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 280 176 36 225 161 417), lower := (rows 35 67 76 280 176 36 64 128 256), losses := [] }

theorem u1951 : Upper (D 8) (R 8) [34,65,72,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1951 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1952 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 280 176 160 101 165 293), lower := (rows 35 67 76 280 176 160 64 128 256), losses := [] }

theorem u1952 : Upper (D 8) (R 8) [34,65,72,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1953 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 296 148 33 240 176 432), lower := (rows 35 67 76 296 148 33 64 128 256), losses := [] }

theorem u1953 : Upper (D 8) (R 8) [34,65,72,288,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1954 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 296 148 48 225 161 417), lower := (rows 35 67 76 296 148 48 64 128 256), losses := [] }

theorem u1954 : Upper (D 8) (R 8) [34,65,72,288,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1954 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1955 : Route 9 := (fun mask => (mask,id))

def c1955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1955 : Upper (D 8) (R 8) [34,65,72,288,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288,132,128] 13 (by decide) (choices 1) [1,16,32] r1955 c1955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u270
  · exact u271
  · exact u272

def b1956 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 296 176 33 212 148 404), lower := (rows 35 67 76 296 176 33 64 128 256), losses := [] }

theorem u1956 : Upper (D 8) (R 8) [34,65,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 76 296 176 36 209 145 401), lower := (rows 35 67 76 296 176 36 64 128 256), losses := [] }

theorem u1957 : Upper (D 8) (R 8) [34,65,72,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1957 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 76 296 176 48 197 133 389), lower := (rows 35 67 76 296 176 48 64 128 256), losses := [] }

theorem u1958 : Upper (D 8) (R 8) [34,65,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1958 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 296 176 160 85 149 277), lower := (rows 35 67 76 296 176 160 64 128 256), losses := [] }

theorem u1959 : Upper (D 8) (R 8) [34,65,72,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 392 176 33 116 180 308), lower := (rows 35 67 76 392 176 33 64 128 256), losses := [] }

theorem u1960 : Upper (D 8) (R 8) [34,65,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1961 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 76 392 176 36 113 177 305), lower := (rows 35 67 76 392 176 36 64 128 256), losses := [] }

theorem u1961 : Upper (D 8) (R 8) [34,65,72,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1961 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1962 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 76 392 176 48 101 165 293), lower := (rows 35 67 76 392 176 48 64 128 256), losses := [] }

theorem u1962 : Upper (D 8) (R 8) [34,65,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1962 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1963 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 296 176 33 84 212 340), lower := (rows 35 67 140 296 176 33 64 128 256), losses := [] }

theorem u1963 : Upper (D 8) (R 8) [34,65,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1964 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 140 296 176 36 81 209 337), lower := (rows 35 67 140 296 176 36 64 128 256), losses := [] }

theorem u1964 : Upper (D 8) (R 8) [34,65,136,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1964 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 140 296 176 48 69 197 325), lower := (rows 35 67 140 296 176 48 64 128 256), losses := [] }

theorem u1965 : Upper (D 8) (R 8) [34,65,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1965 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1966 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 140 296 176 96 85 149 277), lower := (rows 35 67 140 296 176 96 64 128 256), losses := [] }

theorem u1966 : Upper (D 8) (R 8) [34,65,136,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1967 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 296 208 33 116 180 308), lower := (rows 35 67 140 296 208 33 64 128 256), losses := [] }

theorem u1967 : Upper (D 8) (R 8) [34,65,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1968 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 140 296 208 36 113 177 305), lower := (rows 35 67 140 296 208 36 64 128 256), losses := [] }

theorem u1968 : Upper (D 8) (R 8) [34,65,136,288,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1968 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1969 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 140 296 208 48 101 165 293), lower := (rows 35 67 140 296 208 48 64 128 256), losses := [] }

theorem u1969 : Upper (D 8) (R 8) [34,65,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1969 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1970 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 328 176 33 116 180 308), lower := (rows 35 67 140 328 176 33 64 128 256), losses := [] }

theorem u1970 : Upper (D 8) (R 8) [34,65,136,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1971 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 140 328 176 36 113 177 305), lower := (rows 35 67 140 328 176 36 64 128 256), losses := [] }

theorem u1971 : Upper (D 8) (R 8) [34,65,136,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1971 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1972 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 140 328 176 48 101 165 293), lower := (rows 35 67 140 328 176 48 64 128 256), losses := [] }

theorem u1972 : Upper (D 8) (R 8) [34,65,136,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1972 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1973 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 164 200 276 33 120 184 312), lower := (rows 35 67 164 200 276 33 64 128 256), losses := [] }

theorem u1973 : Upper (D 8) (R 8) [34,65,160,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 164 200 276 40 113 177 305), lower := (rows 35 67 164 200 276 40 64 128 256), losses := [] }

theorem u1974 : Upper (D 8) (R 8) [34,65,160,192,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1974 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 67 164 200 276 48 105 169 297), lower := (rows 35 67 164 200 276 48 64 128 256), losses := [] }

theorem u1975 : Upper (D 8) (R 8) [34,65,160,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1975 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 164 200 280 33 116 180 308), lower := (rows 35 67 164 200 280 33 64 128 256), losses := [] }

theorem u1976 : Upper (D 8) (R 8) [34,65,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 164 200 280 36 113 177 305), lower := (rows 35 67 164 200 280 36 64 128 256), losses := [] }

theorem u1977 : Upper (D 8) (R 8) [34,65,160,192,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1977 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1978 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 164 200 280 48 101 165 293), lower := (rows 35 67 164 200 280 48 64 128 256), losses := [] }

theorem u1978 : Upper (D 8) (R 8) [34,65,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1978 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 164 200 304 33 92 156 284), lower := (rows 35 67 164 200 304 33 64 128 256), losses := [] }

theorem u1979 : Upper (D 8) (R 8) [34,65,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P08
