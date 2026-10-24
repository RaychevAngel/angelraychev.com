import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0001

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 7 42 196 280 81 160 65 162 290), lower := (rows 7 42 196 280 81 160 65 128 256), losses := [] }

theorem u1920 : Upper (D 7) (R 7) [6,40,192,272,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 428, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 196 280 81 160 66 161 289), lower := (rows 7 42 196 280 81 160 66 128 256), losses := [] }

theorem u1921 : Upper (D 7) (R 7) [6,40,192,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1922 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 42 196 280 81 160 96 131 259), lower := (rows 7 42 196 280 81 160 96 128 256), losses := [] }

theorem u1922 : Upper (D 7) (R 7) [6,40,192,272,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1923 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,0),(2,1),(4,5),(4,7)], upper := (rows 7 42 196 280 82 33 65 160 416), lower := (rows 7 42 196 280 82 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 32 64 162 290), good := (rows 390 426 196 284 478 416 64 128 256) }] }

theorem u1923 : Upper (D 7) (R 7) [6,40,192,272,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 280 82 33 96 129 385), lower := (rows 7 42 196 280 82 33 96 128 256), losses := [] }

theorem u1924 : Upper (D 7) (R 7) [6,40,192,272,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 280 82 33 192 161 289), lower := (rows 7 42 196 280 82 33 192 128 256), losses := [] }

theorem u1925 : Upper (D 7) (R 7) [6,40,192,272,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 196 280 82 160 65 161 289), lower := (rows 7 42 196 280 82 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 85 24 16 245 65 193 321), good := (rows 485 40 484 316 508 160 485 160 256) }] }

theorem u1926 : Upper (D 7) (R 7) [6,40,192,272,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 280 82 160 96 129 257), lower := (rows 7 42 196 280 82 160 96 128 256), losses := [] }

theorem u1927 : Upper (D 7) (R 7) [6,40,192,272,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 196 280 112 33 65 130 386), lower := (rows 7 42 196 280 112 33 65 128 256), losses := [] }

theorem u1928 : Upper (D 7) (R 7) [6,40,192,272,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,7)], upper := (rows 7 42 196 280 112 33 66 129 385), lower := (rows 7 42 196 280 112 33 66 128 256), losses := [] }

theorem u1929 : Upper (D 7) (R 7) [6,40,192,272,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1930 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 280 112 33 192 131 259), lower := (rows 7 42 196 280 112 33 192 128 256), losses := [] }

theorem u1930 : Upper (D 7) (R 7) [6,40,192,272,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 176, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 7 42 196 328 145 33 66 176 304), lower := (rows 7 42 196 328 145 33 66 128 256), losses := [] }

theorem u1931 : Upper (D 7) (R 7) [6,40,192,320,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1932 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 328 145 33 80 162 290), lower := (rows 7 42 196 328 145 33 80 128 256), losses := [] }

theorem u1932 : Upper (D 7) (R 7) [6,40,192,320,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1932 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1933 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,7),(3,7),(4,5),(4,6)], upper := (rows 7 42 196 328 145 33 96 146 274), lower := (rows 7 42 196 328 145 33 96 128 256), losses := [] }

theorem u1933 : Upper (D 7) (R 7) [6,40,192,320,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 196 328 146 33 65 176 304), lower := (rows 7 42 196 328 146 33 65 128 256), losses := [] }

theorem u1934 : Upper (D 7) (R 7) [6,40,192,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 328 146 33 80 161 289), lower := (rows 7 42 196 328 146 33 80 128 256), losses := [] }

theorem u1935 : Upper (D 7) (R 7) [6,40,192,320,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1935 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1936 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 7 42 196 328 146 33 96 145 273), lower := (rows 7 42 196 328 146 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 98 128 256), good := (rows 70 106 196 328 214 96 96 128 256) },{ target := 1, region := (rows 1 0 20 8 16 33 99 128 256), good := (rows 101 104 196 328 212 97 96 128 256) }] }

theorem u1936 : Upper (D 7) (R 7) [6,40,192,320,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1937 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 69, targets := 32 },{ cop := 0, region := 176, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 196 328 146 48 65 161 289), lower := (rows 7 42 196 328 146 48 65 128 256), losses := [] }

theorem u1937 : Upper (D 7) (R 7) [6,40,192,320,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1937 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,0),(2,1),(4,5)], upper := (rows 7 42 196 328 146 48 96 129 257), lower := (rows 7 42 196 328 146 48 96 128 256), losses := [] }

theorem u1938 : Upper (D 7) (R 7) [6,40,192,320,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1938 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 65 }], pairs := [(2,0),(3,0),(4,0),(4,6)], upper := (rows 7 42 196 328 176 33 65 146 274), lower := (rows 7 42 196 328 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 72 50 32 64 131 259), good := (rows 406 442 204 332 176 432 460 128 256) }] }

theorem u1939 : Upper (D 7) (R 7) [6,40,192,320,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1940 : Route 9 := (fun mask => (mask,id))

def c1940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1940 : Upper (D 7) (R 7) [6,40,192,320,160,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,160,1,2] 13 (by decide) (choices 1) [1,16] r1940 c1940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u94
  · exact u95

def b1941 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 328 176 33 80 131 259), lower := (rows 7 42 196 328 176 33 80 128 256), losses := [] }

theorem u1941 : Upper (D 7) (R 7) [6,40,192,320,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1941 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1942 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 7 42 261 25 82 160 96 192 448), lower := (rows 7 42 261 25 82 160 96 128 256), losses := [] }

theorem u1942 : Upper (D 7) (R 7) [6,40,257,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1943 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(3,5),(4,0)], upper := (rows 7 42 261 25 82 160 192 224 352), lower := (rows 7 42 261 25 82 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 18 0 224 128 256), good := (rows 31 90 269 25 82 192 192 192 256) }] }

theorem u1943 : Upper (D 7) (R 7) [6,40,257,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 7 42 261 73 112 160 66 144 400), lower := (rows 7 42 261 73 112 160 66 128 256), losses := [] }

theorem u1944 : Upper (D 7) (R 7) [6,40,257,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 261 73 112 160 80 130 386), lower := (rows 7 42 261 73 112 160 80 128 256), losses := [] }

theorem u1945 : Upper (D 7) (R 7) [6,40,257,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1945 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 261 73 112 160 192 146 274), lower := (rows 7 42 261 73 112 160 192 128 256), losses := [] }

theorem u1946 : Upper (D 7) (R 7) [6,40,257,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1947 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 3, region := 420, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 261 73 146 160 80 224 352), lower := (rows 7 42 261 73 146 160 80 128 256), losses := [] }

theorem u1947 : Upper (D 7) (R 7) [6,40,257,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1947 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1948 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(3,1),(4,0)], upper := (rows 7 42 261 73 146 160 96 208 336), lower := (rows 7 42 261 73 146 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 176 242 144 272), good := (rows 77 104 269 73 496 224 96 224 256) },{ target := 7, region := (rows 17 2 20 25 16 32 98 0 272), good := (rows 79 106 269 73 351 96 96 0 256) }] }

theorem u1948 : Upper (D 7) (R 7) [6,40,257,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1949 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 7 42 261 73 208 160 66 176 304), lower := (rows 7 42 261 73 208 160 66 128 256), losses := [] }

theorem u1949 : Upper (D 7) (R 7) [6,40,257,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1950 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 261 73 208 160 80 162 290), lower := (rows 7 42 261 73 208 160 80 128 256), losses := [] }

theorem u1950 : Upper (D 7) (R 7) [6,40,257,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1950 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 5, region := 80, targets := 2 }], pairs := [(1,0),(3,1),(4,0),(4,1)], upper := (rows 7 42 261 73 208 160 96 146 274), lower := (rows 7 42 261 73 208 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 176 176 242 128 256), good := (rows 77 120 269 73 240 240 112 240 256) }] }

theorem u1951 : Upper (D 7) (R 7) [6,40,257,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1952 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 4, region := 136, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 42 261 200 112 33 66 144 400), lower := (rows 7 42 261 200 112 33 66 128 256), losses := [] }

theorem u1952 : Upper (D 7) (R 7) [6,40,257,192,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1953 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 261 200 112 33 80 130 386), lower := (rows 7 42 261 200 112 33 80 128 256), losses := [] }

theorem u1953 : Upper (D 7) (R 7) [6,40,257,192,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1953 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1954 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 261 200 112 33 192 146 274), lower := (rows 7 42 261 200 112 33 192 128 256), losses := [] }

theorem u1954 : Upper (D 7) (R 7) [6,40,257,192,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1955 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 42 276 73 112 160 65 130 386), lower := (rows 7 42 276 73 112 160 65 128 256), losses := [] }

theorem u1955 : Upper (D 7) (R 7) [6,40,272,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1),(4,0),(4,1),(4,7)], upper := (rows 7 42 276 73 112 160 66 129 385), lower := (rows 7 42 276 73 112 160 66 128 256), losses := [] }

theorem u1956 : Upper (D 7) (R 7) [6,40,272,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 276 73 112 160 192 131 259), lower := (rows 7 42 276 73 112 160 192 128 256), losses := [] }

theorem u1957 : Upper (D 7) (R 7) [6,40,272,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 42 276 73 145 160 66 224 352), lower := (rows 7 42 276 73 145 160 66 128 256), losses := [] }

theorem u1958 : Upper (D 7) (R 7) [6,40,272,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 162, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(2,0),(2,7),(3,1)], upper := (rows 7 42 276 73 145 160 96 194 322), lower := (rows 7 42 276 73 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 187 255 139 267), good := (rows 486 490 372 490 500 224 96 224 256) },{ target := 7, region := (rows 1 2 20 9 16 32 98 0 259), good := (rows 335 362 276 329 285 96 96 0 256) }] }

theorem u1959 : Upper (D 7) (R 7) [6,40,272,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 0, region := 72, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,0)], upper := (rows 7 42 276 73 146 160 65 224 352), lower := (rows 7 42 276 73 146 160 65 128 256), losses := [] }

theorem u1960 : Upper (D 7) (R 7) [6,40,272,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1961 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(0,5),(2,5),(3,1),(4,5)], upper := (rows 7 42 276 73 146 160 96 193 321), lower := (rows 7 42 276 73 146 160 96 128 256), losses := [{ target := 5, region := (rows 19 2 6 8 18 0 64 136 264), good := (rows 23 415 277 457 151 128 64 128 256) }] }

theorem u1961 : Upper (D 7) (R 7) [6,40,272,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1962 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 42 276 73 208 34 65 160 416), lower := (rows 7 42 276 73 208 34 65 128 256), losses := [] }

theorem u1962 : Upper (D 7) (R 7) [6,40,272,65,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1963 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 404, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 42 276 73 208 34 96 129 385), lower := (rows 7 42 276 73 208 34 96 128 256), losses := [] }

theorem u1963 : Upper (D 7) (R 7) [6,40,272,65,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1964 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 276 73 208 34 192 161 289), lower := (rows 7 42 276 73 208 34 192 128 256), losses := [] }

theorem u1964 : Upper (D 7) (R 7) [6,40,272,65,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 276 73 208 160 65 162 290), lower := (rows 7 42 276 73 208 160 65 128 256), losses := [] }

theorem u1965 : Upper (D 7) (R 7) [6,40,272,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1966 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 42 276 73 208 160 66 161 289), lower := (rows 7 42 276 73 208 160 66 128 256), losses := [] }

theorem u1966 : Upper (D 7) (R 7) [6,40,272,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1967 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(3,1),(4,0),(4,1)], upper := (rows 7 42 276 73 208 160 96 131 259), lower := (rows 7 42 276 73 208 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 176 176 246 128 256), good := (rows 77 120 372 73 240 240 112 240 256) }] }

theorem u1967 : Upper (D 7) (R 7) [6,40,272,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1968 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 42 276 74 81 160 65 160 416), lower := (rows 7 42 276 74 81 160 65 128 256), losses := [] }

theorem u1968 : Upper (D 7) (R 7) [6,40,272,66,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1969 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 276 74 81 160 96 129 385), lower := (rows 7 42 276 74 81 160 96 128 256), losses := [] }

theorem u1969 : Upper (D 7) (R 7) [6,40,272,66,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1970 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 276 74 81 160 192 161 289), lower := (rows 7 42 276 74 81 160 192 128 256), losses := [] }

theorem u1970 : Upper (D 7) (R 7) [6,40,272,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1971 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 160 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 42 276 74 145 160 65 224 352), lower := (rows 7 42 276 74 145 160 65 128 256), losses := [] }

theorem u1971 : Upper (D 7) (R 7) [6,40,272,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1972 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 276 74 145 160 96 193 321), lower := (rows 7 42 276 74 145 160 96 128 256), losses := [] }

theorem u1972 : Upper (D 7) (R 7) [6,40,272,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1973 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 276 74 208 33 65 160 416), lower := (rows 7 42 276 74 208 33 65 128 256), losses := [] }

theorem u1973 : Upper (D 7) (R 7) [6,40,272,66,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 276 74 208 33 96 129 385), lower := (rows 7 42 276 74 208 33 96 128 256), losses := [] }

theorem u1974 : Upper (D 7) (R 7) [6,40,272,66,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 276 74 208 33 192 161 289), lower := (rows 7 42 276 74 208 33 192 128 256), losses := [] }

theorem u1975 : Upper (D 7) (R 7) [6,40,272,66,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 428, targets := 2 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 7 42 276 200 81 33 66 160 416), lower := (rows 7 42 276 200 81 33 66 128 256), losses := [] }

theorem u1976 : Upper (D 7) (R 7) [6,40,272,192,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 112, targets := 130 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,7)], upper := (rows 7 42 276 200 81 33 96 130 386), lower := (rows 7 42 276 200 81 33 96 128 256), losses := [] }

theorem u1977 : Upper (D 7) (R 7) [6,40,272,192,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1978 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 276 200 81 33 192 162 290), lower := (rows 7 42 276 200 81 33 192 128 256), losses := [] }

theorem u1978 : Upper (D 7) (R 7) [6,40,272,192,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,6),(2,6),(3,1),(4,5)], upper := (rows 7 42 276 200 82 33 65 160 416), lower := (rows 7 42 276 200 82 33 65 128 256), losses := [] }

theorem u1979 : Upper (D 7) (R 7) [6,40,272,192,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P07
