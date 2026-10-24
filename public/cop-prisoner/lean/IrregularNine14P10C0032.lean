import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0011
import IrregularNine14P10C0012

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 73 400 312 376 440 312), lower := (rows 35 38 196 73 400 32 64 128 256), losses := [] }

theorem u1920 : Upper (D 10) (R 10) [34,36,192,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1920 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 88 176 297 329 393 265), lower := (rows 35 38 196 88 176 32 64 128 256), losses := [] }

theorem u1921 : Upper (D 10) (R 10) [34,36,192,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1921 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1922 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 88 273 424 488 424 424), lower := (rows 35 38 196 88 273 32 64 128 256), losses := [] }

theorem u1922 : Upper (D 10) (R 10) [34,36,192,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1922 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1923 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 88 304 425 457 393 393), lower := (rows 35 38 196 88 304 32 64 128 256), losses := [] }

theorem u1923 : Upper (D 10) (R 10) [34,36,192,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1923 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 88 400 297 361 425 297), lower := (rows 35 38 196 88 400 32 64 128 256), losses := [] }

theorem u1924 : Upper (D 10) (R 10) [34,36,192,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1924 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 104 273 440 472 408 408), lower := (rows 35 38 196 104 273 32 64 128 256), losses := [] }

theorem u1925 : Upper (D 10) (R 10) [34,36,192,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1925 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 104 280 433 465 401 401), lower := (rows 35 38 196 104 280 32 64 128 256), losses := [] }

theorem u1926 : Upper (D 10) (R 10) [34,36,192,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1926 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 104 400 313 345 409 281), lower := (rows 35 38 196 104 400 32 64 128 256), losses := [] }

theorem u1927 : Upper (D 10) (R 10) [34,36,192,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1927 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 265 304 248 216 216 472), lower := (rows 35 38 196 265 304 32 64 128 256), losses := [] }

theorem u1928 : Upper (D 10) (R 10) [34,36,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1928 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 265 336 184 248 184 440), lower := (rows 35 38 196 265 336 32 64 128 256), losses := [] }

theorem u1929 : Upper (D 10) (R 10) [34,36,192,257,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1929 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1930 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 296 336 185 217 153 409), lower := (rows 35 38 196 296 336 32 64 128 256), losses := [] }

theorem u1930 : Upper (D 10) (R 10) [34,36,192,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1930 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 328 400 57 121 185 313), lower := (rows 35 38 196 328 400 32 64 128 256), losses := [] }

theorem u1931 : Upper (D 10) (R 10) [34,36,192,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1931 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1932 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 44 76 176 432 464 400 400), lower := (rows 35 67 44 76 176 32 64 128 256), losses := [] }

theorem u1932 : Upper (D 10) (R 10) [34,65,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1932 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1933 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 44 76 400 432 496 432 432), lower := (rows 35 67 44 76 400 32 64 128 256), losses := [] }

theorem u1933 : Upper (D 10) (R 10) [34,65,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1933 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 88 148 416 480 416 416), lower := (rows 35 67 44 88 148 32 64 128 256), losses := [] }

theorem u1934 : Upper (D 10) (R 10) [34,65,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1934 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 88 176 420 452 388 388), lower := (rows 35 67 44 88 176 32 64 128 256), losses := [] }

theorem u1935 : Upper (D 10) (R 10) [34,65,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1935 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1936 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 88 400 420 484 420 420), lower := (rows 35 67 44 88 400 32 64 128 256), losses := [] }

theorem u1936 : Upper (D 10) (R 10) [34,65,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1936 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1937 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 104 148 432 464 400 400), lower := (rows 35 67 44 104 148 32 64 128 256), losses := [] }

theorem u1937 : Upper (D 10) (R 10) [34,65,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1937 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 104 400 436 468 404 404), lower := (rows 35 67 44 104 400 32 64 128 256), losses := [] }

theorem u1938 : Upper (D 10) (R 10) [34,65,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1938 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 140 112 432 464 400 400), lower := (rows 35 67 44 140 112 32 64 128 256), losses := [] }

theorem u1939 : Upper (D 10) (R 10) [34,65,40,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1939 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1940 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 140 208 304 368 432 304), lower := (rows 35 67 44 140 208 32 64 128 256), losses := [] }

theorem u1940 : Upper (D 10) (R 10) [34,65,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1940 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m1941_128 : Upper (D 10) (R 10) [34,65,40,132,288,128] 13 :=
  permutation_upper _ _ _ [34,65,40,132,288,64] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u711

def r1941 : Route 9 := (fun mask => (mask,id))

def c1941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1941 : Upper (D 10) (R 10) [34,65,40,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,288] 13 (by decide) (choices 1) [16,64,128,256] r1941 c1941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u710
  · exact u711
  · exact m1941_128
  · exact u712

def b1942 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 140 336 432 496 432 432), lower := (rows 35 67 44 140 336 32 64 128 256), losses := [] }

theorem u1942 : Upper (D 10) (R 10) [34,65,40,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1942 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1943 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 152 84 416 480 416 416), lower := (rows 35 67 44 152 84 32 64 128 256), losses := [] }

theorem u1943 : Upper (D 10) (R 10) [34,65,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1943 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 152 112 420 452 388 388), lower := (rows 35 67 44 152 112 32 64 128 256), losses := [] }

theorem u1944 : Upper (D 10) (R 10) [34,65,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1944 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 152 148 352 352 480 352), lower := (rows 35 67 44 152 148 32 64 128 256), losses := [] }

theorem u1945 : Upper (D 10) (R 10) [34,65,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1945 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 12, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 35 67 44 152 176 356 324 452 324), lower := (rows 35 67 44 152 176 32 64 128 256), losses := [] }

theorem u1946 : Upper (D 10) (R 10) [34,65,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1946 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1947 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 152 208 292 356 420 292), lower := (rows 35 67 44 152 208 32 64 128 256), losses := [] }

theorem u1947 : Upper (D 10) (R 10) [34,65,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1947 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1948 : Route 9 := (fun mask => (mask,id))

def c1948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1948 : Upper (D 10) (R 10) [34,65,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,260] 13 (by decide) (choices 1) [64,128,256] r1948 c1948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u713
  · exact u714
  · exact u715

def r1949 : Route 9 := (fun mask => (mask,id))

def c1949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1949 : Upper (D 10) (R 10) [34,65,40,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,288] 13 (by decide) (choices 1) [4,64,128,256] r1949 c1949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u716
  · exact u717
  · exact u718
  · exact u719

def b1950 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 152 336 420 484 420 420), lower := (rows 35 67 44 152 336 32 64 128 256), losses := [] }

theorem u1950 : Upper (D 10) (R 10) [34,65,40,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1950 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 152 400 356 356 484 356), lower := (rows 35 67 44 152 400 32 64 128 256), losses := [] }

theorem u1951 : Upper (D 10) (R 10) [34,65,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1951 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1952 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 4, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 35 67 44 168 148 368 336 464 336), lower := (rows 35 67 44 168 148 32 64 128 256), losses := [] }

theorem u1952 : Upper (D 10) (R 10) [34,65,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1952 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1953 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 67 44 168 276 496 464 464 464), lower := (rows 35 67 44 168 276 32 64 128 256), losses := [] }

theorem u1953 : Upper (D 10) (R 10) [34,65,40,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1953 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1954 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 35 67 44 168 400 372 340 468 340), lower := (rows 35 67 44 168 400 32 64 128 256), losses := [] }

theorem u1954 : Upper (D 10) (R 10) [34,65,40,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1954 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1955 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 200 148 304 368 432 304), lower := (rows 35 67 44 200 148 32 64 128 256), losses := [] }

theorem u1955 : Upper (D 10) (R 10) [34,65,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1955 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 200 176 308 340 404 276), lower := (rows 35 67 44 200 176 32 64 128 256), losses := [] }

theorem u1956 : Upper (D 10) (R 10) [34,65,40,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1956 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 200 276 432 496 432 432), lower := (rows 35 67 44 200 276 32 64 128 256), losses := [] }

theorem u1957 : Upper (D 10) (R 10) [34,65,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1957 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 200 304 436 468 404 404), lower := (rows 35 67 44 200 304 32 64 128 256), losses := [] }

theorem u1958 : Upper (D 10) (R 10) [34,65,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1958 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 67 44 200 400 308 372 436 308), lower := (rows 35 67 44 200 400 32 64 128 256), losses := [] }

theorem u1959 : Upper (D 10) (R 10) [34,65,40,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1959 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 392 84 432 496 432 432), lower := (rows 35 67 44 392 84 32 64 128 256), losses := [] }

theorem u1960 : Upper (D 10) (R 10) [34,65,40,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1960 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1961 : PairBound 9 := { available := 404, camps := [{ cop := 4, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 392 112 436 468 404 404), lower := (rows 35 67 44 392 112 32 64 128 256), losses := [] }

theorem u1961 : Upper (D 10) (R 10) [34,65,40,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1961 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1962 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 392 148 368 368 496 368), lower := (rows 35 67 44 392 148 32 64 128 256), losses := [] }

theorem u1962 : Upper (D 10) (R 10) [34,65,40,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1962 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1963 : Route 9 := (fun mask => (mask,id))

def c1963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1963 : Upper (D 10) (R 10) [34,65,40,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,160] 13 (by decide) (choices 1) [4,16,64,256] r1963 c1963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u720
  · exact u721
  · exact u722
  · exact u723

def b1964 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 392 208 308 372 436 308), lower := (rows 35 67 44 392 208 32 64 128 256), losses := [] }

theorem u1964 : Upper (D 10) (R 10) [34,65,40,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1964 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 67 44 392 400 116 116 244 372), lower := (rows 35 67 44 392 400 32 64 128 256), losses := [] }

theorem u1965 : Upper (D 10) (R 10) [34,65,40,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1965 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1966 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 76 140 176 304 368 432 304), lower := (rows 35 67 76 140 176 32 64 128 256), losses := [] }

theorem u1966 : Upper (D 10) (R 10) [34,65,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1966 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1967 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 76 140 304 432 496 432 432), lower := (rows 35 67 76 140 304 32 64 128 256), losses := [] }

theorem u1967 : Upper (D 10) (R 10) [34,65,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1967 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1968 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 76 140 400 304 368 432 304), lower := (rows 35 67 76 140 400 32 64 128 256), losses := [] }

theorem u1968 : Upper (D 10) (R 10) [34,65,72,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1968 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1969 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 152 276 416 480 416 416), lower := (rows 35 67 76 152 276 32 64 128 256), losses := [] }

theorem u1969 : Upper (D 10) (R 10) [34,65,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1969 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1970 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 152 304 420 484 420 420), lower := (rows 35 67 76 152 304 32 64 128 256), losses := [] }

theorem u1970 : Upper (D 10) (R 10) [34,65,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1970 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1971 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 168 148 304 368 432 304), lower := (rows 35 67 76 168 148 32 64 128 256), losses := [] }

theorem u1971 : Upper (D 10) (R 10) [34,65,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1971 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1972 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 168 276 432 496 432 432), lower := (rows 35 67 76 168 276 32 64 128 256), losses := [] }

theorem u1972 : Upper (D 10) (R 10) [34,65,72,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1972 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1973 : PairBound 9 := { available := 404, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 168 304 436 468 404 404), lower := (rows 35 67 76 168 304 32 64 128 256), losses := [] }

theorem u1973 : Upper (D 10) (R 10) [34,65,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1973 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 168 400 308 372 436 308), lower := (rows 35 67 76 168 400 32 64 128 256), losses := [] }

theorem u1974 : Upper (D 10) (R 10) [34,65,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1974 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 392 148 304 368 432 304), lower := (rows 35 67 76 392 148 32 64 128 256), losses := [] }

theorem u1975 : Upper (D 10) (R 10) [34,65,72,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1975 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 67 76 392 176 308 372 436 308), lower := (rows 35 67 76 392 176 32 64 128 256), losses := [] }

theorem u1976 : Upper (D 10) (R 10) [34,65,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1976 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 140 176 312 344 408 280), lower := (rows 35 67 100 140 176 32 64 128 256), losses := [] }

theorem u1977 : Upper (D 10) (R 10) [34,65,96,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1977 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1978 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 140 280 432 496 432 432), lower := (rows 35 67 100 140 280 32 64 128 256), losses := [] }

theorem u1978 : Upper (D 10) (R 10) [34,65,96,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1978 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 100 140 304 440 472 408 408), lower := (rows 35 67 100 140 304 32 64 128 256), losses := [] }

theorem u1979 : Upper (D 10) (R 10) [34,65,96,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1979 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P10
