import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15780 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 42 84 440 472 408 408), lower := (rows 193 35 37 42 84 32 64 128 256), losses := [] }

theorem u15780 : Upper (D 8) (R 8) [192,33,33,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15781 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 42 88 436 468 404 404), lower := (rows 193 35 37 42 88 32 64 128 256), losses := [] }

theorem u15781 : Upper (D 8) (R 8) [192,33,33,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15782 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 42 276 248 216 216 472), lower := (rows 193 35 37 42 276 32 64 128 256), losses := [] }

theorem u15782 : Upper (D 8) (R 8) [192,33,33,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15783 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 42 280 244 212 212 468), lower := (rows 193 35 37 42 280 32 64 128 256), losses := [] }

theorem u15783 : Upper (D 8) (R 8) [192,33,33,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15784 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 42 336 188 220 156 412), lower := (rows 193 35 37 42 336 32 64 128 256), losses := [] }

theorem u15784 : Upper (D 8) (R 8) [192,33,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15785 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 56 82 428 460 396 396), lower := (rows 193 35 37 56 82 32 64 128 256), losses := [] }

theorem u15785 : Upper (D 8) (R 8) [192,33,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15786 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 56 274 236 204 204 460), lower := (rows 193 35 37 56 274 32 64 128 256), losses := [] }

theorem u15786 : Upper (D 8) (R 8) [192,33,33,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15787 : PairBound 9 := { available := 198, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 56 280 230 198 198 454), lower := (rows 193 35 37 56 280 32 64 128 256), losses := [] }

theorem u15787 : Upper (D 8) (R 8) [192,33,33,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15788 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 56 336 174 206 142 398), lower := (rows 193 35 37 56 336 32 64 128 256), losses := [] }

theorem u15788 : Upper (D 8) (R 8) [192,33,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15789 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 74 148 312 376 440 312), lower := (rows 193 35 37 74 148 32 64 128 256), losses := [] }

theorem u15789 : Upper (D 8) (R 8) [192,33,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15790 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 74 152 308 372 436 308), lower := (rows 193 35 37 74 152 32 64 128 256), losses := [] }

theorem u15790 : Upper (D 8) (R 8) [192,33,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15791 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 74 176 316 348 412 284), lower := (rows 193 35 37 74 176 32 64 128 256), losses := [] }

theorem u15791 : Upper (D 8) (R 8) [192,33,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15792 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 74 276 184 248 184 440), lower := (rows 193 35 37 74 276 32 64 128 256), losses := [] }

theorem u15792 : Upper (D 8) (R 8) [192,33,33,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15793 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 74 280 180 244 180 436), lower := (rows 193 35 37 74 280 32 64 128 256), losses := [] }

theorem u15793 : Upper (D 8) (R 8) [192,33,33,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15794 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 74 304 188 220 156 412), lower := (rows 193 35 37 74 304 32 64 128 256), losses := [] }

theorem u15794 : Upper (D 8) (R 8) [192,33,33,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15795 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 74 400 60 124 188 316), lower := (rows 193 35 37 74 400 32 64 128 256), losses := [] }

theorem u15795 : Upper (D 8) (R 8) [192,33,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15796 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 88 176 302 334 398 270), lower := (rows 193 35 37 88 176 32 64 128 256), losses := [] }

theorem u15796 : Upper (D 8) (R 8) [192,33,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15797 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 88 274 172 236 172 428), lower := (rows 193 35 37 88 274 32 64 128 256), losses := [] }

theorem u15797 : Upper (D 8) (R 8) [192,33,33,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15798 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 88 304 174 206 142 398), lower := (rows 193 35 37 88 304 32 64 128 256), losses := [] }

theorem u15798 : Upper (D 8) (R 8) [192,33,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15799 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 88 400 46 110 174 302), lower := (rows 193 35 37 88 400 32 64 128 256), losses := [] }

theorem u15799 : Upper (D 8) (R 8) [192,33,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15800 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 104 274 188 220 156 412), lower := (rows 193 35 37 104 274 32 64 128 256), losses := [] }

theorem u15800 : Upper (D 8) (R 8) [192,33,33,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15801 : PairBound 9 := { available := 150, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 104 280 182 214 150 406), lower := (rows 193 35 37 104 280 32 64 128 256), losses := [] }

theorem u15801 : Upper (D 8) (R 8) [192,33,33,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15802 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 193 35 37 104 400 62 94 158 286), lower := (rows 193 35 37 104 400 32 64 128 256), losses := [] }

theorem u15802 : Upper (D 8) (R 8) [192,33,33,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15803 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 44 88 433 465 401 401), lower := (rows 193 35 38 44 88 32 64 128 256), losses := [] }

theorem u15803 : Upper (D 8) (R 8) [192,33,34,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15804 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 44 273 248 216 216 472), lower := (rows 193 35 38 44 273 32 64 128 256), losses := [] }

theorem u15804 : Upper (D 8) (R 8) [192,33,34,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15805 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 44 280 241 209 209 465), lower := (rows 193 35 38 44 280 32 64 128 256), losses := [] }

theorem u15805 : Upper (D 8) (R 8) [192,33,34,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15806 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 44 336 185 217 153 409), lower := (rows 193 35 38 44 336 32 64 128 256), losses := [] }

theorem u15806 : Upper (D 8) (R 8) [192,33,34,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15807 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 56 84 425 457 393 393), lower := (rows 193 35 38 56 84 32 64 128 256), losses := [] }

theorem u15807 : Upper (D 8) (R 8) [192,33,34,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15808 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 56 273 236 204 204 460), lower := (rows 193 35 38 56 273 32 64 128 256), losses := [] }

theorem u15808 : Upper (D 8) (R 8) [192,33,34,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15809 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 56 276 233 201 201 457), lower := (rows 193 35 38 56 276 32 64 128 256), losses := [] }

theorem u15809 : Upper (D 8) (R 8) [192,33,34,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15810 : PairBound 9 := { available := 197, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 56 280 229 197 197 453), lower := (rows 193 35 38 56 280 32 64 128 256), losses := [] }

theorem u15810 : Upper (D 8) (R 8) [192,33,34,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15811 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 56 336 173 205 141 397), lower := (rows 193 35 38 56 336 32 64 128 256), losses := [] }

theorem u15811 : Upper (D 8) (R 8) [192,33,34,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15812 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 76 152 305 369 433 305), lower := (rows 193 35 38 76 152 32 64 128 256), losses := [] }

theorem u15812 : Upper (D 8) (R 8) [192,33,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15813 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 76 176 313 345 409 281), lower := (rows 193 35 38 76 176 32 64 128 256), losses := [] }

theorem u15813 : Upper (D 8) (R 8) [192,33,34,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15814 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 76 273 184 248 184 440), lower := (rows 193 35 38 76 273 32 64 128 256), losses := [] }

theorem u15814 : Upper (D 8) (R 8) [192,33,34,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15815 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 76 280 177 241 177 433), lower := (rows 193 35 38 76 280 32 64 128 256), losses := [] }

theorem u15815 : Upper (D 8) (R 8) [192,33,34,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15816 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 76 304 185 217 153 409), lower := (rows 193 35 38 76 304 32 64 128 256), losses := [] }

theorem u15816 : Upper (D 8) (R 8) [192,33,34,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15817 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 76 400 57 121 185 313), lower := (rows 193 35 38 76 400 32 64 128 256), losses := [] }

theorem u15817 : Upper (D 8) (R 8) [192,33,34,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15818 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 88 176 301 333 397 269), lower := (rows 193 35 38 88 176 32 64 128 256), losses := [] }

theorem u15818 : Upper (D 8) (R 8) [192,33,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15819 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 88 273 172 236 172 428), lower := (rows 193 35 38 88 273 32 64 128 256), losses := [] }

theorem u15819 : Upper (D 8) (R 8) [192,33,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15820 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 88 276 169 233 169 425), lower := (rows 193 35 38 88 276 32 64 128 256), losses := [] }

theorem u15820 : Upper (D 8) (R 8) [192,33,34,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15821 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 88 304 173 205 141 397), lower := (rows 193 35 38 88 304 32 64 128 256), losses := [] }

theorem u15821 : Upper (D 8) (R 8) [192,33,34,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15822 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 88 400 45 109 173 301), lower := (rows 193 35 38 88 400 32 64 128 256), losses := [] }

theorem u15822 : Upper (D 8) (R 8) [192,33,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15823 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 104 273 188 220 156 412), lower := (rows 193 35 38 104 273 32 64 128 256), losses := [] }

theorem u15823 : Upper (D 8) (R 8) [192,33,34,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15824 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 104 276 185 217 153 409), lower := (rows 193 35 38 104 276 32 64 128 256), losses := [] }

theorem u15824 : Upper (D 8) (R 8) [192,33,34,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15825 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 104 280 181 213 149 405), lower := (rows 193 35 38 104 280 32 64 128 256), losses := [] }

theorem u15825 : Upper (D 8) (R 8) [192,33,34,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15826 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 38 104 400 61 93 157 285), lower := (rows 193 35 38 104 400 32 64 128 256), losses := [] }

theorem u15826 : Upper (D 8) (R 8) [192,33,34,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15827 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 44 82 433 465 401 401), lower := (rows 193 35 44 44 82 32 64 128 256), losses := [] }

theorem u15827 : Upper (D 8) (R 8) [192,33,40,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15828 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 44 273 242 210 210 466), lower := (rows 193 35 44 44 273 32 64 128 256), losses := [] }

theorem u15828 : Upper (D 8) (R 8) [192,33,40,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15829 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 44 274 241 209 209 465), lower := (rows 193 35 44 44 274 32 64 128 256), losses := [] }

theorem u15829 : Upper (D 8) (R 8) [192,33,40,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15830 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 44 336 179 211 147 403), lower := (rows 193 35 44 44 336 32 64 128 256), losses := [] }

theorem u15830 : Upper (D 8) (R 8) [192,33,40,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15831 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 56 82 421 453 389 389), lower := (rows 193 35 44 56 82 32 64 128 256), losses := [] }

theorem u15831 : Upper (D 8) (R 8) [192,33,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15832 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 56 84 419 451 387 387), lower := (rows 193 35 44 56 84 32 64 128 256), losses := [] }

theorem u15832 : Upper (D 8) (R 8) [192,33,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15833 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 56 273 230 198 198 454), lower := (rows 193 35 44 56 273 32 64 128 256), losses := [] }

theorem u15833 : Upper (D 8) (R 8) [192,33,40,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15834 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 56 274 229 197 197 453), lower := (rows 193 35 44 56 274 32 64 128 256), losses := [] }

theorem u15834 : Upper (D 8) (R 8) [192,33,40,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15835 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 56 276 227 195 195 451), lower := (rows 193 35 44 56 276 32 64 128 256), losses := [] }

theorem u15835 : Upper (D 8) (R 8) [192,33,40,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15836 : PairBound 9 := { available := 135, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 35 44 56 336 167 199 135 391), lower := (rows 193 35 44 56 336 32 64 128 256), losses := [] }

theorem u15836 : Upper (D 8) (R 8) [192,33,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15837 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 73 146 308 372 436 308), lower := (rows 193 35 44 73 146 32 64 128 256), losses := [] }

theorem u15837 : Upper (D 8) (R 8) [192,33,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15838 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 73 148 306 370 434 306), lower := (rows 193 35 44 73 148 32 64 128 256), losses := [] }

theorem u15838 : Upper (D 8) (R 8) [192,33,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15839 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 35 44 73 176 310 342 406 278), lower := (rows 193 35 44 73 176 32 64 128 256), losses := [] }

theorem u15839 : Upper (D 8) (R 8) [192,33,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15839
end Delivery.IrregularNine14.P08
