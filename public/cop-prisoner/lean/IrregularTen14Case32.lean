import IrregularTen14Base

namespace Delivery.IrregularTen14.Case32
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_0 : Bound 10 := { allowed := (rows 192 224 240 240 0 0 0 0 0 0), upper := (rows 49 274 751 751 767 751 751 751 1007 751), lower := (rows 49 274 4 8 16 32 64 128 256 512), losses := [] }

theorem upper_0 : Upper D R [48,272] 13 :=
  bound_sound D R [48,272] 13 bound_0
    ((Boolean.boundCheck_true D R [48,272] 13 bound_0).mp (by decide +kernel))

theorem upper : Upper D R [48,272] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case32
