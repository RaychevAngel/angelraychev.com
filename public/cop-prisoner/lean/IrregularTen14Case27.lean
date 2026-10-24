import IrregularTen14Base

namespace Delivery.IrregularTen14.Case27
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_0 : Bound 10 := { allowed := (rows 192 176 240 240 0 0 0 0 0 0), upper := (rows 49 70 1023 1019 1019 1019 1019 1019 1019 1019), lower := (rows 49 70 4 8 16 32 64 128 256 512), losses := [] }

theorem upper_0 : Upper D R [48,68] 13 :=
  bound_sound D R [48,68] 13 bound_0
    ((Boolean.boundCheck_true D R [48,68] 13 bound_0).mp (by decide +kernel))

theorem upper : Upper D R [48,68] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case27
