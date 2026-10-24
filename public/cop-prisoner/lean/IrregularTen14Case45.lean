import IrregularTen14Base

namespace Delivery.IrregularTen14.Case45
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 19 14 44 752 736 736 736 992 736), lower := (rows 273 19 14 44 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,17,10,36] 13 :=
  bound_sound D R [272,17,10,36] 13 bound_2
    ((Boolean.boundCheck_true D R [272,17,10,36] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 19 14 104 756 740 740 740 996 740), lower := (rows 273 19 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,17,10,96] 13 :=
  bound_sound D R [272,17,10,96] 13 bound_3
    ((Boolean.boundCheck_true D R [272,17,10,96] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 273 19 14 524 240 224 224 224 480 736), lower := (rows 273 19 14 524 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 6 14 0 1023 1023 1023 1023 1023), good := (rows 993 1007 1006 1004 992 992 992 992 992 992) }] }

theorem upper_4 : Upper D R [272,17,10,516] 13 :=
  bound_sound D R [272,17,10,516] 13 bound_4
    ((Boolean.boundCheck_true D R [272,17,10,516] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 19 14 552 244 228 228 228 484 740), lower := (rows 273 19 14 552 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [272,17,10,544] 13 :=
  bound_sound D R [272,17,10,544] 13 bound_5
    ((Boolean.boundCheck_true D R [272,17,10,544] 13 bound_5).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,17,10] 13 := by
  apply routed_branch D R [272,17,10] 13 (by decide) (choices 2) [36,96,516,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,17,10] (choices 2) [36,96,516,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5

def bound_6 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 19 38 748 764 748 748 748 1004 748), lower := (rows 273 19 38 8 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [272,17,34] 13 :=
  bound_sound D R [272,17,34] 13 bound_6
    ((Boolean.boundCheck_true D R [272,17,34] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 19 44 750 758 742 742 742 998 742), lower := (rows 273 19 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [272,17,40] 13 :=
  bound_sound D R [272,17,40] 13 bound_7
    ((Boolean.boundCheck_true D R [272,17,40] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 224 144 240 0 0 0 0 0 0), upper := (rows 273 19 100 750 766 750 750 750 1006 750), lower := (rows 273 19 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [272,17,96] 13 :=
  bound_sound D R [272,17,96] 13 bound_8
    ((Boolean.boundCheck_true D R [272,17,96] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 19 518 44 248 232 232 232 488 744), lower := (rows 273 19 518 44 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [272,17,514,36] 13 :=
  bound_sound D R [272,17,514,36] 13 bound_10
    ((Boolean.boundCheck_true D R [272,17,514,36] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 19 518 104 252 236 236 236 492 748), lower := (rows 273 19 518 104 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [272,17,514,96] 13 :=
  bound_sound D R [272,17,514,96] 13 bound_11
    ((Boolean.boundCheck_true D R [272,17,514,96] 13 bound_11).mp (by decide +kernel))

def route_9 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [272,17,514] 13 := by
  apply routed_branch D R [272,17,514] 13 (by decide) (choices 2) [36,96] route_9
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,17,514] (choices 2) [36,96] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_11

def bound_13 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 273 19 524 14 240 224 224 224 480 736), lower := (rows 273 19 524 14 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 14 10 0 1023 1023 1023 1023 1023), good := (rows 993 1007 1004 1006 992 992 992 992 992 992) }] }

theorem upper_13 : Upper D R [272,17,520,6] 13 :=
  bound_sound D R [272,17,520,6] 13 bound_13
    ((Boolean.boundCheck_true D R [272,17,520,6] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 19 524 42 244 228 228 228 484 740), lower := (rows 273 19 524 42 16 32 64 128 256 512), losses := [] }

theorem upper_14 : Upper D R [272,17,520,34] 13 :=
  bound_sound D R [272,17,520,34] 13 bound_14
    ((Boolean.boundCheck_true D R [272,17,520,34] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 19 524 44 242 226 226 226 482 738), lower := (rows 273 19 524 44 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [272,17,520,36] 13 :=
  bound_sound D R [272,17,520,36] 13 bound_15
    ((Boolean.boundCheck_true D R [272,17,520,36] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 19 524 104 246 230 230 230 486 742), lower := (rows 273 19 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [272,17,520,96] 13 :=
  bound_sound D R [272,17,520,96] 13 bound_16
    ((Boolean.boundCheck_true D R [272,17,520,96] 13 bound_16).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_12 : Upper D R [272,17,520] 13 := by
  apply routed_branch D R [272,17,520] 13 (by decide) (choices 2) [6,34,36,96] route_12
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,17,520] (choices 2) [6,34,36,96] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_15
  · exact upper_16

def bound_17 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 19 548 238 254 238 238 238 494 750), lower := (rows 273 19 548 8 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [272,17,544] 13 :=
  bound_sound D R [272,17,544] 13 bound_17
    ((Boolean.boundCheck_true D R [272,17,544] 13 bound_17).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,17] 13 := by
  apply routed_branch D R [272,17] 13 (by decide) (choices 2) [10,34,40,96,514,520,544] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,17] (choices 2) [10,34,40,96,514,520,544] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_6
  · exact upper_7
  · exact upper_8
  · exact upper_9
  · exact upper_12
  · exact upper_17

theorem upper : Upper D R [272,17] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case45
