import IrregularTen14Base

namespace Delivery.IrregularTen14.Case46
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 22 7 104 760 744 744 744 1000 744), lower := (rows 273 22 7 104 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [272,20,3,96] 13 :=
  bound_sound D R [272,20,3,96] 13 bound_2
    ((Boolean.boundCheck_true D R [272,20,3,96] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 7 552 248 232 232 232 488 744), lower := (rows 273 22 7 552 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [272,20,3,544] 13 :=
  bound_sound D R [272,20,3,544] 13 bound_3
    ((Boolean.boundCheck_true D R [272,20,3,544] 13 bound_3).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [272,20,3] 13 := by
  apply routed_branch D R [272,20,3] 13 (by decide) (choices 2) [96,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,20,3] (choices 2) [96,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_2
  · exact upper_3

def bound_5 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 13 42 752 736 736 736 992 736), lower := (rows 273 22 13 42 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [272,20,9,34] 13 :=
  bound_sound D R [272,20,9,34] 13 bound_5
    ((Boolean.boundCheck_true D R [272,20,9,34] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 22 13 104 754 738 738 738 994 738), lower := (rows 273 22 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [272,20,9,96] 13 :=
  bound_sound D R [272,20,9,96] 13 bound_6
    ((Boolean.boundCheck_true D R [272,20,9,96] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 224 240 224 0 0 0 0 0 0), upper := (rows 273 22 13 522 240 224 224 224 480 736), lower := (rows 273 22 13 522 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 10 0 1023 1023 1023 1023 1023), good := (rows 993 1006 1005 1002 992 992 992 992 992 992) }] }

theorem upper_7 : Upper D R [272,20,9,514] 13 :=
  bound_sound D R [272,20,9,514] 13 bound_7
    ((Boolean.boundCheck_true D R [272,20,9,514] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 13 552 242 226 226 226 482 738), lower := (rows 273 22 13 552 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [272,20,9,544] 13 :=
  bound_sound D R [272,20,9,544] 13 bound_8
    ((Boolean.boundCheck_true D R [272,20,9,544] 13 bound_8).mp (by decide +kernel))

def route_4 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_4 : Upper D R [272,20,9] 13 := by
  apply routed_branch D R [272,20,9] 13 (by decide) (choices 2) [34,96,514,544] route_4
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,20,9] (choices 2) [34,96,514,544] route_4).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_8

def bound_10 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 14 41 752 736 736 736 992 736), lower := (rows 273 22 14 41 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [272,20,10,33] 13 :=
  bound_sound D R [272,20,10,33] 13 bound_10
    ((Boolean.boundCheck_true D R [272,20,10,33] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 22 14 104 753 737 737 737 993 737), lower := (rows 273 22 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [272,20,10,96] 13 :=
  bound_sound D R [272,20,10,96] 13 bound_11
    ((Boolean.boundCheck_true D R [272,20,10,96] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 224 240 224 0 0 0 0 0 0), upper := (rows 273 22 14 521 240 224 224 224 480 736), lower := (rows 273 22 14 521 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 1023 1023), good := (rows 1001 998 1006 1001 992 992 992 992 992 992) }] }

theorem upper_12 : Upper D R [272,20,10,513] 13 :=
  bound_sound D R [272,20,10,513] 13 bound_12
    ((Boolean.boundCheck_true D R [272,20,10,513] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 14 552 241 225 225 225 481 737), lower := (rows 273 22 14 552 16 32 64 128 256 512), losses := [] }

theorem upper_13 : Upper D R [272,20,10,544] 13 :=
  bound_sound D R [272,20,10,544] 13 bound_13
    ((Boolean.boundCheck_true D R [272,20,10,544] 13 bound_13).mp (by decide +kernel))

def route_9 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [272,20,10] 13 := by
  apply routed_branch D R [272,20,10] 13 (by decide) (choices 2) [33,96,513,544] route_9
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,20,10] (choices 2) [33,96,513,544] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12
  · exact upper_13

def bound_14 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 22 37 746 762 746 746 746 1002 746), lower := (rows 273 22 37 8 16 32 64 128 256 512), losses := [] }

theorem upper_14 : Upper D R [272,20,33] 13 :=
  bound_sound D R [272,20,33] 13 bound_14
    ((Boolean.boundCheck_true D R [272,20,33] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 22 38 745 761 745 745 745 1001 745), lower := (rows 273 22 38 8 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [272,20,34] 13 :=
  bound_sound D R [272,20,34] 13 bound_15
    ((Boolean.boundCheck_true D R [272,20,34] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 22 44 747 755 739 739 739 995 739), lower := (rows 273 22 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [272,20,40] 13 :=
  bound_sound D R [272,20,40] 13 bound_16
    ((Boolean.boundCheck_true D R [272,20,40] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 224 224 144 240 0 0 0 0 0 0), upper := (rows 273 22 100 747 763 747 747 747 1003 747), lower := (rows 273 22 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [272,20,96] 13 :=
  bound_sound D R [272,20,96] 13 bound_17
    ((Boolean.boundCheck_true D R [272,20,96] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 517 42 248 232 232 232 488 744), lower := (rows 273 22 517 42 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [272,20,513,34] 13 :=
  bound_sound D R [272,20,513,34] 13 bound_19
    ((Boolean.boundCheck_true D R [272,20,513,34] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 22 517 104 250 234 234 234 490 746), lower := (rows 273 22 517 104 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [272,20,513,96] 13 :=
  bound_sound D R [272,20,513,96] 13 bound_20
    ((Boolean.boundCheck_true D R [272,20,513,96] 13 bound_20).mp (by decide +kernel))

def route_18 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_18 : Upper D R [272,20,513] 13 := by
  apply routed_branch D R [272,20,513] 13 (by decide) (choices 2) [34,96] route_18
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,20,513] (choices 2) [34,96] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_19
  · exact upper_20

def bound_22 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 518 41 248 232 232 232 488 744), lower := (rows 273 22 518 41 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [272,20,514,33] 13 :=
  bound_sound D R [272,20,514,33] 13 bound_22
    ((Boolean.boundCheck_true D R [272,20,514,33] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 22 518 104 249 233 233 233 489 745), lower := (rows 273 22 518 104 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [272,20,514,96] 13 :=
  bound_sound D R [272,20,514,96] 13 bound_23
    ((Boolean.boundCheck_true D R [272,20,514,96] 13 bound_23).mp (by decide +kernel))

def route_21 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_21 : Upper D R [272,20,514] 13 := by
  apply routed_branch D R [272,20,514] 13 (by decide) (choices 2) [33,96] route_21
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,20,514] (choices 2) [33,96] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_22
  · exact upper_23

def bound_25 : Bound 10 := { allowed := (rows 224 224 224 240 0 0 0 0 0 0), upper := (rows 273 22 524 11 240 224 224 224 480 736), lower := (rows 273 22 524 11 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 1023 1023), good := (rows 993 998 1004 1007 992 992 992 992 992 992) }] }

theorem upper_25 : Upper D R [272,20,520,3] 13 :=
  bound_sound D R [272,20,520,3] 13 bound_25
    ((Boolean.boundCheck_true D R [272,20,520,3] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 524 41 242 226 226 226 482 738), lower := (rows 273 22 524 41 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [272,20,520,33] 13 :=
  bound_sound D R [272,20,520,33] 13 bound_26
    ((Boolean.boundCheck_true D R [272,20,520,33] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 273 22 524 42 241 225 225 225 481 737), lower := (rows 273 22 524 42 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [272,20,520,34] 13 :=
  bound_sound D R [272,20,520,34] 13 bound_27
    ((Boolean.boundCheck_true D R [272,20,520,34] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 273 22 524 104 243 227 227 227 483 739), lower := (rows 273 22 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [272,20,520,96] 13 :=
  bound_sound D R [272,20,520,96] 13 bound_28
    ((Boolean.boundCheck_true D R [272,20,520,96] 13 bound_28).mp (by decide +kernel))

def route_24 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_24 : Upper D R [272,20,520] 13 := by
  apply routed_branch D R [272,20,520] 13 (by decide) (choices 2) [3,33,34,96] route_24
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,20,520] (choices 2) [3,33,34,96] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28

def bound_29 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 273 22 548 235 251 235 235 235 491 747), lower := (rows 273 22 548 8 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [272,20,544] 13 :=
  bound_sound D R [272,20,544] 13 bound_29
    ((Boolean.boundCheck_true D R [272,20,544] 13 bound_29).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [272,20] 13 := by
  apply routed_branch D R [272,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,513,514,520,544] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [272,20] (choices 2) [3,9,10,33,34,40,96,513,514,520,544] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_4
  · exact upper_9
  · exact upper_14
  · exact upper_15
  · exact upper_16
  · exact upper_17
  · exact upper_18
  · exact upper_21
  · exact upper_24
  · exact upper_29

theorem upper : Upper D R [272,20] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case46
