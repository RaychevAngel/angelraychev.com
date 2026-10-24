import IrregularTen14Base

namespace Delivery.IrregularTen14.Case11
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 19 22 13 104 1008 992 992 992 992 992), lower := (rows 19 22 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,20,9,96] 13 :=
  bound_sound D R [18,20,9,96] 13 bound_2
    ((Boolean.boundCheck_true D R [18,20,9,96] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 22 13 296 752 736 736 736 992 736), lower := (rows 19 22 13 296 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [18,20,9,288] 13 :=
  bound_sound D R [18,20,9,288] 13 bound_3
    ((Boolean.boundCheck_true D R [18,20,9,288] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 19 22 13 776 240 224 224 224 480 736), lower := (rows 19 22 13 776 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 1023 0 1023 1023 1023 1023 1023), good := (rows 1007 1006 1005 1000 1000 1000 1000 1000 1000 1000) }] }

theorem upper_4 : Upper D R [18,20,9,768] 13 :=
  bound_sound D R [18,20,9,768] 13 bound_4
    ((Boolean.boundCheck_true D R [18,20,9,768] 13 bound_4).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [18,20,9] 13 := by
  apply routed_branch D R [18,20,9] 13 (by decide) (choices 2) [96,288,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,20,9] (choices 2) [96,288,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4

def bound_5 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 19 22 37 1000 1016 1000 1000 1000 1000 1000), lower := (rows 19 22 37 8 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [18,20,33] 13 :=
  bound_sound D R [18,20,33] 13 bound_5
    ((Boolean.boundCheck_true D R [18,20,33] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 19 22 44 1001 1009 993 993 993 993 993), lower := (rows 19 22 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [18,20,40] 13 :=
  bound_sound D R [18,20,40] 13 bound_6
    ((Boolean.boundCheck_true D R [18,20,40] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 224 144 240 0 0 0 0 0 0), upper := (rows 19 22 100 1001 1017 1001 1001 1001 1001 1001), lower := (rows 19 22 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,20,96] 13 :=
  bound_sound D R [18,20,96] 13 bound_7
    ((Boolean.boundCheck_true D R [18,20,96] 13 bound_7).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 19 22 261 104 760 744 744 744 1000 744), lower := (rows 19 22 261 104 16 32 64 128 256 512), losses := [] }

theorem upper_9 : Upper D R [18,20,257,96] 13 :=
  bound_sound D R [18,20,257,96] 13 bound_9
    ((Boolean.boundCheck_true D R [18,20,257,96] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 22 261 552 248 232 232 232 488 744), lower := (rows 19 22 261 552 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [18,20,257,544] 13 :=
  bound_sound D R [18,20,257,544] 13 bound_10
    ((Boolean.boundCheck_true D R [18,20,257,544] 13 bound_10).mp (by decide +kernel))

def route_8 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_8 : Upper D R [18,20,257] 13 := by
  apply routed_branch D R [18,20,257] 13 (by decide) (choices 2) [96,544] route_8
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,20,257] (choices 2) [96,544] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_9
  · exact upper_10

def bound_12 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 22 268 41 752 736 736 736 992 736), lower := (rows 19 22 268 41 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [18,20,264,33] 13 :=
  bound_sound D R [18,20,264,33] 13 bound_12
    ((Boolean.boundCheck_true D R [18,20,264,33] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 19 22 268 104 753 737 737 737 993 737), lower := (rows 19 22 268 104 16 32 64 128 256 512), losses := [] }

theorem upper_13 : Upper D R [18,20,264,96] 13 :=
  bound_sound D R [18,20,264,96] 13 bound_13
    ((Boolean.boundCheck_true D R [18,20,264,96] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 19 22 268 521 240 224 224 224 480 736), lower := (rows 19 22 268 521 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 13 9 0 1023 1023 1023 1023 1023), good := (rows 1007 998 1004 1005 992 992 992 992 992 992) }] }

theorem upper_14 : Upper D R [18,20,264,513] 13 :=
  bound_sound D R [18,20,264,513] 13 bound_14
    ((Boolean.boundCheck_true D R [18,20,264,513] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 22 268 552 241 225 225 225 481 737), lower := (rows 19 22 268 552 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [18,20,264,544] 13 :=
  bound_sound D R [18,20,264,544] 13 bound_15
    ((Boolean.boundCheck_true D R [18,20,264,544] 13 bound_15).mp (by decide +kernel))

def route_11 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_11 : Upper D R [18,20,264] 13 := by
  apply routed_branch D R [18,20,264] 13 (by decide) (choices 2) [33,96,513,544] route_11
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,20,264] (choices 2) [33,96,513,544] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_12
  · exact upper_13
  · exact upper_14
  · exact upper_15

def bound_16 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 19 22 292 745 761 745 745 745 1001 745), lower := (rows 19 22 292 8 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [18,20,288] 13 :=
  bound_sound D R [18,20,288] 13 bound_16
    ((Boolean.boundCheck_true D R [18,20,288] 13 bound_16).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 22 772 41 248 232 232 232 488 744), lower := (rows 19 22 772 41 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [18,20,768,33] 13 :=
  bound_sound D R [18,20,768,33] 13 bound_18
    ((Boolean.boundCheck_true D R [18,20,768,33] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 19 22 772 104 249 233 233 233 489 745), lower := (rows 19 22 772 104 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [18,20,768,96] 13 :=
  bound_sound D R [18,20,768,96] 13 bound_19
    ((Boolean.boundCheck_true D R [18,20,768,96] 13 bound_19).mp (by decide +kernel))

def route_17 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_17 : Upper D R [18,20,768] 13 := by
  apply routed_branch D R [18,20,768] 13 (by decide) (choices 2) [33,96] route_17
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,20,768] (choices 2) [33,96] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_18
  · exact upper_19

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,20] 13 := by
  apply routed_branch D R [18,20] 13 (by decide) (choices 2) [9,33,40,96,257,264,288,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,20] (choices 2) [9,33,40,96,257,264,288,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_8
  · exact upper_11
  · exact upper_16
  · exact upper_17

theorem upper : Upper D R [18,20] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case11
