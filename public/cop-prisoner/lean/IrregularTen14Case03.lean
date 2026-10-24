import IrregularTen14Base

namespace Delivery.IrregularTen14.Case03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 240 192 240 192 0 0 0 0 0 0), upper := (rows 7 50 13 56 976 992 960 960 960 960), lower := (rows 7 50 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [6,48,9,48] 13 :=
  bound_sound D R [6,48,9,48] 13 bound_2
    ((Boolean.boundCheck_true D R [6,48,9,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 240 192 240 160 0 0 0 0 0 0), upper := (rows 7 50 13 88 1008 992 992 992 992 992), lower := (rows 7 50 13 88 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [6,48,9,80] 13 :=
  bound_sound D R [6,48,9,80] 13 bound_3
    ((Boolean.boundCheck_true D R [6,48,9,80] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 240 192 240 48 0 0 0 0 0 0), upper := (rows 7 50 13 200 1008 1008 1008 1008 1008 1008), lower := (rows 7 50 13 200 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [6,48,9,192] 13 :=
  bound_sound D R [6,48,9,192] 13 bound_4
    ((Boolean.boundCheck_true D R [6,48,9,192] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 7 50 13 280 752 736 736 736 992 736), lower := (rows 7 50 13 280 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [6,48,9,272] 13 :=
  bound_sound D R [6,48,9,272] 13 bound_5
    ((Boolean.boundCheck_true D R [6,48,9,272] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 7 50 13 328 752 752 752 752 1008 752), lower := (rows 7 50 13 328 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [6,48,9,320] 13 :=
  bound_sound D R [6,48,9,320] 13 bound_6
    ((Boolean.boundCheck_true D R [6,48,9,320] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 7 50 13 776 48 240 208 208 464 720), lower := (rows 7 50 13 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 7 27 16 0 82 146 274 530), good := (rows 975 991 13 776 984 0 64 128 256 512) }] }

theorem upper_8 : Upper D R [6,48,9,768,32] 13 :=
  bound_sound D R [6,48,9,768,32] 13 bound_8
    ((Boolean.boundCheck_true D R [6,48,9,768,32] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 7 50 13 776 80 48 224 224 480 736), lower := (rows 7 50 13 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 43 0 32 98 162 290 546), good := (rows 975 1007 13 776 64 1000 64 128 256 512) }] }

theorem upper_10 : Upper D R [6,48,9,768,64,16] 13 :=
  bound_sound D R [6,48,9,768,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [6,48,9,768,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 176 192 176 176 0 0 0 0 0 0), upper := (rows 7 50 13 776 80 96 240 176 432 688), lower := (rows 7 50 13 776 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 3 2 7 11 16 32 0 130 258 514), good := (rows 911 959 13 776 16 32 0 128 256 512) }] }

theorem upper_11 : Upper D R [6,48,9,768,64,64] 13 :=
  bound_sound D R [6,48,9,768,64,64] 13 bound_11
    ((Boolean.boundCheck_true D R [6,48,9,768,64,64] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 7 50 13 776 80 160 80 224 480 736), lower := (rows 7 50 13 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 90 0 242 64 208 336 592), good := (rows 47 943 13 776 1000 160 1000 160 256 512) }] }

theorem upper_13 : Upper D R [6,48,9,768,64,128,16] 13 :=
  bound_sound D R [6,48,9,768,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [6,48,9,768,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 7 50 13 776 80 160 96 208 464 720), lower := (rows 7 50 13 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 7 90 80 0 64 208 336 592), good := (rows 15 927 13 776 984 128 984 128 256 512) }] }

theorem upper_14 : Upper D R [6,48,9,768,64,128,32] 13 :=
  bound_sound D R [6,48,9,768,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [6,48,9,768,64,128,32] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 240 128 240 240 0 0 0 0 0 0), upper := (rows 7 50 13 776 80 160 192 240 368 624), lower := (rows 7 50 13 776 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 18 4 8 16 224 0 128 256 512), good := (rows 7 50 13 776 50 160 160 160 256 512) }] }

theorem upper_15 : Upper D R [6,48,9,768,64,128,128] 13 :=
  bound_sound D R [6,48,9,768,64,128,128] 13 bound_15
    ((Boolean.boundCheck_true D R [6,48,9,768,64,128,128] 13 bound_15).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [6,48,9,768,64,128] 13 := by
  apply routed_branch D R [6,48,9,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,48,9,768,64,128] (choices 1) [16,32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_15

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [6,48,9,768,64] 13 := by
  apply routed_branch D R [6,48,9,768,64] 13 (by decide) (choices 1) [16,64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,48,9,768,64] (choices 1) [16,64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def route_7 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_7 : Upper D R [6,48,9,768] 13 := by
  apply routed_branch D R [6,48,9,768] 13 (by decide) (choices 1) [32,64] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,48,9,768] (choices 1) [32,64] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_8
  · exact upper_9

def route_1 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [6,48,9] 13 := by
  apply routed_branch D R [6,48,9] 13 (by decide) (choices 2) [48,80,192,272,320,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,48,9] (choices 2) [48,80,192,272,320,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7

def bound_16 : Bound 10 := { allowed := (rows 240 192 224 240 0 0 0 0 0 0), upper := (rows 7 50 21 1000 1016 1000 1000 1000 1000 1000), lower := (rows 7 50 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [6,48,17] 13 :=
  bound_sound D R [6,48,17] 13 bound_16
    ((Boolean.boundCheck_true D R [6,48,17] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 240 192 224 240 0 0 0 0 0 0), upper := (rows 7 50 28 1001 1009 993 993 993 993 993), lower := (rows 7 50 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [6,48,24] 13 :=
  bound_sound D R [6,48,24] 13 bound_17
    ((Boolean.boundCheck_true D R [6,48,24] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 240 192 192 240 0 0 0 0 0 0), upper := (rows 7 50 52 969 985 1001 969 969 969 969), lower := (rows 7 50 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [6,48,48] 13 :=
  bound_sound D R [6,48,48] 13 bound_18
    ((Boolean.boundCheck_true D R [6,48,48] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 240 192 176 240 0 0 0 0 0 0), upper := (rows 7 50 69 1016 1016 1016 1016 1016 1016 1016), lower := (rows 7 50 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [6,48,65] 13 :=
  bound_sound D R [6,48,65] 13 bound_19
    ((Boolean.boundCheck_true D R [6,48,65] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 240 192 176 240 0 0 0 0 0 0), upper := (rows 7 50 76 1017 1009 1009 1009 1009 1009 1009), lower := (rows 7 50 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [6,48,72] 13 :=
  bound_sound D R [6,48,72] 13 bound_20
    ((Boolean.boundCheck_true D R [6,48,72] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 240 192 160 240 0 0 0 0 0 0), upper := (rows 7 50 84 1001 1017 1001 1001 1001 1001 1001), lower := (rows 7 50 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [6,48,80] 13 :=
  bound_sound D R [6,48,80] 13 bound_21
    ((Boolean.boundCheck_true D R [6,48,80] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 240 192 48 240 0 0 0 0 0 0), upper := (rows 7 50 196 1017 1017 1017 1017 1017 1017 1017), lower := (rows 7 50 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [6,48,192] 13 :=
  bound_sound D R [6,48,192] 13 bound_22
    ((Boolean.boundCheck_true D R [6,48,192] 13 bound_22).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 192 240 192 0 0 0 0 0 0), upper := (rows 7 50 261 56 728 744 712 712 968 712), lower := (rows 7 50 261 56 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [6,48,257,48] 13 :=
  bound_sound D R [6,48,257,48] 13 bound_24
    ((Boolean.boundCheck_true D R [6,48,257,48] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 240 192 240 160 0 0 0 0 0 0), upper := (rows 7 50 261 88 760 744 744 744 1000 744), lower := (rows 7 50 261 88 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [6,48,257,80] 13 :=
  bound_sound D R [6,48,257,80] 13 bound_25
    ((Boolean.boundCheck_true D R [6,48,257,80] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 240 192 240 48 0 0 0 0 0 0), upper := (rows 7 50 261 200 760 760 760 760 1016 760), lower := (rows 7 50 261 200 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [6,48,257,192] 13 :=
  bound_sound D R [6,48,257,192] 13 bound_26
    ((Boolean.boundCheck_true D R [6,48,257,192] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 7 50 261 536 248 232 232 232 488 744), lower := (rows 7 50 261 536 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [6,48,257,528] 13 :=
  bound_sound D R [6,48,257,528] 13 bound_27
    ((Boolean.boundCheck_true D R [6,48,257,528] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 7 50 261 584 248 248 248 248 504 760), lower := (rows 7 50 261 584 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [6,48,257,576] 13 :=
  bound_sound D R [6,48,257,576] 13 bound_28
    ((Boolean.boundCheck_true D R [6,48,257,576] 13 bound_28).mp (by decide +kernel))

def route_23 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_23 : Upper D R [6,48,257] 13 := by
  apply routed_branch D R [6,48,257] 13 (by decide) (choices 2) [48,80,192,528,576] route_23
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,48,257] (choices 2) [48,80,192,528,576] route_23).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_24
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28

def bound_30 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 7 50 268 25 752 736 736 736 992 736), lower := (rows 7 50 268 25 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [6,48,264,17] 13 :=
  bound_sound D R [6,48,264,17] 13 bound_30
    ((Boolean.boundCheck_true D R [6,48,264,17] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 240 192 240 192 0 0 0 0 0 0), upper := (rows 7 50 268 56 721 737 705 705 961 705), lower := (rows 7 50 268 56 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [6,48,264,48] 13 :=
  bound_sound D R [6,48,264,48] 13 bound_31
    ((Boolean.boundCheck_true D R [6,48,264,48] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 7 50 268 73 752 752 752 752 1008 752), lower := (rows 7 50 268 73 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [6,48,264,65] 13 :=
  bound_sound D R [6,48,264,65] 13 bound_32
    ((Boolean.boundCheck_true D R [6,48,264,65] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 240 192 240 160 0 0 0 0 0 0), upper := (rows 7 50 268 88 753 737 737 737 993 737), lower := (rows 7 50 268 88 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [6,48,264,80] 13 :=
  bound_sound D R [6,48,264,80] 13 bound_33
    ((Boolean.boundCheck_true D R [6,48,264,80] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 240 192 240 48 0 0 0 0 0 0), upper := (rows 7 50 268 200 753 753 753 753 1009 753), lower := (rows 7 50 268 200 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [6,48,264,192] 13 :=
  bound_sound D R [6,48,264,192] 13 bound_34
    ((Boolean.boundCheck_true D R [6,48,264,192] 13 bound_34).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 7 50 268 521 48 240 208 208 464 720), lower := (rows 7 50 268 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 7 11 16 0 82 146 274 530), good := (rows 975 991 268 525 976 0 64 128 256 512) }] }

theorem upper_36 : Upper D R [6,48,264,513,32] 13 :=
  bound_sound D R [6,48,264,513,32] 13 bound_36
    ((Boolean.boundCheck_true D R [6,48,264,513,32] 13 bound_36).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 7 50 268 521 80 48 224 224 480 736), lower := (rows 7 50 268 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 11 0 32 98 162 290 546), good := (rows 975 1007 268 525 64 992 64 128 256 512) }] }

theorem upper_38 : Upper D R [6,48,264,513,64,16] 13 :=
  bound_sound D R [6,48,264,513,64,16] 13 bound_38
    ((Boolean.boundCheck_true D R [6,48,264,513,64,16] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 176 192 176 176 0 0 0 0 0 0), upper := (rows 7 50 268 521 80 96 240 176 432 688), lower := (rows 7 50 268 521 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 3 2 7 11 16 32 0 130 258 514), good := (rows 911 959 268 525 16 32 0 128 256 512) }] }

theorem upper_39 : Upper D R [6,48,264,513,64,64] 13 :=
  bound_sound D R [6,48,264,513,64,64] 13 bound_39
    ((Boolean.boundCheck_true D R [6,48,264,513,64,64] 13 bound_39).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 7 50 268 521 80 160 80 224 480 736), lower := (rows 7 50 268 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 6 10 0 242 64 208 336 592), good := (rows 47 943 268 521 992 160 992 160 256 512) }] }

theorem upper_41 : Upper D R [6,48,264,513,64,128,16] 13 :=
  bound_sound D R [6,48,264,513,64,128,16] 13 bound_41
    ((Boolean.boundCheck_true D R [6,48,264,513,64,128,16] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 7 50 268 521 80 160 96 208 464 720), lower := (rows 7 50 268 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 6 10 80 0 64 208 336 592), good := (rows 15 927 268 521 976 128 976 128 256 512) }] }

theorem upper_42 : Upper D R [6,48,264,513,64,128,32] 13 :=
  bound_sound D R [6,48,264,513,64,128,32] 13 bound_42
    ((Boolean.boundCheck_true D R [6,48,264,513,64,128,32] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 240 128 240 240 0 0 0 0 0 0), upper := (rows 7 50 268 521 80 160 192 240 368 624), lower := (rows 7 50 268 521 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 18 4 8 16 224 0 128 256 512), good := (rows 7 50 268 521 50 160 160 160 256 512) }] }

theorem upper_43 : Upper D R [6,48,264,513,64,128,128] 13 :=
  bound_sound D R [6,48,264,513,64,128,128] 13 bound_43
    ((Boolean.boundCheck_true D R [6,48,264,513,64,128,128] 13 bound_43).mp (by decide +kernel))

def route_40 : Route 10 := (fun mask => (mask,id))

theorem upper_40 : Upper D R [6,48,264,513,64,128] 13 := by
  apply routed_branch D R [6,48,264,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_40
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,48,264,513,64,128] (choices 1) [16,32,128] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_43

def route_37 : Route 10 := (fun mask => (mask,id))

theorem upper_37 : Upper D R [6,48,264,513,64] 13 := by
  apply routed_branch D R [6,48,264,513,64] 13 (by decide) (choices 1) [16,64,128] route_37
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,48,264,513,64] (choices 1) [16,64,128] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_38
  · exact upper_39
  · exact upper_40

def route_35 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_35 : Upper D R [6,48,264,513] 13 := by
  apply routed_branch D R [6,48,264,513] 13 (by decide) (choices 1) [32,64] route_35
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,48,264,513] (choices 1) [32,64] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_36
  · exact upper_37

def bound_44 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 7 50 268 536 241 225 225 225 481 737), lower := (rows 7 50 268 536 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [6,48,264,528] 13 :=
  bound_sound D R [6,48,264,528] 13 bound_44
    ((Boolean.boundCheck_true D R [6,48,264,528] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 7 50 268 584 241 241 241 241 497 753), lower := (rows 7 50 268 584 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [6,48,264,576] 13 :=
  bound_sound D R [6,48,264,576] 13 bound_45
    ((Boolean.boundCheck_true D R [6,48,264,576] 13 bound_45).mp (by decide +kernel))

def route_29 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_29 : Upper D R [6,48,264] 13 := by
  apply routed_branch D R [6,48,264] 13 (by decide) (choices 2) [17,48,65,80,192,513,528,576] route_29
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,48,264] (choices 2) [17,48,65,80,192,513,528,576] route_29).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_30
  · exact upper_31
  · exact upper_32
  · exact upper_33
  · exact upper_34
  · exact upper_35
  · exact upper_44
  · exact upper_45

def bound_46 : Bound 10 := { allowed := (rows 240 192 224 240 0 0 0 0 0 0), upper := (rows 7 50 276 745 761 745 745 745 1001 745), lower := (rows 7 50 276 8 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [6,48,272] 13 :=
  bound_sound D R [6,48,272] 13 bound_46
    ((Boolean.boundCheck_true D R [6,48,272] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 240 192 176 240 0 0 0 0 0 0), upper := (rows 7 50 324 761 761 761 761 761 1017 761), lower := (rows 7 50 324 8 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [6,48,320] 13 :=
  bound_sound D R [6,48,320] 13 bound_47
    ((Boolean.boundCheck_true D R [6,48,320] 13 bound_47).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 7 50 772 25 248 232 232 232 488 744), lower := (rows 7 50 772 25 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [6,48,768,17] 13 :=
  bound_sound D R [6,48,768,17] 13 bound_49
    ((Boolean.boundCheck_true D R [6,48,768,17] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 240 192 240 192 0 0 0 0 0 0), upper := (rows 7 50 772 56 217 233 201 201 457 713), lower := (rows 7 50 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [6,48,768,48] 13 :=
  bound_sound D R [6,48,768,48] 13 bound_50
    ((Boolean.boundCheck_true D R [6,48,768,48] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 7 50 772 73 248 248 248 248 504 760), lower := (rows 7 50 772 73 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [6,48,768,65] 13 :=
  bound_sound D R [6,48,768,65] 13 bound_51
    ((Boolean.boundCheck_true D R [6,48,768,65] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 240 192 240 160 0 0 0 0 0 0), upper := (rows 7 50 772 88 249 233 233 233 489 745), lower := (rows 7 50 772 88 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [6,48,768,80] 13 :=
  bound_sound D R [6,48,768,80] 13 bound_52
    ((Boolean.boundCheck_true D R [6,48,768,80] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 240 192 240 48 0 0 0 0 0 0), upper := (rows 7 50 772 200 249 249 249 249 505 761), lower := (rows 7 50 772 200 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [6,48,768,192] 13 :=
  bound_sound D R [6,48,768,192] 13 bound_53
    ((Boolean.boundCheck_true D R [6,48,768,192] 13 bound_53).mp (by decide +kernel))

def route_48 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_48 : Upper D R [6,48,768] 13 := by
  apply routed_branch D R [6,48,768] 13 (by decide) (choices 2) [17,48,65,80,192] route_48
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,48,768] (choices 2) [17,48,65,80,192] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53

def route_0 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [6,48] 13 := by
  apply routed_branch D R [6,48] 13 (by decide) (choices 2) [9,17,24,48,65,72,80,192,257,264,272,320,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,48] (choices 2) [9,17,24,48,65,72,80,192,257,264,272,320,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_16
  · exact upper_17
  · exact upper_18
  · exact upper_19
  · exact upper_20
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_29
  · exact upper_46
  · exact upper_47
  · exact upper_48

theorem upper : Upper D R [6,48] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case03
