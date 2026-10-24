import IrregularTen14Base

namespace Delivery.IrregularTen14.Case21
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 7 14 56 976 992 960 960 960 960), lower := (rows 49 7 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [48,5,10,48] 13 :=
  bound_sound D R [48,5,10,48] 13 bound_2
    ((Boolean.boundCheck_true D R [48,5,10,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 7 14 88 1008 992 992 992 992 992), lower := (rows 49 7 14 88 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [48,5,10,80] 13 :=
  bound_sound D R [48,5,10,80] 13 bound_3
    ((Boolean.boundCheck_true D R [48,5,10,80] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 7 14 200 1008 1008 1008 1008 1008 1008), lower := (rows 49 7 14 200 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [48,5,10,192] 13 :=
  bound_sound D R [48,5,10,192] 13 bound_4
    ((Boolean.boundCheck_true D R [48,5,10,192] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 7 14 280 752 736 736 736 992 736), lower := (rows 49 7 14 280 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [48,5,10,272] 13 :=
  bound_sound D R [48,5,10,272] 13 bound_5
    ((Boolean.boundCheck_true D R [48,5,10,272] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 7 14 328 752 752 752 752 1008 752), lower := (rows 49 7 14 328 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [48,5,10,320] 13 :=
  bound_sound D R [48,5,10,320] 13 bound_6
    ((Boolean.boundCheck_true D R [48,5,10,320] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 7 14 776 48 240 208 208 464 720), lower := (rows 49 7 14 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 3 7 27 16 0 81 145 273 529), good := (rows 991 975 14 776 984 0 64 128 256 512) }] }

theorem upper_8 : Upper D R [48,5,10,768,32] 13 :=
  bound_sound D R [48,5,10,768,32] 13 bound_8
    ((Boolean.boundCheck_true D R [48,5,10,768,32] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 7 14 776 80 48 224 224 480 736), lower := (rows 49 7 14 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 43 0 32 97 161 289 545), good := (rows 1007 975 14 776 64 1000 64 128 256 512) }] }

theorem upper_10 : Upper D R [48,5,10,768,64,16] 13 :=
  bound_sound D R [48,5,10,768,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [48,5,10,768,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 7 14 776 80 96 240 176 432 688), lower := (rows 49 7 14 776 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 3 7 11 16 32 0 129 257 513), good := (rows 959 911 14 776 16 32 0 128 256 512) }] }

theorem upper_11 : Upper D R [48,5,10,768,64,64] 13 :=
  bound_sound D R [48,5,10,768,64,64] 13 bound_11
    ((Boolean.boundCheck_true D R [48,5,10,768,64,64] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 7 14 776 80 160 80 224 480 736), lower := (rows 49 7 14 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 89 0 241 64 208 336 592), good := (rows 943 47 14 776 1000 160 1000 160 256 512) }] }

theorem upper_13 : Upper D R [48,5,10,768,64,128,16] 13 :=
  bound_sound D R [48,5,10,768,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [48,5,10,768,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 7 14 776 80 160 96 208 464 720), lower := (rows 49 7 14 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 3 7 89 80 0 64 208 336 592), good := (rows 927 15 14 776 984 128 984 128 256 512) }] }

theorem upper_14 : Upper D R [48,5,10,768,64,128,32] 13 :=
  bound_sound D R [48,5,10,768,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [48,5,10,768,64,128,32] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 7 14 776 80 160 192 240 368 624), lower := (rows 49 7 14 776 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 7 14 776 49 160 160 160 256 512) }] }

theorem upper_15 : Upper D R [48,5,10,768,64,128,128] 13 :=
  bound_sound D R [48,5,10,768,64,128,128] 13 bound_15
    ((Boolean.boundCheck_true D R [48,5,10,768,64,128,128] 13 bound_15).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [48,5,10,768,64,128] 13 := by
  apply routed_branch D R [48,5,10,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,5,10,768,64,128] (choices 1) [16,32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_15

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [48,5,10,768,64] 13 := by
  apply routed_branch D R [48,5,10,768,64] 13 (by decide) (choices 1) [16,64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,5,10,768,64] (choices 1) [16,64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def route_7 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_7 : Upper D R [48,5,10,768] 13 := by
  apply routed_branch D R [48,5,10,768] 13 (by decide) (choices 1) [32,64] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,5,10,768] (choices 1) [32,64] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_8
  · exact upper_9

def route_1 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [48,5,10] 13 := by
  apply routed_branch D R [48,5,10] 13 (by decide) (choices 2) [48,80,192,272,320,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,5,10] (choices 2) [48,80,192,272,320,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7

def bound_16 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 7 22 1000 1016 1000 1000 1000 1000 1000), lower := (rows 49 7 22 8 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [48,5,18] 13 :=
  bound_sound D R [48,5,18] 13 bound_16
    ((Boolean.boundCheck_true D R [48,5,18] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 7 28 1002 1010 994 994 994 994 994), lower := (rows 49 7 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [48,5,24] 13 :=
  bound_sound D R [48,5,24] 13 bound_17
    ((Boolean.boundCheck_true D R [48,5,24] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 192 240 192 240 0 0 0 0 0 0), upper := (rows 49 7 52 970 986 1002 970 970 970 970), lower := (rows 49 7 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [48,5,48] 13 :=
  bound_sound D R [48,5,48] 13 bound_18
    ((Boolean.boundCheck_true D R [48,5,48] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 7 70 1016 1016 1016 1016 1016 1016 1016), lower := (rows 49 7 70 8 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [48,5,66] 13 :=
  bound_sound D R [48,5,66] 13 bound_19
    ((Boolean.boundCheck_true D R [48,5,66] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 7 76 1018 1010 1010 1010 1010 1010 1010), lower := (rows 49 7 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [48,5,72] 13 :=
  bound_sound D R [48,5,72] 13 bound_20
    ((Boolean.boundCheck_true D R [48,5,72] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 192 240 160 240 0 0 0 0 0 0), upper := (rows 49 7 84 1002 1018 1002 1002 1002 1002 1002), lower := (rows 49 7 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [48,5,80] 13 :=
  bound_sound D R [48,5,80] 13 bound_21
    ((Boolean.boundCheck_true D R [48,5,80] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 192 240 48 240 0 0 0 0 0 0), upper := (rows 49 7 196 1018 1018 1018 1018 1018 1018 1018), lower := (rows 49 7 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [48,5,192] 13 :=
  bound_sound D R [48,5,192] 13 bound_22
    ((Boolean.boundCheck_true D R [48,5,192] 13 bound_22).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 7 262 56 728 744 712 712 968 712), lower := (rows 49 7 262 56 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [48,5,258,48] 13 :=
  bound_sound D R [48,5,258,48] 13 bound_24
    ((Boolean.boundCheck_true D R [48,5,258,48] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 7 262 88 760 744 744 744 1000 744), lower := (rows 49 7 262 88 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [48,5,258,80] 13 :=
  bound_sound D R [48,5,258,80] 13 bound_25
    ((Boolean.boundCheck_true D R [48,5,258,80] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 7 262 200 760 760 760 760 1016 760), lower := (rows 49 7 262 200 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [48,5,258,192] 13 :=
  bound_sound D R [48,5,258,192] 13 bound_26
    ((Boolean.boundCheck_true D R [48,5,258,192] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 7 262 536 248 232 232 232 488 744), lower := (rows 49 7 262 536 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [48,5,258,528] 13 :=
  bound_sound D R [48,5,258,528] 13 bound_27
    ((Boolean.boundCheck_true D R [48,5,258,528] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 7 262 584 248 248 248 248 504 760), lower := (rows 49 7 262 584 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [48,5,258,576] 13 :=
  bound_sound D R [48,5,258,576] 13 bound_28
    ((Boolean.boundCheck_true D R [48,5,258,576] 13 bound_28).mp (by decide +kernel))

def route_23 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_23 : Upper D R [48,5,258] 13 := by
  apply routed_branch D R [48,5,258] 13 (by decide) (choices 2) [48,80,192,528,576] route_23
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,5,258] (choices 2) [48,80,192,528,576] route_23).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_24
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28

def bound_30 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 7 268 26 752 736 736 736 992 736), lower := (rows 49 7 268 26 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [48,5,264,18] 13 :=
  bound_sound D R [48,5,264,18] 13 bound_30
    ((Boolean.boundCheck_true D R [48,5,264,18] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 7 268 56 722 738 706 706 962 706), lower := (rows 49 7 268 56 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [48,5,264,48] 13 :=
  bound_sound D R [48,5,264,48] 13 bound_31
    ((Boolean.boundCheck_true D R [48,5,264,48] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 7 268 74 752 752 752 752 1008 752), lower := (rows 49 7 268 74 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [48,5,264,66] 13 :=
  bound_sound D R [48,5,264,66] 13 bound_32
    ((Boolean.boundCheck_true D R [48,5,264,66] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 7 268 88 754 738 738 738 994 738), lower := (rows 49 7 268 88 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [48,5,264,80] 13 :=
  bound_sound D R [48,5,264,80] 13 bound_33
    ((Boolean.boundCheck_true D R [48,5,264,80] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 7 268 200 754 754 754 754 1010 754), lower := (rows 49 7 268 200 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [48,5,264,192] 13 :=
  bound_sound D R [48,5,264,192] 13 bound_34
    ((Boolean.boundCheck_true D R [48,5,264,192] 13 bound_34).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 7 268 522 48 240 208 208 464 720), lower := (rows 49 7 268 522 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 3 7 11 16 0 81 145 273 529), good := (rows 991 975 268 526 976 0 64 128 256 512) }] }

theorem upper_36 : Upper D R [48,5,264,514,32] 13 :=
  bound_sound D R [48,5,264,514,32] 13 bound_36
    ((Boolean.boundCheck_true D R [48,5,264,514,32] 13 bound_36).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 7 268 522 80 48 224 224 480 736), lower := (rows 49 7 268 522 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 7 11 0 32 97 161 289 545), good := (rows 1007 975 268 526 64 992 64 128 256 512) }] }

theorem upper_38 : Upper D R [48,5,264,514,64,16] 13 :=
  bound_sound D R [48,5,264,514,64,16] 13 bound_38
    ((Boolean.boundCheck_true D R [48,5,264,514,64,16] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 7 268 522 80 96 240 176 432 688), lower := (rows 49 7 268 522 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 3 7 11 16 32 0 129 257 513), good := (rows 959 911 268 526 16 32 0 128 256 512) }] }

theorem upper_39 : Upper D R [48,5,264,514,64,64] 13 :=
  bound_sound D R [48,5,264,514,64,64] 13 bound_39
    ((Boolean.boundCheck_true D R [48,5,264,514,64,64] 13 bound_39).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 7 268 522 80 160 80 224 480 736), lower := (rows 49 7 268 522 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 5 9 0 241 64 208 336 592), good := (rows 943 47 268 522 992 160 992 160 256 512) }] }

theorem upper_41 : Upper D R [48,5,264,514,64,128,16] 13 :=
  bound_sound D R [48,5,264,514,64,128,16] 13 bound_41
    ((Boolean.boundCheck_true D R [48,5,264,514,64,128,16] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 7 268 522 80 160 96 208 464 720), lower := (rows 49 7 268 522 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 3 5 9 80 0 64 208 336 592), good := (rows 927 15 268 522 976 128 976 128 256 512) }] }

theorem upper_42 : Upper D R [48,5,264,514,64,128,32] 13 :=
  bound_sound D R [48,5,264,514,64,128,32] 13 bound_42
    ((Boolean.boundCheck_true D R [48,5,264,514,64,128,32] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 7 268 522 80 160 192 240 368 624), lower := (rows 49 7 268 522 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 7 268 522 49 160 160 160 256 512) }] }

theorem upper_43 : Upper D R [48,5,264,514,64,128,128] 13 :=
  bound_sound D R [48,5,264,514,64,128,128] 13 bound_43
    ((Boolean.boundCheck_true D R [48,5,264,514,64,128,128] 13 bound_43).mp (by decide +kernel))

def route_40 : Route 10 := (fun mask => (mask,id))

theorem upper_40 : Upper D R [48,5,264,514,64,128] 13 := by
  apply routed_branch D R [48,5,264,514,64,128] 13 (by decide) (choices 1) [16,32,128] route_40
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,5,264,514,64,128] (choices 1) [16,32,128] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_43

def route_37 : Route 10 := (fun mask => (mask,id))

theorem upper_37 : Upper D R [48,5,264,514,64] 13 := by
  apply routed_branch D R [48,5,264,514,64] 13 (by decide) (choices 1) [16,64,128] route_37
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,5,264,514,64] (choices 1) [16,64,128] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_38
  · exact upper_39
  · exact upper_40

def route_35 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_35 : Upper D R [48,5,264,514] 13 := by
  apply routed_branch D R [48,5,264,514] 13 (by decide) (choices 1) [32,64] route_35
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,5,264,514] (choices 1) [32,64] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_36
  · exact upper_37

def bound_44 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 7 268 536 242 226 226 226 482 738), lower := (rows 49 7 268 536 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [48,5,264,528] 13 :=
  bound_sound D R [48,5,264,528] 13 bound_44
    ((Boolean.boundCheck_true D R [48,5,264,528] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 7 268 584 242 242 242 242 498 754), lower := (rows 49 7 268 584 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [48,5,264,576] 13 :=
  bound_sound D R [48,5,264,576] 13 bound_45
    ((Boolean.boundCheck_true D R [48,5,264,576] 13 bound_45).mp (by decide +kernel))

def route_29 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_29 : Upper D R [48,5,264] 13 := by
  apply routed_branch D R [48,5,264] 13 (by decide) (choices 2) [18,48,66,80,192,514,528,576] route_29
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,5,264] (choices 2) [18,48,66,80,192,514,528,576] route_29).mp (by decide +kernel))
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

def bound_46 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 7 276 746 762 746 746 746 1002 746), lower := (rows 49 7 276 8 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [48,5,272] 13 :=
  bound_sound D R [48,5,272] 13 bound_46
    ((Boolean.boundCheck_true D R [48,5,272] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 7 324 762 762 762 762 762 1018 762), lower := (rows 49 7 324 8 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [48,5,320] 13 :=
  bound_sound D R [48,5,320] 13 bound_47
    ((Boolean.boundCheck_true D R [48,5,320] 13 bound_47).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 7 772 26 248 232 232 232 488 744), lower := (rows 49 7 772 26 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [48,5,768,18] 13 :=
  bound_sound D R [48,5,768,18] 13 bound_49
    ((Boolean.boundCheck_true D R [48,5,768,18] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 7 772 56 218 234 202 202 458 714), lower := (rows 49 7 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [48,5,768,48] 13 :=
  bound_sound D R [48,5,768,48] 13 bound_50
    ((Boolean.boundCheck_true D R [48,5,768,48] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 7 772 74 248 248 248 248 504 760), lower := (rows 49 7 772 74 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [48,5,768,66] 13 :=
  bound_sound D R [48,5,768,66] 13 bound_51
    ((Boolean.boundCheck_true D R [48,5,768,66] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 7 772 88 250 234 234 234 490 746), lower := (rows 49 7 772 88 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [48,5,768,80] 13 :=
  bound_sound D R [48,5,768,80] 13 bound_52
    ((Boolean.boundCheck_true D R [48,5,768,80] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 7 772 200 250 250 250 250 506 762), lower := (rows 49 7 772 200 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [48,5,768,192] 13 :=
  bound_sound D R [48,5,768,192] 13 bound_53
    ((Boolean.boundCheck_true D R [48,5,768,192] 13 bound_53).mp (by decide +kernel))

def route_48 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_48 : Upper D R [48,5,768] 13 := by
  apply routed_branch D R [48,5,768] 13 (by decide) (choices 2) [18,48,66,80,192] route_48
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,5,768] (choices 2) [18,48,66,80,192] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53

def route_0 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 514 => (258,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [48,5] 13 := by
  apply routed_branch D R [48,5] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,192,258,264,272,320,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,5] (choices 2) [10,18,24,48,66,72,80,192,258,264,272,320,768] route_0).mp (by decide +kernel))
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

theorem upper : Upper D R [48,5] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case21
