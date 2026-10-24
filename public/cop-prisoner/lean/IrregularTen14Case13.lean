import IrregularTen14Base

namespace Delivery.IrregularTen14.Case13
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 38 13 56 976 992 960 960 960 960), lower := (rows 19 38 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,36,9,48] 13 :=
  bound_sound D R [18,36,9,48] 13 bound_2
    ((Boolean.boundCheck_true D R [18,36,9,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 38 13 88 1008 992 992 992 992 992), lower := (rows 19 38 13 88 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [18,36,9,80] 13 :=
  bound_sound D R [18,36,9,80] 13 bound_3
    ((Boolean.boundCheck_true D R [18,36,9,80] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 38 13 104 976 1008 976 976 976 976), lower := (rows 19 38 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [18,36,9,96] 13 :=
  bound_sound D R [18,36,9,96] 13 bound_4
    ((Boolean.boundCheck_true D R [18,36,9,96] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 38 13 200 1008 1008 1008 1008 1008 1008), lower := (rows 19 38 13 200 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [18,36,9,192] 13 :=
  bound_sound D R [18,36,9,192] 13 bound_5
    ((Boolean.boundCheck_true D R [18,36,9,192] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 38 13 280 752 736 736 736 992 736), lower := (rows 19 38 13 280 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [18,36,9,272] 13 :=
  bound_sound D R [18,36,9,272] 13 bound_6
    ((Boolean.boundCheck_true D R [18,36,9,272] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 38 13 296 720 752 720 720 976 720), lower := (rows 19 38 13 296 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,36,9,288] 13 :=
  bound_sound D R [18,36,9,288] 13 bound_7
    ((Boolean.boundCheck_true D R [18,36,9,288] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 38 13 328 752 752 752 752 1008 752), lower := (rows 19 38 13 328 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [18,36,9,320] 13 :=
  bound_sound D R [18,36,9,320] 13 bound_8
    ((Boolean.boundCheck_true D R [18,36,9,320] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 38 13 776 48 240 208 208 464 720), lower := (rows 19 38 13 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 29 16 0 81 145 273 529), good := (rows 991 14 973 776 984 0 64 128 256 512) }] }

theorem upper_10 : Upper D R [18,36,9,768,32] 13 :=
  bound_sound D R [18,36,9,768,32] 13 bound_10
    ((Boolean.boundCheck_true D R [18,36,9,768,32] 13 bound_10).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 208 224 224 0 0 0 0 0 0), upper := (rows 19 38 13 776 80 48 224 224 480 736), lower := (rows 19 38 13 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 43 0 32 98 162 290 546), good := (rows 975 1006 13 776 64 1000 64 128 256 512) }] }

theorem upper_12 : Upper D R [18,36,9,768,64,16] 13 :=
  bound_sound D R [18,36,9,768,64,16] 13 bound_12
    ((Boolean.boundCheck_true D R [18,36,9,768,64,16] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 38 13 776 80 96 240 176 432 688), lower := (rows 19 38 13 776 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 112 0 64 128 256 512), good := (rows 19 23 13 776 80 80 80 128 256 512) }] }

theorem upper_13 : Upper D R [18,36,9,768,64,64] 13 :=
  bound_sound D R [18,36,9,768,64,64] 13 bound_13
    ((Boolean.boundCheck_true D R [18,36,9,768,64,64] 13 bound_13).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 19 38 13 776 80 160 80 224 480 736), lower := (rows 19 38 13 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 89 0 241 64 208 336 592), good := (rows 943 38 47 776 1000 160 1000 160 256 512) }] }

theorem upper_15 : Upper D R [18,36,9,768,64,128,16] 13 :=
  bound_sound D R [18,36,9,768,64,128,16] 13 bound_15
    ((Boolean.boundCheck_true D R [18,36,9,768,64,128,16] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 38 13 776 80 160 96 208 464 720), lower := (rows 19 38 13 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 89 80 0 64 208 336 592), good := (rows 927 6 13 776 984 128 984 128 256 512) }] }

theorem upper_16 : Upper D R [18,36,9,768,64,128,32] 13 :=
  bound_sound D R [18,36,9,768,64,128,32] 13 bound_16
    ((Boolean.boundCheck_true D R [18,36,9,768,64,128,32] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 38 13 776 80 160 192 240 368 624), lower := (rows 19 38 13 776 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 242 0 224 128 256 512), good := (rows 19 87 13 776 80 208 208 208 256 512) }] }

theorem upper_17 : Upper D R [18,36,9,768,64,128,128] 13 :=
  bound_sound D R [18,36,9,768,64,128,128] 13 bound_17
    ((Boolean.boundCheck_true D R [18,36,9,768,64,128,128] 13 bound_17).mp (by decide +kernel))

def route_14 : Route 10 := (fun mask => (mask,id))

theorem upper_14 : Upper D R [18,36,9,768,64,128] 13 := by
  apply routed_branch D R [18,36,9,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_14
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,36,9,768,64,128] (choices 1) [16,32,128] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_15
  · exact upper_16
  · exact upper_17

def route_11 : Route 10 := (fun mask => (mask,id))

theorem upper_11 : Upper D R [18,36,9,768,64] 13 := by
  apply routed_branch D R [18,36,9,768,64] 13 (by decide) (choices 1) [16,64,128] route_11
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,36,9,768,64] (choices 1) [16,64,128] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_12
  · exact upper_13
  · exact upper_14

def route_9 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [18,36,9,768] 13 := by
  apply routed_branch D R [18,36,9,768] 13 (by decide) (choices 1) [32,64] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,36,9,768] (choices 1) [32,64] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_11

def route_1 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [18,36,9] 13 := by
  apply routed_branch D R [18,36,9] 13 (by decide) (choices 2) [48,80,96,192,272,288,320,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,36,9] (choices 2) [48,80,96,192,272,288,320,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_8
  · exact upper_9

def bound_18 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 38 21 1000 1016 1000 1000 1000 1000 1000), lower := (rows 19 38 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [18,36,17] 13 :=
  bound_sound D R [18,36,17] 13 bound_18
    ((Boolean.boundCheck_true D R [18,36,17] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 38 28 1001 1009 993 993 993 993 993), lower := (rows 19 38 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [18,36,24] 13 :=
  bound_sound D R [18,36,24] 13 bound_19
    ((Boolean.boundCheck_true D R [18,36,24] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 38 37 984 984 1016 984 984 984 984), lower := (rows 19 38 37 8 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [18,36,33] 13 :=
  bound_sound D R [18,36,33] 13 bound_20
    ((Boolean.boundCheck_true D R [18,36,33] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 38 44 985 977 1009 977 977 977 977), lower := (rows 19 38 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [18,36,40] 13 :=
  bound_sound D R [18,36,40] 13 bound_21
    ((Boolean.boundCheck_true D R [18,36,40] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 208 192 240 0 0 0 0 0 0), upper := (rows 19 38 52 969 985 1001 969 969 969 969), lower := (rows 19 38 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [18,36,48] 13 :=
  bound_sound D R [18,36,48] 13 bound_22
    ((Boolean.boundCheck_true D R [18,36,48] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 38 69 1016 1016 1016 1016 1016 1016 1016), lower := (rows 19 38 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [18,36,65] 13 :=
  bound_sound D R [18,36,65] 13 bound_23
    ((Boolean.boundCheck_true D R [18,36,65] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 38 76 1017 1009 1009 1009 1009 1009 1009), lower := (rows 19 38 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [18,36,72] 13 :=
  bound_sound D R [18,36,72] 13 bound_24
    ((Boolean.boundCheck_true D R [18,36,72] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 224 208 160 240 0 0 0 0 0 0), upper := (rows 19 38 84 1001 1017 1001 1001 1001 1001 1001), lower := (rows 19 38 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [18,36,80] 13 :=
  bound_sound D R [18,36,80] 13 bound_25
    ((Boolean.boundCheck_true D R [18,36,80] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 208 144 240 0 0 0 0 0 0), upper := (rows 19 38 100 985 985 1017 985 985 985 985), lower := (rows 19 38 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [18,36,96] 13 :=
  bound_sound D R [18,36,96] 13 bound_26
    ((Boolean.boundCheck_true D R [18,36,96] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 208 48 240 0 0 0 0 0 0), upper := (rows 19 38 196 1017 1017 1017 1017 1017 1017 1017), lower := (rows 19 38 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [18,36,192] 13 :=
  bound_sound D R [18,36,192] 13 bound_27
    ((Boolean.boundCheck_true D R [18,36,192] 13 bound_27).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 38 261 56 728 744 712 712 968 712), lower := (rows 19 38 261 56 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [18,36,257,48] 13 :=
  bound_sound D R [18,36,257,48] 13 bound_29
    ((Boolean.boundCheck_true D R [18,36,257,48] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 38 261 88 760 744 744 744 1000 744), lower := (rows 19 38 261 88 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [18,36,257,80] 13 :=
  bound_sound D R [18,36,257,80] 13 bound_30
    ((Boolean.boundCheck_true D R [18,36,257,80] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 38 261 104 728 760 728 728 984 728), lower := (rows 19 38 261 104 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [18,36,257,96] 13 :=
  bound_sound D R [18,36,257,96] 13 bound_31
    ((Boolean.boundCheck_true D R [18,36,257,96] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 38 261 200 760 760 760 760 1016 760), lower := (rows 19 38 261 200 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [18,36,257,192] 13 :=
  bound_sound D R [18,36,257,192] 13 bound_32
    ((Boolean.boundCheck_true D R [18,36,257,192] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 38 261 536 248 232 232 232 488 744), lower := (rows 19 38 261 536 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [18,36,257,528] 13 :=
  bound_sound D R [18,36,257,528] 13 bound_33
    ((Boolean.boundCheck_true D R [18,36,257,528] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 38 261 552 216 248 216 216 472 728), lower := (rows 19 38 261 552 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [18,36,257,544] 13 :=
  bound_sound D R [18,36,257,544] 13 bound_34
    ((Boolean.boundCheck_true D R [18,36,257,544] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 38 261 584 248 248 248 248 504 760), lower := (rows 19 38 261 584 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [18,36,257,576] 13 :=
  bound_sound D R [18,36,257,576] 13 bound_35
    ((Boolean.boundCheck_true D R [18,36,257,576] 13 bound_35).mp (by decide +kernel))

def route_28 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_28 : Upper D R [18,36,257] 13 := by
  apply routed_branch D R [18,36,257] 13 (by decide) (choices 2) [48,80,96,192,528,544,576] route_28
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,36,257] (choices 2) [48,80,96,192,528,544,576] route_28).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_32
  · exact upper_33
  · exact upper_34
  · exact upper_35

def bound_37 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 38 268 25 752 736 736 736 992 736), lower := (rows 19 38 268 25 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [18,36,264,17] 13 :=
  bound_sound D R [18,36,264,17] 13 bound_37
    ((Boolean.boundCheck_true D R [18,36,264,17] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 38 268 41 720 752 720 720 976 720), lower := (rows 19 38 268 41 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [18,36,264,33] 13 :=
  bound_sound D R [18,36,264,33] 13 bound_38
    ((Boolean.boundCheck_true D R [18,36,264,33] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 38 268 56 721 737 705 705 961 705), lower := (rows 19 38 268 56 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [18,36,264,48] 13 :=
  bound_sound D R [18,36,264,48] 13 bound_39
    ((Boolean.boundCheck_true D R [18,36,264,48] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 38 268 73 752 752 752 752 1008 752), lower := (rows 19 38 268 73 16 32 64 128 256 512), losses := [] }

theorem upper_40 : Upper D R [18,36,264,65] 13 :=
  bound_sound D R [18,36,264,65] 13 bound_40
    ((Boolean.boundCheck_true D R [18,36,264,65] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 38 268 88 753 737 737 737 993 737), lower := (rows 19 38 268 88 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [18,36,264,80] 13 :=
  bound_sound D R [18,36,264,80] 13 bound_41
    ((Boolean.boundCheck_true D R [18,36,264,80] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 38 268 104 721 753 721 721 977 721), lower := (rows 19 38 268 104 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [18,36,264,96] 13 :=
  bound_sound D R [18,36,264,96] 13 bound_42
    ((Boolean.boundCheck_true D R [18,36,264,96] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 38 268 200 753 753 753 753 1009 753), lower := (rows 19 38 268 200 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [18,36,264,192] 13 :=
  bound_sound D R [18,36,264,192] 13 bound_43
    ((Boolean.boundCheck_true D R [18,36,264,192] 13 bound_43).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 38 268 521 48 240 208 208 464 720), lower := (rows 19 38 268 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 13 9 16 0 81 145 273 529), good := (rows 991 6 268 973 976 0 64 128 256 512) }] }

theorem upper_45 : Upper D R [18,36,264,513,32] 13 :=
  bound_sound D R [18,36,264,513,32] 13 bound_45
    ((Boolean.boundCheck_true D R [18,36,264,513,32] 13 bound_45).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 208 224 224 0 0 0 0 0 0), upper := (rows 19 38 268 521 80 48 224 224 480 736), lower := (rows 19 38 268 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 9 0 32 98 162 290 546), good := (rows 975 998 268 525 64 992 64 128 256 512) }] }

theorem upper_47 : Upper D R [18,36,264,513,64,16] 13 :=
  bound_sound D R [18,36,264,513,64,16] 13 bound_47
    ((Boolean.boundCheck_true D R [18,36,264,513,64,16] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 38 268 521 80 96 240 176 432 688), lower := (rows 19 38 268 521 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 112 0 64 128 256 512), good := (rows 19 23 268 521 80 80 80 128 256 512) }] }

theorem upper_48 : Upper D R [18,36,264,513,64,64] 13 :=
  bound_sound D R [18,36,264,513,64,64] 13 bound_48
    ((Boolean.boundCheck_true D R [18,36,264,513,64,64] 13 bound_48).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 19 38 268 521 80 160 80 224 480 736), lower := (rows 19 38 268 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 5 9 0 241 64 208 336 592), good := (rows 943 38 270 559 992 160 992 160 256 512) }] }

theorem upper_50 : Upper D R [18,36,264,513,64,128,16] 13 :=
  bound_sound D R [18,36,264,513,64,128,16] 13 bound_50
    ((Boolean.boundCheck_true D R [18,36,264,513,64,128,16] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 38 268 521 80 160 96 208 464 720), lower := (rows 19 38 268 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 9 80 0 64 208 336 592), good := (rows 927 6 268 525 976 128 976 128 256 512) }] }

theorem upper_51 : Upper D R [18,36,264,513,64,128,32] 13 :=
  bound_sound D R [18,36,264,513,64,128,32] 13 bound_51
    ((Boolean.boundCheck_true D R [18,36,264,513,64,128,32] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 38 268 521 80 160 192 240 368 624), lower := (rows 19 38 268 521 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 242 0 224 128 256 512), good := (rows 19 87 268 521 80 208 208 208 256 512) }] }

theorem upper_52 : Upper D R [18,36,264,513,64,128,128] 13 :=
  bound_sound D R [18,36,264,513,64,128,128] 13 bound_52
    ((Boolean.boundCheck_true D R [18,36,264,513,64,128,128] 13 bound_52).mp (by decide +kernel))

def route_49 : Route 10 := (fun mask => (mask,id))

theorem upper_49 : Upper D R [18,36,264,513,64,128] 13 := by
  apply routed_branch D R [18,36,264,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_49
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,36,264,513,64,128] (choices 1) [16,32,128] route_49).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_50
  · exact upper_51
  · exact upper_52

def route_46 : Route 10 := (fun mask => (mask,id))

theorem upper_46 : Upper D R [18,36,264,513,64] 13 := by
  apply routed_branch D R [18,36,264,513,64] 13 (by decide) (choices 1) [16,64,128] route_46
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,36,264,513,64] (choices 1) [16,64,128] route_46).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_47
  · exact upper_48
  · exact upper_49

def route_44 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_44 : Upper D R [18,36,264,513] 13 := by
  apply routed_branch D R [18,36,264,513] 13 (by decide) (choices 1) [32,64] route_44
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,36,264,513] (choices 1) [32,64] route_44).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_45
  · exact upper_46

def bound_53 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 38 268 536 241 225 225 225 481 737), lower := (rows 19 38 268 536 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [18,36,264,528] 13 :=
  bound_sound D R [18,36,264,528] 13 bound_53
    ((Boolean.boundCheck_true D R [18,36,264,528] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 38 268 552 209 241 209 209 465 721), lower := (rows 19 38 268 552 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [18,36,264,544] 13 :=
  bound_sound D R [18,36,264,544] 13 bound_54
    ((Boolean.boundCheck_true D R [18,36,264,544] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 38 268 584 241 241 241 241 497 753), lower := (rows 19 38 268 584 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [18,36,264,576] 13 :=
  bound_sound D R [18,36,264,576] 13 bound_55
    ((Boolean.boundCheck_true D R [18,36,264,576] 13 bound_55).mp (by decide +kernel))

def route_36 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_36 : Upper D R [18,36,264] 13 := by
  apply routed_branch D R [18,36,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_36
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,36,264] (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_36).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_37
  · exact upper_38
  · exact upper_39
  · exact upper_40
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44
  · exact upper_53
  · exact upper_54
  · exact upper_55

def bound_56 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 38 276 745 761 745 745 745 1001 745), lower := (rows 19 38 276 8 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [18,36,272] 13 :=
  bound_sound D R [18,36,272] 13 bound_56
    ((Boolean.boundCheck_true D R [18,36,272] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 38 292 729 729 761 729 729 985 729), lower := (rows 19 38 292 8 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [18,36,288] 13 :=
  bound_sound D R [18,36,288] 13 bound_57
    ((Boolean.boundCheck_true D R [18,36,288] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 38 324 761 761 761 761 761 1017 761), lower := (rows 19 38 324 8 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [18,36,320] 13 :=
  bound_sound D R [18,36,320] 13 bound_58
    ((Boolean.boundCheck_true D R [18,36,320] 13 bound_58).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 38 772 25 248 232 232 232 488 744), lower := (rows 19 38 772 25 16 32 64 128 256 512), losses := [] }

theorem upper_60 : Upper D R [18,36,768,17] 13 :=
  bound_sound D R [18,36,768,17] 13 bound_60
    ((Boolean.boundCheck_true D R [18,36,768,17] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 38 772 41 216 248 216 216 472 728), lower := (rows 19 38 772 41 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [18,36,768,33] 13 :=
  bound_sound D R [18,36,768,33] 13 bound_61
    ((Boolean.boundCheck_true D R [18,36,768,33] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 38 772 56 217 233 201 201 457 713), lower := (rows 19 38 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [18,36,768,48] 13 :=
  bound_sound D R [18,36,768,48] 13 bound_62
    ((Boolean.boundCheck_true D R [18,36,768,48] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 38 772 73 248 248 248 248 504 760), lower := (rows 19 38 772 73 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [18,36,768,65] 13 :=
  bound_sound D R [18,36,768,65] 13 bound_63
    ((Boolean.boundCheck_true D R [18,36,768,65] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 38 772 88 249 233 233 233 489 745), lower := (rows 19 38 772 88 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [18,36,768,80] 13 :=
  bound_sound D R [18,36,768,80] 13 bound_64
    ((Boolean.boundCheck_true D R [18,36,768,80] 13 bound_64).mp (by decide +kernel))

def bound_65 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 38 772 104 217 249 217 217 473 729), lower := (rows 19 38 772 104 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [18,36,768,96] 13 :=
  bound_sound D R [18,36,768,96] 13 bound_65
    ((Boolean.boundCheck_true D R [18,36,768,96] 13 bound_65).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 38 772 200 249 249 249 249 505 761), lower := (rows 19 38 772 200 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [18,36,768,192] 13 :=
  bound_sound D R [18,36,768,192] 13 bound_66
    ((Boolean.boundCheck_true D R [18,36,768,192] 13 bound_66).mp (by decide +kernel))

def route_59 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_59 : Upper D R [18,36,768] 13 := by
  apply routed_branch D R [18,36,768] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] route_59
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,36,768] (choices 2) [17,33,48,65,80,96,192] route_59).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_60
  · exact upper_61
  · exact upper_62
  · exact upper_63
  · exact upper_64
  · exact upper_65
  · exact upper_66

def route_0 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,36] 13 := by
  apply routed_branch D R [18,36] 13 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96,192,257,264,272,288,320,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,36] (choices 2) [9,17,24,33,40,48,65,72,80,96,192,257,264,272,288,320,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_18
  · exact upper_19
  · exact upper_20
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_24
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_36
  · exact upper_56
  · exact upper_57
  · exact upper_58
  · exact upper_59

theorem upper : Upper D R [18,36] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case13
