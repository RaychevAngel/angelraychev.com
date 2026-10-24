import IrregularTen14Base

namespace Delivery.IrregularTen14.Case20
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 240 224 0 0 0 0 0 0), upper := (rows 19 770 13 28 240 224 224 224 480 736), lower := (rows 19 770 13 28 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 1023 4 8 0 1023 1023 1023 1023 1023), good := (rows 995 994 1007 1006 994 994 994 994 994 994) }] }

theorem upper_2 : Upper D R [18,768,9,20] 13 :=
  bound_sound D R [18,768,9,20] 13 bound_2
    ((Boolean.boundCheck_true D R [18,768,9,20] 13 bound_2).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 19 770 13 44 48 240 208 208 464 720), lower := (rows 19 770 13 44 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 23 4 8 16 0 81 145 273 529), good := (rows 979 770 975 14 979 0 64 128 256 512) }] }

theorem upper_4 : Upper D R [18,768,9,36,32] 13 :=
  bound_sound D R [18,768,9,36,32] 13 bound_4
    ((Boolean.boundCheck_true D R [18,768,9,36,32] 13 bound_4).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 770 13 44 80 48 224 224 480 736), lower := (rows 19 770 13 44 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 46 4 8 0 32 104 168 296 552), good := (rows 3 770 975 1006 64 994 64 128 256 512) }] }

theorem upper_6 : Upper D R [18,768,9,36,64,16] 13 :=
  bound_sound D R [18,768,9,36,64,16] 13 bound_6
    ((Boolean.boundCheck_true D R [18,768,9,36,64,16] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 770 13 44 80 96 240 176 432 688), lower := (rows 19 770 13 44 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 9 0 112 64 128 256 512), good := (rows 47 770 13 44 96 96 96 128 256 512) }] }

theorem upper_7 : Upper D R [18,768,9,36,64,64] 13 :=
  bound_sound D R [18,768,9,36,64,64] 13 bound_7
    ((Boolean.boundCheck_true D R [18,768,9,36,64,64] 13 bound_7).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 770 13 44 80 160 80 224 480 736), lower := (rows 19 770 13 44 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 83 5 13 0 241 64 208 336 592), good := (rows 943 770 47 44 994 160 994 160 256 512) }] }

theorem upper_9 : Upper D R [18,768,9,36,64,128,16] 13 :=
  bound_sound D R [18,768,9,36,64,128,16] 13 bound_9
    ((Boolean.boundCheck_true D R [18,768,9,36,64,128,16] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 19 770 13 44 80 160 96 208 464 720), lower := (rows 19 770 13 44 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 83 4 8 80 0 64 208 336 592), good := (rows 915 770 15 12 979 128 979 128 256 512) }] }

theorem upper_10 : Upper D R [18,768,9,36,64,128,32] 13 :=
  bound_sound D R [18,768,9,36,64,128,32] 13 bound_10
    ((Boolean.boundCheck_true D R [18,768,9,36,64,128,32] 13 bound_10).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 770 13 44 80 160 192 144 352 608), lower := (rows 19 770 13 44 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 255 4 8 0 224 224 128 504 760), good := (rows 771 770 783 878 866 994 994 994 256 512) }] }

theorem upper_12 : Upper D R [18,768,9,36,64,128,128,16] 13 :=
  bound_sound D R [18,768,9,36,64,128,128,16] 13 bound_12
    ((Boolean.boundCheck_true D R [18,768,9,36,64,128,128,16] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 770 13 44 80 160 192 160 336 592), lower := (rows 19 770 13 44 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 5 13 0 1023 1023 1023 256 512), good := (rows 239 994 237 236 224 224 224 224 480 736) }] }

theorem upper_13 : Upper D R [18,768,9,36,64,128,128,32] 13 :=
  bound_sound D R [18,768,9,36,64,128,128,32] 13 bound_13
    ((Boolean.boundCheck_true D R [18,768,9,36,64,128,128,32] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 770 13 44 80 160 192 192 304 560), lower := (rows 19 770 13 44 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 5 13 0 1023 1023 1023 256 512), good := (rows 239 994 237 236 224 224 224 224 480 736) }] }

theorem upper_14 : Upper D R [18,768,9,36,64,128,128,64] 13 :=
  bound_sound D R [18,768,9,36,64,128,128,64] 13 bound_14
    ((Boolean.boundCheck_true D R [18,768,9,36,64,128,128,64] 13 bound_14).mp (by decide +kernel))

def route_11 : Route 10 := (fun mask => (mask,id))

theorem upper_11 : Upper D R [18,768,9,36,64,128,128] 13 := by
  apply routed_branch D R [18,768,9,36,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_11
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,9,36,64,128,128] (choices 1) [16,32,64] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_12
  · exact upper_13
  · exact upper_14

def route_8 : Route 10 := (fun mask => (mask,id))

theorem upper_8 : Upper D R [18,768,9,36,64,128] 13 := by
  apply routed_branch D R [18,768,9,36,64,128] 13 (by decide) (choices 1) [16,32,128] route_8
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,9,36,64,128] (choices 1) [16,32,128] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_9
  · exact upper_10
  · exact upper_11

def route_5 : Route 10 := (fun mask => (mask,id))

theorem upper_5 : Upper D R [18,768,9,36,64] 13 := by
  apply routed_branch D R [18,768,9,36,64] 13 (by decide) (choices 1) [16,64,128] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,9,36,64] (choices 1) [16,64,128] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_6
  · exact upper_7
  · exact upper_8

def route_3 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_3 : Upper D R [18,768,9,36] 13 := by
  apply routed_branch D R [18,768,9,36] 13 (by decide) (choices 1) [32,64] route_3
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,9,36] (choices 1) [32,64] route_3).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_4
  · exact upper_5

def bound_15 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 770 13 56 244 228 228 228 484 740), lower := (rows 19 770 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [18,768,9,48] 13 :=
  bound_sound D R [18,768,9,48] 13 bound_15
    ((Boolean.boundCheck_true D R [18,768,9,48] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 19 770 13 104 244 244 244 244 500 756), lower := (rows 19 770 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [18,768,9,96] 13 :=
  bound_sound D R [18,768,9,96] 13 bound_16
    ((Boolean.boundCheck_true D R [18,768,9,96] 13 bound_16).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [18,768,9] 13 := by
  apply routed_branch D R [18,768,9] 13 (by decide) (choices 2) [20,36,48,96] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,768,9] (choices 2) [20,36,48,96] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_15
  · exact upper_16

def bound_18 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 770 21 44 248 232 232 232 488 744), lower := (rows 19 770 21 44 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [18,768,17,36] 13 :=
  bound_sound D R [18,768,17,36] 13 bound_18
    ((Boolean.boundCheck_true D R [18,768,17,36] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 770 21 104 252 236 236 236 492 748), lower := (rows 19 770 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [18,768,17,96] 13 :=
  bound_sound D R [18,768,17,96] 13 bound_19
    ((Boolean.boundCheck_true D R [18,768,17,96] 13 bound_19).mp (by decide +kernel))

def route_17 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_17 : Upper D R [18,768,17] 13 := by
  apply routed_branch D R [18,768,17] 13 (by decide) (choices 2) [36,96] route_17
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,768,17] (choices 2) [36,96] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_18
  · exact upper_19

def bound_21 : Bound 10 := { allowed := (rows 224 224 224 240 0 0 0 0 0 0), upper := (rows 19 770 28 13 240 224 224 224 480 736), lower := (rows 19 770 28 13 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 1023 4 8 0 1023 1023 1023 1023 1023), good := (rows 995 994 1006 1007 994 994 994 994 994 994) }] }

theorem upper_21 : Upper D R [18,768,24,5] 13 :=
  bound_sound D R [18,768,24,5] 13 bound_21
    ((Boolean.boundCheck_true D R [18,768,24,5] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 770 28 41 244 228 228 228 484 740), lower := (rows 19 770 28 41 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [18,768,24,33] 13 :=
  bound_sound D R [18,768,24,33] 13 bound_22
    ((Boolean.boundCheck_true D R [18,768,24,33] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 770 28 44 241 225 225 225 481 737), lower := (rows 19 770 28 44 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [18,768,24,36] 13 :=
  bound_sound D R [18,768,24,36] 13 bound_23
    ((Boolean.boundCheck_true D R [18,768,24,36] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 770 28 104 245 229 229 229 485 741), lower := (rows 19 770 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [18,768,24,96] 13 :=
  bound_sound D R [18,768,24,96] 13 bound_24
    ((Boolean.boundCheck_true D R [18,768,24,96] 13 bound_24).mp (by decide +kernel))

def route_20 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_20 : Upper D R [18,768,24] 13 := by
  apply routed_branch D R [18,768,24] 13 (by decide) (choices 2) [5,33,36,96] route_20
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,768,24] (choices 2) [5,33,36,96] route_20).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_24

def bound_26 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 770 37 28 248 232 232 232 488 744), lower := (rows 19 770 37 28 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [18,768,33,20] 13 :=
  bound_sound D R [18,768,33,20] 13 bound_26
    ((Boolean.boundCheck_true D R [18,768,33,20] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 770 37 44 216 248 216 216 472 728), lower := (rows 19 770 37 44 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [18,768,33,36] 13 :=
  bound_sound D R [18,768,33,36] 13 bound_27
    ((Boolean.boundCheck_true D R [18,768,33,36] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 770 37 56 220 236 204 204 460 716), lower := (rows 19 770 37 56 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [18,768,33,48] 13 :=
  bound_sound D R [18,768,33,48] 13 bound_28
    ((Boolean.boundCheck_true D R [18,768,33,48] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 770 37 76 248 248 248 248 504 760), lower := (rows 19 770 37 76 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [18,768,33,68] 13 :=
  bound_sound D R [18,768,33,68] 13 bound_29
    ((Boolean.boundCheck_true D R [18,768,33,68] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 770 37 88 252 236 236 236 492 748), lower := (rows 19 770 37 88 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [18,768,33,80] 13 :=
  bound_sound D R [18,768,33,80] 13 bound_30
    ((Boolean.boundCheck_true D R [18,768,33,80] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 770 37 104 220 252 220 220 476 732), lower := (rows 19 770 37 104 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [18,768,33,96] 13 :=
  bound_sound D R [18,768,33,96] 13 bound_31
    ((Boolean.boundCheck_true D R [18,768,33,96] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 770 37 200 252 252 252 252 508 764), lower := (rows 19 770 37 200 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [18,768,33,192] 13 :=
  bound_sound D R [18,768,33,192] 13 bound_32
    ((Boolean.boundCheck_true D R [18,768,33,192] 13 bound_32).mp (by decide +kernel))

def route_25 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_25 : Upper D R [18,768,33] 13 := by
  apply routed_branch D R [18,768,33] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_25
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,768,33] (choices 2) [20,36,48,68,80,96,192] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_32

def bound_35 : Bound 10 := { allowed := (rows 192 208 208 240 0 0 0 0 0 0), upper := (rows 19 770 44 13 48 240 208 208 464 720), lower := (rows 19 770 44 13 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 27 4 8 16 0 81 145 273 529), good := (rows 979 770 14 975 979 0 64 128 256 512) }] }

theorem upper_35 : Upper D R [18,768,40,5,32] 13 :=
  bound_sound D R [18,768,40,5,32] 13 bound_35
    ((Boolean.boundCheck_true D R [18,768,40,5,32] 13 bound_35).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 19 770 44 13 80 48 224 224 480 736), lower := (rows 19 770 44 13 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 46 4 8 0 32 100 164 292 548), good := (rows 3 770 1006 975 64 994 64 128 256 512) }] }

theorem upper_37 : Upper D R [18,768,40,5,64,16] 13 :=
  bound_sound D R [18,768,40,5,64,16] 13 bound_37
    ((Boolean.boundCheck_true D R [18,768,40,5,64,16] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 770 44 13 80 96 240 176 432 688), lower := (rows 19 770 44 13 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 9 0 112 64 128 256 512), good := (rows 47 770 44 13 96 96 96 128 256 512) }] }

theorem upper_38 : Upper D R [18,768,40,5,64,64] 13 :=
  bound_sound D R [18,768,40,5,64,64] 13 bound_38
    ((Boolean.boundCheck_true D R [18,768,40,5,64,64] 13 bound_38).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 770 44 13 80 160 80 224 480 736), lower := (rows 19 770 44 13 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 83 13 9 0 241 64 208 336 592), good := (rows 943 770 44 47 994 160 994 160 256 512) }] }

theorem upper_40 : Upper D R [18,768,40,5,64,128,16] 13 :=
  bound_sound D R [18,768,40,5,64,128,16] 13 bound_40
    ((Boolean.boundCheck_true D R [18,768,40,5,64,128,16] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 192 208 208 240 0 0 0 0 0 0), upper := (rows 19 770 44 13 80 160 96 208 464 720), lower := (rows 19 770 44 13 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 83 4 8 80 0 64 208 336 592), good := (rows 915 770 12 15 979 128 979 128 256 512) }] }

theorem upper_41 : Upper D R [18,768,40,5,64,128,32] 13 :=
  bound_sound D R [18,768,40,5,64,128,32] 13 bound_41
    ((Boolean.boundCheck_true D R [18,768,40,5,64,128,32] 13 bound_41).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 19 770 44 13 80 160 192 144 352 608), lower := (rows 19 770 44 13 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 255 4 8 0 224 224 128 500 756), good := (rows 771 770 878 783 866 994 994 994 256 512) }] }

theorem upper_43 : Upper D R [18,768,40,5,64,128,128,16] 13 :=
  bound_sound D R [18,768,40,5,64,128,128,16] 13 bound_43
    ((Boolean.boundCheck_true D R [18,768,40,5,64,128,128,16] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 770 44 13 80 160 192 160 336 592), lower := (rows 19 770 44 13 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 13 9 0 1023 1023 1023 256 512), good := (rows 239 994 236 237 224 224 224 224 480 736) }] }

theorem upper_44 : Upper D R [18,768,40,5,64,128,128,32] 13 :=
  bound_sound D R [18,768,40,5,64,128,128,32] 13 bound_44
    ((Boolean.boundCheck_true D R [18,768,40,5,64,128,128,32] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 770 44 13 80 160 192 192 304 560), lower := (rows 19 770 44 13 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 13 9 0 1023 1023 1023 256 512), good := (rows 239 994 236 237 224 224 224 224 480 736) }] }

theorem upper_45 : Upper D R [18,768,40,5,64,128,128,64] 13 :=
  bound_sound D R [18,768,40,5,64,128,128,64] 13 bound_45
    ((Boolean.boundCheck_true D R [18,768,40,5,64,128,128,64] 13 bound_45).mp (by decide +kernel))

def route_42 : Route 10 := (fun mask => (mask,id))

theorem upper_42 : Upper D R [18,768,40,5,64,128,128] 13 := by
  apply routed_branch D R [18,768,40,5,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_42
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,40,5,64,128,128] (choices 1) [16,32,64] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45

def route_39 : Route 10 := (fun mask => (mask,id))

theorem upper_39 : Upper D R [18,768,40,5,64,128] 13 := by
  apply routed_branch D R [18,768,40,5,64,128] 13 (by decide) (choices 1) [16,32,128] route_39
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,40,5,64,128] (choices 1) [16,32,128] route_39).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_40
  · exact upper_41
  · exact upper_42

def route_36 : Route 10 := (fun mask => (mask,id))

theorem upper_36 : Upper D R [18,768,40,5,64] 13 := by
  apply routed_branch D R [18,768,40,5,64] 13 (by decide) (choices 1) [16,64,128] route_36
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,40,5,64] (choices 1) [16,64,128] route_36).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_37
  · exact upper_38
  · exact upper_39

def route_34 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_34 : Upper D R [18,768,40,5] 13 := by
  apply routed_branch D R [18,768,40,5] 13 (by decide) (choices 1) [32,64] route_34
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,768,40,5] (choices 1) [32,64] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_35
  · exact upper_36

def bound_46 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 770 44 25 244 228 228 228 484 740), lower := (rows 19 770 44 25 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [18,768,40,17] 13 :=
  bound_sound D R [18,768,40,17] 13 bound_46
    ((Boolean.boundCheck_true D R [18,768,40,17] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 770 44 28 241 225 225 225 481 737), lower := (rows 19 770 44 28 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [18,768,40,20] 13 :=
  bound_sound D R [18,768,40,20] 13 bound_47
    ((Boolean.boundCheck_true D R [18,768,40,20] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 770 44 41 212 244 212 212 468 724), lower := (rows 19 770 44 41 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [18,768,40,33] 13 :=
  bound_sound D R [18,768,40,33] 13 bound_48
    ((Boolean.boundCheck_true D R [18,768,40,33] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 770 44 44 209 241 209 209 465 721), lower := (rows 19 770 44 44 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [18,768,40,36] 13 :=
  bound_sound D R [18,768,40,36] 13 bound_49
    ((Boolean.boundCheck_true D R [18,768,40,36] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 770 44 56 213 229 197 197 453 709), lower := (rows 19 770 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [18,768,40,48] 13 :=
  bound_sound D R [18,768,40,48] 13 bound_50
    ((Boolean.boundCheck_true D R [18,768,40,48] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 770 44 73 244 244 244 244 500 756), lower := (rows 19 770 44 73 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [18,768,40,65] 13 :=
  bound_sound D R [18,768,40,65] 13 bound_51
    ((Boolean.boundCheck_true D R [18,768,40,65] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 770 44 76 241 241 241 241 497 753), lower := (rows 19 770 44 76 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [18,768,40,68] 13 :=
  bound_sound D R [18,768,40,68] 13 bound_52
    ((Boolean.boundCheck_true D R [18,768,40,68] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 770 44 88 245 229 229 229 485 741), lower := (rows 19 770 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [18,768,40,80] 13 :=
  bound_sound D R [18,768,40,80] 13 bound_53
    ((Boolean.boundCheck_true D R [18,768,40,80] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 770 44 104 213 245 213 213 469 725), lower := (rows 19 770 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [18,768,40,96] 13 :=
  bound_sound D R [18,768,40,96] 13 bound_54
    ((Boolean.boundCheck_true D R [18,768,40,96] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 770 44 200 245 245 245 245 501 757), lower := (rows 19 770 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [18,768,40,192] 13 :=
  bound_sound D R [18,768,40,192] 13 bound_55
    ((Boolean.boundCheck_true D R [18,768,40,192] 13 bound_55).mp (by decide +kernel))

def route_33 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_33 : Upper D R [18,768,40] 13 := by
  apply routed_branch D R [18,768,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_33
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,768,40] (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_33).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_34
  · exact upper_46
  · exact upper_47
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_54
  · exact upper_55

def bound_56 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 770 52 237 253 237 237 237 493 749), lower := (rows 19 770 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [18,768,48] 13 :=
  bound_sound D R [18,768,48] 13 bound_56
    ((Boolean.boundCheck_true D R [18,768,48] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 224 240 144 240 0 0 0 0 0 0), upper := (rows 19 770 100 253 253 253 253 253 509 765), lower := (rows 19 770 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [18,768,96] 13 :=
  bound_sound D R [18,768,96] 13 bound_57
    ((Boolean.boundCheck_true D R [18,768,96] 13 bound_57).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,768] 13 := by
  apply routed_branch D R [18,768] 13 (by decide) (choices 2) [9,17,24,33,40,48,96] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,768] (choices 2) [9,17,24,33,40,48,96] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_17
  · exact upper_20
  · exact upper_25
  · exact upper_33
  · exact upper_56
  · exact upper_57

theorem upper : Upper D R [18,768] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case20
