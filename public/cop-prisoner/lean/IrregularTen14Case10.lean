import IrregularTen14Base

namespace Delivery.IrregularTen14.Case10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_1 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 19 19 44 1004 1012 996 996 996 996 996), lower := (rows 19 19 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_1 : Upper D R [18,17,40] 13 :=
  bound_sound D R [18,17,40] 13 bound_1
    ((Boolean.boundCheck_true D R [18,17,40] 13 bound_1).mp (by decide +kernel))

def bound_2 : Bound 10 := { allowed := (rows 224 224 144 240 0 0 0 0 0 0), upper := (rows 19 19 100 1004 1020 1004 1004 1004 1004 1004), lower := (rows 19 19 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,17,96] 13 :=
  bound_sound D R [18,17,96] 13 bound_2
    ((Boolean.boundCheck_true D R [18,17,96] 13 bound_2).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 19 268 44 752 736 736 736 992 736), lower := (rows 19 19 268 44 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [18,17,264,36] 13 :=
  bound_sound D R [18,17,264,36] 13 bound_4
    ((Boolean.boundCheck_true D R [18,17,264,36] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 19 19 268 104 756 740 740 740 996 740), lower := (rows 19 19 268 104 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [18,17,264,96] 13 :=
  bound_sound D R [18,17,264,96] 13 bound_5
    ((Boolean.boundCheck_true D R [18,17,264,96] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 19 19 268 524 240 224 224 224 480 736), lower := (rows 19 19 268 524 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 1023 1023 0 1023 1023 1023 1023 1023), good := (rows 1007 1007 1004 1004 1004 1004 1004 1004 1004 1004) }] }

theorem upper_6 : Upper D R [18,17,264,516] 13 :=
  bound_sound D R [18,17,264,516] 13 bound_6
    ((Boolean.boundCheck_true D R [18,17,264,516] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 19 268 552 244 228 228 228 484 740), lower := (rows 19 19 268 552 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,17,264,544] 13 :=
  bound_sound D R [18,17,264,544] 13 bound_7
    ((Boolean.boundCheck_true D R [18,17,264,544] 13 bound_7).mp (by decide +kernel))

def route_3 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_3 : Upper D R [18,17,264] 13 := by
  apply routed_branch D R [18,17,264] 13 (by decide) (choices 2) [36,96,516,544] route_3
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,17,264] (choices 2) [36,96,516,544] route_3).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7

def bound_8 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 19 19 292 748 764 748 748 748 1004 748), lower := (rows 19 19 292 8 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [18,17,288] 13 :=
  bound_sound D R [18,17,288] 13 bound_8
    ((Boolean.boundCheck_true D R [18,17,288] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 19 19 772 44 248 232 232 232 488 744), lower := (rows 19 19 772 44 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [18,17,768,36] 13 :=
  bound_sound D R [18,17,768,36] 13 bound_10
    ((Boolean.boundCheck_true D R [18,17,768,36] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 224 240 144 0 0 0 0 0 0), upper := (rows 19 19 772 104 252 236 236 236 492 748), lower := (rows 19 19 772 104 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [18,17,768,96] 13 :=
  bound_sound D R [18,17,768,96] 13 bound_11
    ((Boolean.boundCheck_true D R [18,17,768,96] 13 bound_11).mp (by decide +kernel))

def route_9 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [18,17,768] 13 := by
  apply routed_branch D R [18,17,768] 13 (by decide) (choices 2) [36,96] route_9
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,17,768] (choices 2) [36,96] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_11

def route_0 : Route 10 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,17] 13 := by
  apply routed_branch D R [18,17] 13 (by decide) (choices 2) [40,96,264,288,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,17] (choices 2) [40,96,264,288,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_2
  · exact upper_3
  · exact upper_8
  · exact upper_9

theorem upper : Upper D R [18,17] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case10
