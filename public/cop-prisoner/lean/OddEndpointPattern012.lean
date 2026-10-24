import OddEndpointCertificatesSpec
import GroupedInitialMasks
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointPattern012
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
def residue : OddEndpointGraph.Case := 0
def patchAnchor : Option Int := some (5)
def frozenArena : Arena R C := arena residue patchAnchor
instance (x z : R) : Decidable (frozenArena.messenger x z) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).messenger x z))
instance (c d : C) : Decidable (frozenArena.pursuer c d) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).pursuer c d))
instance (x : R) (c : C) : Decidable (frozenArena.collision x c) :=
  inferInstanceAs (Decidable ((arena residue patchAnchor).collision x c))
theorem arena_eq : frozenArena=arena residue patchAnchor := rfl
def replyBits (r : Nat) : Nat := (if r < 45 then (if r < 22 then (if r < 11 then (if r < 5 then (if r < 2 then (if r < 1 then 0 else 0) else (if r < 3 then 0 else (if r < 4 then 0 else 0))) else (if r < 8 then (if r < 6 then 0 else (if r < 7 then 1237940039285380274899124416 else 1237940039285380274899124608)) else (if r < 9 then 131840 else (if r < 10 then 9728 else 1237940039285380274899127296)))) else (if r < 16 then (if r < 13 then (if r < 12 then 38912 else 12352) else (if r < 14 then 24832 else (if r < 15 then 8437760 else 622592))) else (if r < 19 then (if r < 17 then 197632 else (if r < 18 then 2490368 else 790528)) else (if r < 20 then 1589248 else (if r < 21 then 540016640 else 39845888))))) else (if r < 33 then (if r < 27 then (if r < 24 then (if r < 23 then 12648448 else 159383552) else (if r < 25 then 50593792 else (if r < 26 then 101711872 else 34561064960))) else (if r < 30 then (if r < 28 then 2550136832 else (if r < 29 then 809500672 else 10200547328)) else (if r < 31 then 3238002688 else (if r < 32 then 6509559808 else 2211908157440)))) else (if r < 39 then (if r < 36 then (if r < 34 then 163208757248 else (if r < 35 then 51808043008 else 652835028992)) else (if r < 37 then 207232172032 else (if r < 38 then 416611827712 else 141562122076160))) else (if r < 42 then (if r < 40 then 10445360463872 else (if r < 41 then 3315714752512 else 41781441855488)) else (if r < 43 then 13262859010048 else (if r < 44 then 26663156973568 else 9059975812874240)))))) else (if r < 68 then (if r < 56 then (if r < 50 then (if r < 47 then (if r < 46 then 668503069687808 else 212205744160768) else (if r < 48 then 2674012278751232 else (if r < 49 then 848822976643072 else 1706442046308352))) else (if r < 53 then (if r < 51 then 579838452023951360 else (if r < 52 then 42784196460019712 else 13581167626289152)) else (if r < 54 then 171136785840078848 else (if r < 55 then 54324670505156608 else 109212290963734528)))) else (if r < 62 then (if r < 59 then (if r < 57 then 37109660929532887040 else (if r < 58 then 2738188573441261568 else 869194728082505728)) else (if r < 60 then 10952754293765046272 else (if r < 61 then 3476778912330022912 else 6989586621679009792))) else (if r < 65 then (if r < 63 then 2375018299490104770560 else (if r < 64 then 175244068700240740352 else 55628462597280366592)) else (if r < 66 then 700976274800962961408 else (if r < 67 then 222513850389121466368 else 447333543787456626688))))) else (if r < 79 then (if r < 73 then (if r < 70 then (if r < 69 then 152001171167366705315840 else 11215620396815407382528) else (if r < 71 then 3560221606225943461888 else (if r < 72 then 44862481587261629530112 else 4796153459164483420160))) else (if r < 76 then (if r < 74 then 28629346802397224108032 else (if r < 75 then 9728074954711469140213760 else 717799705396186072481792)) else (if r < 77 then 227854182798460381560832 else (if r < 78 then 2871198821584744289927168 else 911416731193841526243328)))) else (if r < 85 then (if r < 82 then (if r < 80 then 1832278195353422342914048 else (if r < 81 then 1241566816744224162423242752 else 1245193594203068049947361280)) else (if r < 83 then 14582667699101464419893248 else (if r < 84 then 1247611445842297308296773632 else 0))) else (if r < 88 then (if r < 86 then 0 else (if r < 87 then 0 else 0)) else (if r < 89 then 0 else (if r < 90 then 0 else 1257278130032731472049471424)))))))
def replyMasks (c : C) : Nat := replyBits c.val
def collisionBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 3 then 2475880078570760549798248447 else 2475880078570760549798248447)) else (if r < 6 then (if r < 5 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 7 then 262144 else 524288))) else (if r < 12 then (if r < 10 then (if r < 9 then 1048576 else 2097152) else (if r < 11 then 4194304 else 8388608)) else (if r < 14 then (if r < 13 then 16777216 else 33554432) else (if r < 15 then 67108864 else 134217728)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 268435456 else 536870912) else (if r < 19 then 1073741824 else 2147483648)) else (if r < 22 then (if r < 21 then 4294967296 else 8589934592) else (if r < 23 then 17179869184 else 34359738368))) else (if r < 28 then (if r < 26 then (if r < 25 then 68719476736 else 137438953472) else (if r < 27 then 274877906944 else 549755813888)) else (if r < 30 then (if r < 29 then 1099511627776 else 2199023255552) else (if r < 31 then 4398046511104 else (if r < 32 then 8796093022208 else 17592186044416)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 35184372088832 else 70368744177664) else (if r < 36 then 140737488355328 else 281474976710656)) else (if r < 39 then (if r < 38 then 562949953421312 else 1125899906842624) else (if r < 40 then 2251799813685248 else 4503599627370496))) else (if r < 45 then (if r < 43 then (if r < 42 then 9007199254740992 else 18014398509481984) else (if r < 44 then 36028797018963968 else 72057594037927936)) else (if r < 47 then (if r < 46 then 144115188075855872 else 288230376151711744) else (if r < 48 then 576460752303423488 else 1152921504606846976)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 2305843009213693952 else 4611686018427387904) else (if r < 52 then 9223372036854775808 else 18446744073709551616)) else (if r < 55 then (if r < 54 then 36893488147419103232 else 73786976294838206464) else (if r < 56 then 147573952589676412928 else 295147905179352825856))) else (if r < 61 then (if r < 59 then (if r < 58 then 590295810358705651712 else 1180591620717411303424) else (if r < 60 then 2361183241434822606848 else 2475880078570760549798248447)) else (if r < 63 then (if r < 62 then 2475880078570760549798248447 else 2475880078570760549798248447) else (if r < 64 then 2475880078570760549798248447 else (if r < 65 then 2475880078570760549798248447 else 2475880078570760549798248447)))))))
def collisionMasks (x : R) : Nat := collisionBits x.val
def requiredBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 0 else 0) else (if r < 3 then 0 else 0)) else (if r < 6 then (if r < 5 then 0 else 0) else (if r < 7 then 1257282852399214341694160832 else 1257282852399214341693898688))) else (if r < 12 then (if r < 10 then (if r < 9 then 1257282852399214341693374400 else 1257282852399214341692325824) else (if r < 11 then 1257282852399214341690228672 else 1257282852399214341686034368)) else (if r < 14 then (if r < 13 then 1257282852399214341677645760 else 1257282852399214341660868544) else (if r < 15 then 1257282852399214341627314112 else 1257282852399214341560205248)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 1257282852399214341425987520 else 1257282852399214341157552064) else (if r < 19 then 1257282852399214340620681152 else 1257282852399214339546939328)) else (if r < 22 then (if r < 21 then 1257282852399214337399455680 else 1257282852399214333104488384) else (if r < 23 then 1257282852399214324514553792 else 1257282852399214307334684608))) else (if r < 28 then (if r < 26 then (if r < 25 then 1257282852399214272974946240 else 1257282852399214204255469504) else (if r < 27 then 1257282852399214066816516032 else 1257282852399213791938609088)) else (if r < 30 then (if r < 29 then 1257282852399213242182795200 else 1257282852399212142671167424) else (if r < 31 then 1257282852399209943647911872 else (if r < 32 then 1257282852399205545601400768 else 1257282852399196749508378560)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 1257282852399179157322334144 else 1257282852399143972950245312) else (if r < 36 then 1257282852399073604206067648 else 1257282852398932866717712320)) else (if r < 39 then (if r < 38 then 1257282852398651391741001664 else 1257282852398088441787580352) else (if r < 40 then 1257282852396962541880737728 else 1257282852394710742067052480))) else (if r < 45 then (if r < 43 then (if r < 42 then 1257282852390207142439681984 else 1257282852381199943184940992) else (if r < 44 then 1257282852363185544675459008 else 1257282852327156747656495040)) else (if r < 47 then (if r < 46 then 1257282852255099153618567104 else 1257282852110983965542711232) else (if r < 48 then 1257282851822753589390999488 else 1257282851246292837087576000)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 1257282850093371332480729024 else 1257282847787528323267035072) else (if r < 52 then 1257282843175842304839647168 else 1257282833952470267984871360)) else (if r < 55 then (if r < 54 then 1257282815505726194275319744 else 1257282778612238046856216512) else (if r < 56 then 1257282704825261752018010048 else 1257282557251309162341597120))) else (if r < 61 then (if r < 59 then (if r < 58 then 1257282262103403982988771264 else 1257281671807593624283119552) else (if r < 60 then 1257280491215972906871816128 else 0)) else (if r < 63 then (if r < 62 then 0 else 0) else (if r < 64 then 0 else (if r < 65 then 0 else 0)))))))
def requiredMasks (x : R) : Nat := requiredBits x.val
def validMask : Nat := 1257282852399214341694422976
theorem reply_cases : ∀ c, presentC residue patchAnchor c →
    if c=outside then ∀ d, presentC residue patchAnchor d →
      (d=outside ∨ boundary residue d) → Has (replyMasks c) d
    else Has (replyMasks c) c ∧ ∀ b : Bool, permitted residue patchAnchor (cvertex c) b →
      Has (replyMasks c) (pack residue (next residue patchAnchor b (cvertex c))) := by
  unfold Has
  decide +kernel
theorem reply_coverage : ∀ c d, frozenArena.pursuer c d → Has (replyMasks c) d := by
  intro c d move
  obtain ⟨pc,pd,step⟩ := move
  have covered := reply_cases c pc
  by_cases out : c=outside
  · rw [if_pos out] at step covered
    exact covered d pd step
  · rw [if_neg out] at step covered
    rcases step with wait|⟨b,allowed,same⟩
    · simpa only [wait] using covered.1
    · rw [same]
      exact covered.2 b allowed
theorem collision_rows : ∀ x,
    (presentR residue patchAnchor x → Has (collisionMasks x) (pack residue (rvertex x))) ∧
    (¬presentR residue patchAnchor x → collisionMasks x=2^91-1) := by
  unfold Has
  decide +kernel
theorem collision_coverage : ∀ x c, frozenArena.collision x c → Has (collisionMasks x) c :=
  GroupedInitialMasks.collision_coverage (presentR residue patchAnchor)
    (fun x => pack residue (rvertex x)) collisionMasks collision_rows
theorem valid_bits : ∀ c, presentC residue patchAnchor c → Has validMask c := by
  unfold Has
  decide +kernel
theorem required_rows : ∀ x, presentR residue patchAnchor x →
    requiredMasks x=validMask ^^^ 2^(pack residue (rvertex x)).val := by
  decide +kernel
theorem required_coverage : ∀ x c, presentR residue patchAnchor x → presentC residue patchAnchor c →
    ¬(arena residue patchAnchor).collision x c → Has (requiredMasks x) c :=
  GroupedInitialMasks.required_coverage (presentR residue patchAnchor) (presentC residue patchAnchor)
    (fun x => pack residue (rvertex x)) validMask requiredMasks valid_bits required_rows
#print axioms arena_eq
#print axioms required_coverage
end Delivery.OddEndpointPattern012
