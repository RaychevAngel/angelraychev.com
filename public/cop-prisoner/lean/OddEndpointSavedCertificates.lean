import OddEndpointCertificate000
import OddEndpointCertificate001
import OddEndpointCertificate002
import OddEndpointCertificate003
import OddEndpointCertificate004
import OddEndpointCertificate005
import OddEndpointCertificate006
import OddEndpointCertificate007
import OddEndpointCertificate008
import OddEndpointCertificate009
import OddEndpointCertificate010
import OddEndpointCertificate011
import OddEndpointCertificate012
import OddEndpointCertificate013
import OddEndpointCertificate014
import OddEndpointCertificate015
import OddEndpointCertificate016
import OddEndpointCertificate017
import OddEndpointCertificate018
import OddEndpointCertificate019
import OddEndpointCertificate020
import OddEndpointCertificate021
import OddEndpointCertificate022
import OddEndpointCertificate023
import OddEndpointCertificate024
import OddEndpointCertificate025
import OddEndpointCertificate026
import OddEndpointCertificate027
import OddEndpointCertificate028
import OddEndpointCertificate029
import OddEndpointCertificate030
import OddEndpointCertificate031
import OddEndpointCertificate032
import OddEndpointCertificate033
import OddEndpointCertificate034
import OddEndpointCertificate035
import OddEndpointCertificate036
import OddEndpointCertificate037
import OddEndpointCertificate038
import OddEndpointCertificate039
import OddEndpointCertificate040
import OddEndpointCertificate041
import OddEndpointCertificate042
import OddEndpointCertificate043
import OddEndpointCertificate044
import OddEndpointCertificate045
import OddEndpointCertificate046
import OddEndpointCertificate047
import OddEndpointCertificate048
import OddEndpointCertificate049
import OddEndpointCertificate050
import OddEndpointCertificate051
import OddEndpointCertificate052
import OddEndpointCertificate053
import OddEndpointCertificate054
import OddEndpointCertificate055
import OddEndpointCertificate056
import OddEndpointCertificate057
import OddEndpointCertificate058
import OddEndpointCertificate059
import OddEndpointCertificate060
import OddEndpointCertificate061
import OddEndpointCertificate062
import OddEndpointCertificate063
import OddEndpointCertificate064
import OddEndpointCertificate065
import OddEndpointCertificate066
import OddEndpointCertificate067
import OddEndpointCertificate068
import OddEndpointCertificate069
import OddEndpointCertificate070
import OddEndpointCertificate071
import OddEndpointCertificate072
import OddEndpointCertificate073
import OddEndpointCertificate074
import OddEndpointCertificate075
import OddEndpointCertificate076
import OddEndpointCertificate077
import OddEndpointCertificate078
import OddEndpointCertificate079
import OddEndpointCertificate080
import OddEndpointCertificate081
import OddEndpointCertificate082
import OddEndpointCertificate083
import OddEndpointCertificate084
import OddEndpointCertificate085
import OddEndpointCertificate086
import OddEndpointCertificate087
import OddEndpointCertificate088
import OddEndpointCertificate089
import OddEndpointCertificate090
import OddEndpointCertificate091
import OddEndpointCertificate092
import OddEndpointCertificate093
import OddEndpointCertificate094
import OddEndpointCertificate095
import OddEndpointCertificate096
import OddEndpointCertificate097
import OddEndpointCertificate098
import OddEndpointCertificate099
import OddEndpointCertificate100
import OddEndpointCertificate101
import OddEndpointCertificate102
import OddEndpointCertificate103
import OddEndpointCertificate104
import OddEndpointCertificate105
import OddEndpointCertificate106
import OddEndpointCertificate107
import OddEndpointCertificate108
import OddEndpointCertificate109
import OddEndpointCertificate110
import OddEndpointCertificate111
import OddEndpointCertificate112
import OddEndpointCertificate113
import OddEndpointCertificate114
import OddEndpointCertificate115
import OddEndpointCertificate116
import OddEndpointCertificate117
import OddEndpointCertificate118
import OddEndpointCertificate119
import OddEndpointCertificate120
import OddEndpointCertificate121
import OddEndpointCertificate122
import OddEndpointCertificate123
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointSavedCertificates
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
noncomputable def certificates (r : OddEndpointGraph.Case) (a : Option Int)
    (allowed : Catalogued r a) : Certificates r a := by
  apply Classical.choice
  have cases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by
    have finite : ∀ r : Fin 6, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by decide +kernel
    exact finite r
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · cases a with
    | none => exact ⟨OddEndpointCertificate000.certificates⟩
    | some h =>
      have cases : h=(-6) ∨ h=(-5) ∨ h=(-4) ∨ h=(-3) ∨ h=(-2) ∨ h=(-1) ∨ h=(0) ∨ h=(1) ∨ h=(2) ∨ h=(3) ∨ h=(4) ∨ h=(5) ∨ h=(6) := by
        change -6≤h ∧ h≤6 at allowed
        omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨OddEndpointCertificate001.certificates⟩
      · exact ⟨OddEndpointCertificate002.certificates⟩
      · exact ⟨OddEndpointCertificate003.certificates⟩
      · exact ⟨OddEndpointCertificate004.certificates⟩
      · exact ⟨OddEndpointCertificate005.certificates⟩
      · exact ⟨OddEndpointCertificate006.certificates⟩
      · exact ⟨OddEndpointCertificate007.certificates⟩
      · exact ⟨OddEndpointCertificate008.certificates⟩
      · exact ⟨OddEndpointCertificate009.certificates⟩
      · exact ⟨OddEndpointCertificate010.certificates⟩
      · exact ⟨OddEndpointCertificate011.certificates⟩
      · exact ⟨OddEndpointCertificate012.certificates⟩
      · exact ⟨OddEndpointCertificate013.certificates⟩
  · cases a with
    | none => exact ⟨OddEndpointCertificate014.certificates⟩
    | some h =>
      have cases : h=(-10) ∨ h=(-9) ∨ h=(-8) ∨ h=(-7) ∨ h=(-6) ∨ h=(-5) ∨ h=(-4) ∨ h=(-3) ∨ h=(-2) ∨ h=(-1) ∨ h=(0) ∨ h=(1) ∨ h=(2) ∨ h=(3) ∨ h=(4) ∨ h=(5) ∨ h=(6) ∨ h=(7) ∨ h=(8) ∨ h=(9) ∨ h=(10) := by
        change -10≤h ∧ h≤10 at allowed
        omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨OddEndpointCertificate015.certificates⟩
      · exact ⟨OddEndpointCertificate016.certificates⟩
      · exact ⟨OddEndpointCertificate017.certificates⟩
      · exact ⟨OddEndpointCertificate018.certificates⟩
      · exact ⟨OddEndpointCertificate019.certificates⟩
      · exact ⟨OddEndpointCertificate020.certificates⟩
      · exact ⟨OddEndpointCertificate021.certificates⟩
      · exact ⟨OddEndpointCertificate022.certificates⟩
      · exact ⟨OddEndpointCertificate023.certificates⟩
      · exact ⟨OddEndpointCertificate024.certificates⟩
      · exact ⟨OddEndpointCertificate025.certificates⟩
      · exact ⟨OddEndpointCertificate026.certificates⟩
      · exact ⟨OddEndpointCertificate027.certificates⟩
      · exact ⟨OddEndpointCertificate028.certificates⟩
      · exact ⟨OddEndpointCertificate029.certificates⟩
      · exact ⟨OddEndpointCertificate030.certificates⟩
      · exact ⟨OddEndpointCertificate031.certificates⟩
      · exact ⟨OddEndpointCertificate032.certificates⟩
      · exact ⟨OddEndpointCertificate033.certificates⟩
      · exact ⟨OddEndpointCertificate034.certificates⟩
      · exact ⟨OddEndpointCertificate035.certificates⟩
  · cases a with
    | none => exact ⟨OddEndpointCertificate036.certificates⟩
    | some h =>
      have cases : h=(-10) ∨ h=(-9) ∨ h=(-8) ∨ h=(-7) ∨ h=(-6) ∨ h=(-5) ∨ h=(-4) ∨ h=(-3) ∨ h=(-2) ∨ h=(-1) ∨ h=(0) ∨ h=(1) ∨ h=(2) ∨ h=(3) ∨ h=(4) ∨ h=(5) ∨ h=(6) ∨ h=(7) ∨ h=(8) ∨ h=(9) ∨ h=(10) := by
        change -10≤h ∧ h≤10 at allowed
        omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨OddEndpointCertificate037.certificates⟩
      · exact ⟨OddEndpointCertificate038.certificates⟩
      · exact ⟨OddEndpointCertificate039.certificates⟩
      · exact ⟨OddEndpointCertificate040.certificates⟩
      · exact ⟨OddEndpointCertificate041.certificates⟩
      · exact ⟨OddEndpointCertificate042.certificates⟩
      · exact ⟨OddEndpointCertificate043.certificates⟩
      · exact ⟨OddEndpointCertificate044.certificates⟩
      · exact ⟨OddEndpointCertificate045.certificates⟩
      · exact ⟨OddEndpointCertificate046.certificates⟩
      · exact ⟨OddEndpointCertificate047.certificates⟩
      · exact ⟨OddEndpointCertificate048.certificates⟩
      · exact ⟨OddEndpointCertificate049.certificates⟩
      · exact ⟨OddEndpointCertificate050.certificates⟩
      · exact ⟨OddEndpointCertificate051.certificates⟩
      · exact ⟨OddEndpointCertificate052.certificates⟩
      · exact ⟨OddEndpointCertificate053.certificates⟩
      · exact ⟨OddEndpointCertificate054.certificates⟩
      · exact ⟨OddEndpointCertificate055.certificates⟩
      · exact ⟨OddEndpointCertificate056.certificates⟩
      · exact ⟨OddEndpointCertificate057.certificates⟩
  · cases a with
    | none => exact ⟨OddEndpointCertificate058.certificates⟩
    | some h =>
      have cases : h=(-10) ∨ h=(-9) ∨ h=(-8) ∨ h=(-7) ∨ h=(-6) ∨ h=(-5) ∨ h=(-4) ∨ h=(-3) ∨ h=(-2) ∨ h=(-1) ∨ h=(0) ∨ h=(1) ∨ h=(2) ∨ h=(3) ∨ h=(4) ∨ h=(5) ∨ h=(6) ∨ h=(7) ∨ h=(8) ∨ h=(9) ∨ h=(10) := by
        change -10≤h ∧ h≤10 at allowed
        omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨OddEndpointCertificate059.certificates⟩
      · exact ⟨OddEndpointCertificate060.certificates⟩
      · exact ⟨OddEndpointCertificate061.certificates⟩
      · exact ⟨OddEndpointCertificate062.certificates⟩
      · exact ⟨OddEndpointCertificate063.certificates⟩
      · exact ⟨OddEndpointCertificate064.certificates⟩
      · exact ⟨OddEndpointCertificate065.certificates⟩
      · exact ⟨OddEndpointCertificate066.certificates⟩
      · exact ⟨OddEndpointCertificate067.certificates⟩
      · exact ⟨OddEndpointCertificate068.certificates⟩
      · exact ⟨OddEndpointCertificate069.certificates⟩
      · exact ⟨OddEndpointCertificate070.certificates⟩
      · exact ⟨OddEndpointCertificate071.certificates⟩
      · exact ⟨OddEndpointCertificate072.certificates⟩
      · exact ⟨OddEndpointCertificate073.certificates⟩
      · exact ⟨OddEndpointCertificate074.certificates⟩
      · exact ⟨OddEndpointCertificate075.certificates⟩
      · exact ⟨OddEndpointCertificate076.certificates⟩
      · exact ⟨OddEndpointCertificate077.certificates⟩
      · exact ⟨OddEndpointCertificate078.certificates⟩
      · exact ⟨OddEndpointCertificate079.certificates⟩
  · cases a with
    | none => exact ⟨OddEndpointCertificate080.certificates⟩
    | some h =>
      have cases : h=(-10) ∨ h=(-9) ∨ h=(-8) ∨ h=(-7) ∨ h=(-6) ∨ h=(-5) ∨ h=(-4) ∨ h=(-3) ∨ h=(-2) ∨ h=(-1) ∨ h=(0) ∨ h=(1) ∨ h=(2) ∨ h=(3) ∨ h=(4) ∨ h=(5) ∨ h=(6) ∨ h=(7) ∨ h=(8) ∨ h=(9) ∨ h=(10) := by
        change -10≤h ∧ h≤10 at allowed
        omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨OddEndpointCertificate081.certificates⟩
      · exact ⟨OddEndpointCertificate082.certificates⟩
      · exact ⟨OddEndpointCertificate083.certificates⟩
      · exact ⟨OddEndpointCertificate084.certificates⟩
      · exact ⟨OddEndpointCertificate085.certificates⟩
      · exact ⟨OddEndpointCertificate086.certificates⟩
      · exact ⟨OddEndpointCertificate087.certificates⟩
      · exact ⟨OddEndpointCertificate088.certificates⟩
      · exact ⟨OddEndpointCertificate089.certificates⟩
      · exact ⟨OddEndpointCertificate090.certificates⟩
      · exact ⟨OddEndpointCertificate091.certificates⟩
      · exact ⟨OddEndpointCertificate092.certificates⟩
      · exact ⟨OddEndpointCertificate093.certificates⟩
      · exact ⟨OddEndpointCertificate094.certificates⟩
      · exact ⟨OddEndpointCertificate095.certificates⟩
      · exact ⟨OddEndpointCertificate096.certificates⟩
      · exact ⟨OddEndpointCertificate097.certificates⟩
      · exact ⟨OddEndpointCertificate098.certificates⟩
      · exact ⟨OddEndpointCertificate099.certificates⟩
      · exact ⟨OddEndpointCertificate100.certificates⟩
      · exact ⟨OddEndpointCertificate101.certificates⟩
  · cases a with
    | none => exact ⟨OddEndpointCertificate102.certificates⟩
    | some h =>
      have cases : h=(-10) ∨ h=(-9) ∨ h=(-8) ∨ h=(-7) ∨ h=(-6) ∨ h=(-5) ∨ h=(-4) ∨ h=(-3) ∨ h=(-2) ∨ h=(-1) ∨ h=(0) ∨ h=(1) ∨ h=(2) ∨ h=(3) ∨ h=(4) ∨ h=(5) ∨ h=(6) ∨ h=(7) ∨ h=(8) ∨ h=(9) ∨ h=(10) := by
        change -10≤h ∧ h≤10 at allowed
        omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨OddEndpointCertificate103.certificates⟩
      · exact ⟨OddEndpointCertificate104.certificates⟩
      · exact ⟨OddEndpointCertificate105.certificates⟩
      · exact ⟨OddEndpointCertificate106.certificates⟩
      · exact ⟨OddEndpointCertificate107.certificates⟩
      · exact ⟨OddEndpointCertificate108.certificates⟩
      · exact ⟨OddEndpointCertificate109.certificates⟩
      · exact ⟨OddEndpointCertificate110.certificates⟩
      · exact ⟨OddEndpointCertificate111.certificates⟩
      · exact ⟨OddEndpointCertificate112.certificates⟩
      · exact ⟨OddEndpointCertificate113.certificates⟩
      · exact ⟨OddEndpointCertificate114.certificates⟩
      · exact ⟨OddEndpointCertificate115.certificates⟩
      · exact ⟨OddEndpointCertificate116.certificates⟩
      · exact ⟨OddEndpointCertificate117.certificates⟩
      · exact ⟨OddEndpointCertificate118.certificates⟩
      · exact ⟨OddEndpointCertificate119.certificates⟩
      · exact ⟨OddEndpointCertificate120.certificates⟩
      · exact ⟨OddEndpointCertificate121.certificates⟩
      · exact ⟨OddEndpointCertificate122.certificates⟩
      · exact ⟨OddEndpointCertificate123.certificates⟩
#print axioms certificates
end Delivery.OddEndpointSavedCertificates
