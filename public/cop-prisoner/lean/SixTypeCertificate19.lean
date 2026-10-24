import SixTypeObjective19Transfer
import SixTypeObjective19Delivery0
import SixTypeObjective19Delivery1
import SixTypeObjective19Delivery2
import SixTypeObjective19Delivery3
import SixTypeObjective19Delivery4
import SixTypeObjective19Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate19
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern19.pattern := by
  constructor
  · exact ⟨SixTypeObjective19Transfer.data, SixTypeObjective19Transfer.checked, SixTypeObjective19Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective19Delivery0.data, SixTypeObjective19Delivery0.checked, SixTypeObjective19Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective19Delivery1.data, SixTypeObjective19Delivery1.checked, SixTypeObjective19Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective19Delivery2.data, SixTypeObjective19Delivery2.checked, SixTypeObjective19Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective19Delivery3.data, SixTypeObjective19Delivery3.checked, SixTypeObjective19Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective19Delivery4.data, SixTypeObjective19Delivery4.checked, SixTypeObjective19Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective19Delivery5.data, SixTypeObjective19Delivery5.checked, SixTypeObjective19Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate19
