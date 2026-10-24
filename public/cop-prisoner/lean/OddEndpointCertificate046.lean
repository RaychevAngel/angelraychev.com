import OddEndpointObjective046Transfer
import OddEndpointObjective046Delivery0
import OddEndpointObjective046Delivery1
import OddEndpointObjective046Delivery2
import OddEndpointObjective046Delivery3
import OddEndpointObjective046Delivery4
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate046
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern046
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective046Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective046Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective046Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective046Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective046Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective046Delivery4.certificate⟩
    · exact False.elim ((by decide : ¬targetAllowed residue patchAnchor 5) allowed)
#print axioms certificates
end Delivery.OddEndpointCertificate046
