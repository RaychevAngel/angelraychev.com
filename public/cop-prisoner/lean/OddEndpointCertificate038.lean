import OddEndpointObjective038Transfer
import OddEndpointObjective038Delivery0
import OddEndpointObjective038Delivery1
import OddEndpointObjective038Delivery2
import OddEndpointObjective038Delivery3
import OddEndpointObjective038Delivery4
import OddEndpointObjective038Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate038
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern038
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective038Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective038Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective038Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective038Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective038Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective038Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective038Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate038
