import NLS.Articles.KdVKdV2Frequencies.HilbertFrequencyCompactFromIntermediate
import NLS.Articles.KdVKdV2Frequencies.GlobalCorrectedFrequencyCompact
import NLS.SequenceSpaces.HilbertCompactActionIntertwining

/-! The ACTUAL physical Hilbert frequency gradient has compact corrected
ACTION derivative at EVERY nonnegative Hilbert action. Original weighted
compactness, exact cone calibration and genuine Hessian symmetry supply
the full operator conclusion, including arbitrary infinite support. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem physical_hilbert_corrected_gradient_compact
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (a : ActionSpace) (ha : a∈positiveQuadrant) :
    IsCompactOperator (fderiv ℂ (actionGradient E.hamiltonian) a+
      (6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace) := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  obtain ⟨Ω,I,hΩ,hΩr,hI,hIrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  let α : ℝ := -3/4
  have hα0 : -1<α := by norm_num [α]
  have hα1 : α< -1/2 := by norm_num [α]
  obtain ⟨U,F,hU,hCU,hF,_hzeroF,hpair⟩ := exists_global_negativeWeighted_physical_action_packet
    D (-α) ((α+1)/2) (by norm_num [α]) (by norm_num [α]) (by norm_num [α]) (by ring)
  apply physical_hilbert_compact_of_intermediate_packet D E α hα0 hα1 U F hU hCU hF hpair
    V G hV hCV hG hrec ?_ a ha
  intro b hb
  exact global_negativeWeighted_corrected_derivative_compact D (-α) ((α+1)/2)
    (by norm_num [α]) (by norm_num [α]) (by norm_num [α]) (by ring)
    Ω hΩr I hI hΩ hIrec U F hU hCU hF hpair b hb

end NLS.Articles.KdVKdV2Frequencies
