import NLS.KdV.HillOriginalSequenceBasisDirections
import NLS.SequenceSpaces.NatL2DenseRange

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.KdV

/-- The derivative of the ACTUAL original spectral sequence has dense
range at EVERY original real mean-zero L2 source. This follows from the
full physical Gardner matrix and actual real mean-zero Hamiltonian
preimages, including every low and collapsed spectral gap. -/
theorem denseRange_fderiv_hillOriginalMeanZeroRealSpectralMap
    (q : hillRealMeanZeroSourceSubmodule) :
    DenseRange (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q) :=
  NLS.SequenceSpaces.denseRange_natL2_of_single_preimages _
    (exists_hillOriginalMeanZeroDerivative_single_preimage q)

/-- Once closedness of the actual range is established, the proved
all-source physical preimages give surjectivity of that same derivative. -/
theorem surjective_fderiv_hillOriginalMeanZeroRealSpectralMap_of_closed_range
    (q : hillRealMeanZeroSourceSubmodule)
    (hc : IsClosed (range (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q))) :
    Function.Surjective (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q) := by
  apply range_eq_univ.mp
  rw [←hc.closure_eq]
  exact (denseRange_fderiv_hillOriginalMeanZeroRealSpectralMap q).closure_eq

end NLS.KdV
