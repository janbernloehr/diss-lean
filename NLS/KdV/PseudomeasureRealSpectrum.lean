import NLS.KdV.SingularHillRealSpectrum
import NLS.KdV.PseudomeasureMultiplicityOrder

/-!
# Actual real endpoint spectrum and geometric multiplicity

The reality assumption is on the unchanged original distribution, and all
root spaces use the entire original H1 domain. Algebraic and geometric
multiplicities agree globally for real endpoint potentials. In the corrected
tail strips the actual determinant order is therefore at most two.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Every point of the full original real endpoint spectrum is real. -/
theorem endpointHillSpectrum_im_eq_zero (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate)
    (z : ℂ) (hz : z ∈ endpointHillSpectrum r hr1 q) : z.im = 0 := by
  obtain ⟨f, hf0, hf⟩ := (mem_endpointHillSpectrum_iff r hr hr1 q z).mp hz
  exact singularHill_eigenvalue_im_eq_zero _ hq z f hf0 hf

/-- The actual algebraic multiplicity of a native real endpoint potential
is the dimension of its full original domain eigenspace. -/
theorem endpointHillAlgebraicMultiplicity_eq_geometric (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) (z : ℂ) :
    endpointHillAlgebraicMultiplicity r hr hr1 q z = Module.finrank ℂ
      (singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) z) := by
  unfold endpointHillAlgebraicMultiplicity
  rw [singularHillRootSpaceTop_eq_one_of_real _ hq z]
  exact (singularHillEigenspaceRootEquiv _ z).finrank_eq.symm

/-- For real endpoint potentials the original eigenspace is finite dimensional globally. -/
theorem finiteDimensional_realEndpointHillEigenspace (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) (z : ℂ) :
    FiniteDimensional ℂ (singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) z) := by
  have hfin := finiteDimensional_endpointHillRootSpaceTop r hr hr1 q z
  rw [singularHillRootSpaceTop_eq_one_of_real _ hq z] at hfin
  let := hfin
  exact FiniteDimensional.of_injective (singularHillEigenspaceRootEquiv _ z).toLinearMap
    (singularHillEigenspaceRootEquiv _ z).injective

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
  (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs hq in
/-- Every actual zero of the corrected-strip determinant is real. -/
theorem endpointReducedDeterminant_zero_im_eq_zero (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : endpointReducedDeterminant r hr hr1 n (q,z) = 0) : z.im = 0 :=
  endpointHillSpectrum_im_eq_zero r hr hr1 q hq z
    ((mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn z hz q hs).mpr hd)

include hn hs hq in
/-- Actual algebraic multiplicity is at most two on the corrected real tail strips. -/
theorem endpointHillAlgebraicMultiplicity_le_two_of_real (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    endpointHillAlgebraicMultiplicity r hr hr1 q z ≤ 2 := by
  rw [endpointHillAlgebraicMultiplicity_eq_geometric r hr hr1 q hq z]
  exact finrank_singularHillEigenspace_le_two r hr hr1 n hn z hz q hs

include hn hs hq in
/-- Actual analytic determinant order is at most two throughout the corrected strip. -/
theorem endpointReducedDeterminant_order_le_two_of_real (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    analyticOrderAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z ≤ 2 := by
  rw [← endpointHillAlgebraicMultiplicity_eq_analyticOrderAt r hr hr1 n hn q hs z hz]
  exact_mod_cast endpointHillAlgebraicMultiplicity_le_two_of_real r hr hr1 n hn q hq hs z hz

end NLS.KdV
