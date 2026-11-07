import NLS.KdV.SingularHillSemibounded
import NLS.KdV.PseudomeasureWideLocalization

/-!
# Lower bounds and finite central regions of the actual endpoint spectrum

The potential may be complex. The original full H1/H-minus-one Fredholm
alternative turns the full-domain form bounds into statements about every
actual spectral point. Every left real half-plane contains only finitely many
spectral values. Native real potentials also have an actual lowest eigenvalue.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
include hr

/-- The full original complex endpoint spectrum has an explicit lower real-part bound. -/
theorem endpointHillSpectrum_re_lower_bound (z : ℂ) (hz : z ∈ endpointHillSpectrum r hr1 q) :
    -singularHillLowerBoundConstant ‖endpointHillHminusOne SpectralWeight.one r hr1 q‖ ≤ z.re := by
  obtain ⟨f,hf0,hf⟩ := (mem_endpointHillSpectrum_iff r hr hr1 q z).mp hz
  exact singularHill_eigenvalue_re_lower_bound _ z f hf0 hf

/-- The full original complex endpoint spectrum obeys the same imaginary-part bound. -/
theorem endpointHillSpectrum_abs_im_le (z : ℂ) (hz : z ∈ endpointHillSpectrum r hr1 q) :
    |z.im| ≤ z.re+2*singularHillLowerBoundConstant ‖endpointHillHminusOne SpectralWeight.one r hr1 q‖ := by
  obtain ⟨f,hf0,hf⟩ := (mem_endpointHillSpectrum_iff r hr hr1 q z).mp hz
  exact singularHill_eigenvalue_abs_im_le _ z f hf0 hf

/-- Bounding the real part above bounds the entire actual spectral value. -/
theorem endpointHillSpectrum_norm_le (z : ℂ) (hz : z ∈ endpointHillSpectrum r hr1 q) :
    ‖z‖ ≤ 2*z.re+4*singularHillLowerBoundConstant ‖endpointHillHminusOne SpectralWeight.one r hr1 q‖ := by
  obtain ⟨f,hf0,hf⟩ := (mem_endpointHillSpectrum_iff r hr hr1 q z).mp hz
  exact singularHill_eigenvalue_norm_le _ z f hf0 hf

/-- The full actual spectrum in any left real half-plane is finite, also for complex potentials. -/
theorem finite_endpointHillSpectrum_re_le (T : ℝ) :
    Set.Finite {z : ℂ | z ∈ endpointHillSpectrum r hr1 q ∧ z.re ≤ T} := by
  apply (finite_endpointHillSpectrum_norm_le r hr hr1 q
    (2*T+4*singularHillLowerBoundConstant ‖endpointHillHminusOne SpectralWeight.one r hr1 q‖)).subset
  intro z hz
  exact ⟨hz.1,(endpointHillSpectrum_norm_le r hr hr1 q z hz.1).trans (by linarith [hz.2])⟩

/-- The strict central sublevel set is finite in the full original spectrum. -/
theorem finite_endpointHillSpectrum_re_lt (T : ℝ) :
    Set.Finite {z : ℂ | z ∈ endpointHillSpectrum r hr1 q ∧ z.re < T} :=
  (finite_endpointHillSpectrum_re_le r hr hr1 q T).subset (fun _ h => ⟨h.1,h.2.le⟩)

/-- The left of the explicit lower bound is in the full actual physical resolvent. -/
theorem endpointHill_mem_resolvent_of_re_lt (z : ℂ)
    (hz : z.re < -singularHillLowerBoundConstant ‖endpointHillHminusOne SpectralWeight.one r hr1 q‖) :
    z ∈ endpointHillResolventSet r hr1 q := by
  by_contra hnot
  exact not_le.mpr hz (endpointHillSpectrum_re_lower_bound r hr hr1 q z hnot)

/-- The real endpoint spectrum is nonempty, using a proved actual high pair. -/
theorem endpointHillSpectrum_nonempty_of_real
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) :
    (endpointHillSpectrum r hr1 q).Nonempty := by
  obtain ⟨N,hN,hcut⟩ := exists_endpointHill_cutoff r hr1 ‖q‖
  let p := endpointHillRealPair r hr hr1 N hN q (hcut N le_rfl) hq
  exact ⟨p.left,p.left_spectral⟩

/-- Every native real original endpoint potential has an actual lowest spectral value. -/
theorem endpointHillSpectrum_exists_lowest_of_real
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) :
    ∃ a : ℝ, (a:ℂ) ∈ endpointHillSpectrum r hr1 q ∧
      ∀ z ∈ endpointHillSpectrum r hr1 q, a ≤ z.re := by
  obtain ⟨b,hb⟩ := endpointHillSpectrum_nonempty_of_real r hr hr1 q hq
  obtain ⟨a,ha,hmin⟩ := Set.exists_min_image
    {z : ℂ | z ∈ endpointHillSpectrum r hr1 q ∧ z.re ≤ b.re} Complex.re
      (finite_endpointHillSpectrum_re_le r hr hr1 q b.re) ⟨b,hb,le_rfl⟩
  have him := endpointHillSpectrum_im_eq_zero r hr hr1 q hq a ha.1
  have he : (a.re:ℂ) = a := by apply Complex.ext <;> simp [him]
  refine ⟨a.re,he.symm ▸ ha.1,?_⟩
  intro z hz
  by_cases hzb : z.re ≤ b.re
  · exact hmin z ⟨hz,hzb⟩
  · linarith [ha.2]

end NLS.KdV
