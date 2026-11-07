import NLS.Articles.KdVPseudomeasures.SpectralMultiplicityOrder
import NLS.KdV.PseudomeasureRealSpectrum

/-!
# Spectral reality for the original article potentials

The physical H-minus-one inclusion preserves the complete original distribution.
Native reality therefore gives global spectral reality and semisimplicity on the
full original H1 domain. On exact original norm balls one cutoff, chosen before
the potential, gives real corrected-strip zeros of multiplicity one or two.
Canonical global spectral labels and their low-mode offset are not asserted.
-/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Native distributional reality is preserved by the exact original inclusion. -/
theorem sourceComplexHminusOne_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : q.val = q.val.conjugate) :
    (sourceComplexHminusOne r hr q).val = (sourceComplexHminusOne r hr q).val.conjugate := by
  rw [sourceComplexHminusOne_val]
  exact hq

/-- All spectral points of every original native real endpoint potential are real. -/
theorem sourceHillSpectrum_im_eq_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : q.val = q.val.conjugate)
    (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q) : z.im = 0 := by
  obtain ⟨f, hf0, hf⟩ := (sourceHillSpectrum_mem_iff r hr q z).mp hz
  exact singularHill_eigenvalue_im_eq_zero _ (sourceComplexHminusOne_real r hr q hq) z f hf0 hf

/-- The original real mean-zero physically period-one source has entirely real spectrum. -/
theorem sourceHillSpectrum_ofPotential_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q.val) : z.im = 0 :=
  sourceHillSpectrum_im_eq_zero r hr q.val q.property.1 z hz

/-- Every nonreal parameter gives a bijective physical pencil on the full original H1 domain. -/
theorem sourceHillPencil_bijective_of_im_ne_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : q.val = q.val.conjugate)
    (z : ℂ) (hz : z.im ≠ 0) :
    Function.Bijective (singularHillOperator (sourceComplexHminusOne r hr q) -
      z • singularHillDomainInclusion) := by
  by_contra hnot
  exact hz (sourceHillSpectrum_im_eq_zero r hr q hq z hnot)

/-- The original full algebraic root space of a real source potential is its actual first root level. -/
theorem sourceHillRootSpaceTop_eq_one_of_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : q.val = q.val.conjugate) (z : ℂ) :
    singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z =
      singularHillRootSpace (sourceComplexHminusOne r hr q) z 1 :=
  singularHillRootSpaceTop_eq_one_of_real _ (sourceComplexHminusOne_real r hr q hq) z

/-- On the original real source, actual algebraic and geometric multiplicities agree globally. -/
theorem sourceHillAlgebraicMultiplicity_eq_geometric (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : q.val = q.val.conjugate) (z : ℂ) :
    sourceHillAlgebraicMultiplicity r hr q z =
      Module.finrank ℂ (singularHillEigenspace (sourceComplexHminusOne r hr q) z) := by
  unfold sourceHillAlgebraicMultiplicity
  rw [sourceHillRootSpaceTop_eq_one_of_real r hr q hq z]
  exact (singularHillEigenspaceRootEquiv _ z).finrank_eq.symm

/-- Original native real endpoint eigenspaces are finite dimensional at every parameter. -/
theorem finiteDimensional_realSourceHillEigenspace (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : q.val = q.val.conjugate) (z : ℂ) :
    FiniteDimensional ℂ (singularHillEigenspace (sourceComplexHminusOne r hr q) z) := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  apply finiteDimensional_realEndpointHillEigenspace r hr.1 hr.2 (sourceEndpointCoefficients r q)
  rw [sourceEndpointCoefficients_HminusOne_val]
  exact hq

/-- Every actual source determinant zero in an allowed strip is a real physical spectral point. -/
theorem sourceEndpointDeterminant_zero_im_eq_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hq : q.val = q.val.conjugate)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : sourceEndpointDeterminant r hr n (q,z) = 0) : z.im = 0 := by
  apply sourceHillSpectrum_im_eq_zero r hr q hq z
  rw [sourceHillSpectrum_eq]
  apply (mem_endpointHillSpectrum_iff_determinant r hr.1 hr.2 n hn z hz
    (sourceEndpointCoefficients r q) _).mpr hd
  simpa only [norm_sourceEndpointCoefficients] using hs

/-- Actual physical algebraic multiplicities of real source potentials are at most two in tail strips. -/
theorem sourceHillAlgebraicMultiplicity_le_two_of_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hq : q.val = q.val.conjugate)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) : sourceHillAlgebraicMultiplicity r hr q z ≤ 2 := by
  rw [sourceHillAlgebraicMultiplicity_eq_geometric r hr q hq z,
    ← sourceEndpointCoefficients_HminusOne_complex r hr q]
  apply finrank_singularHillEigenspace_le_two r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q)
  simpa only [norm_sourceEndpointCoefficients] using hs

/-- The actual original real-source determinant has analytic order at most two on each tail strip. -/
theorem sourceEndpointDeterminant_order_le_two_of_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hq : q.val = q.val.conjugate)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    analyticOrderAt (fun y => sourceEndpointDeterminant r hr n (q,y)) z ≤ 2 := by
  rw [← sourceHillAlgebraicMultiplicity_eq_analyticOrderAt r hr n hn q hs z hz]
  exact_mod_cast sourceHillAlgebraicMultiplicity_le_two_of_real r hr n hn q hq hs z hz

/-- One cutoff, chosen before every original physical potential on a norm ball,
gives real tail zeros of actual multiplicity one or two and total algebraic count two. -/
theorem source_uniform_real_spectral_tail (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R → ∀ n : ℕ, N ≤ n →
      (∀ z ∈ reducedHillStrip n, sourceEndpointDeterminant r hr n (q.val,z) = 0 →
        z.im = 0 ∧ (sourceHillAlgebraicMultiplicity r hr q.val z = 1 ∨
          sourceHillAlgebraicMultiplicity r hr q.val z = 2)) ∧
      (∑ᶠ z : ℂ, if z ∈ reducedHillStrip n then sourceHillAlgebraicMultiplicity r hr q.val z else 0) = 2 := by
  obtain ⟨N, hN, hcut⟩ := exists_endpointHill_cutoff r hr.2 R
  refine ⟨N, hN, ?_⟩
  intro q hq n hn
  have hn1 := hN.trans hn
  have hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hn)
  refine ⟨?_, sourceHill_strip_algebraic_count_two r hr n hn1 q.val hs⟩
  intro z hz hd
  refine ⟨sourceEndpointDeterminant_zero_im_eq_zero r hr n hn1 q.val q.property.1 hs z hz hd, ?_⟩
  have hu := sourceHillAlgebraicMultiplicity_le_two_of_real r hr n hn1 q.val q.property.1 hs z hz
  have hp : 0 < sourceHillAlgebraicMultiplicity r hr q.val z := by
    apply (sourceHillAlgebraicMultiplicity_pos_iff r hr q.val z).mpr
    rw [sourceHillSpectrum_eq]
    apply (mem_endpointHillSpectrum_iff_determinant r hr.1 hr.2 n hn1 z hz
      (sourceEndpointCoefficients r q.val) _).mpr hd
    simpa only [norm_sourceEndpointCoefficients] using hs
  omega

end NLS.Articles.KdVPseudomeasures
