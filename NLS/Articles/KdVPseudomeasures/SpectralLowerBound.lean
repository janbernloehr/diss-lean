import NLS.Articles.KdVPseudomeasures.SpectralWideLocalization
import NLS.KdV.PseudomeasureLowerSpectrum

/-!
# Uniform lower spectral bounds and finite central spectra on the original source

The norm bound uses the actual original endpoint-to-H-minus-one inclusion.
Every spectral point is for the full original H1/H-minus-one operator. Central
algebraic counts are defined from actual finite physical spectra. Their exact
value2N-1 for complex source potentials is proved downstream in
SpectralComplexCentral, followed by canonical lexicographic global labels.
-/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The original same-distribution H-minus-one inclusion as its actual bounded linear map. -/
def sourceHminusOneInclusion (r : ℝ) (hr : AdmissiblePredualOrder r) :
    FourierLebesgueSpace (2:ℝ) (-r) ⊤ →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  endpointLowerInclusion (-r) (-1) (by norm_num) (admissible_hminusOne_threshold r hr)

/-- No original distribution changes in passing to this bounded-map formulation. -/
theorem sourceHminusOneInclusion_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    sourceHminusOneInclusion r hr q = sourceComplexHminusOne r hr q := rfl

/-- One explicit spectral constant for the entire exact original endpoint norm ball. -/
def sourceSpectralBound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) : ℝ :=
  singularHillLowerBoundConstant (‖sourceHminusOneInclusion r hr‖*R)

theorem sourceSpectralBound_nonneg (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    0 ≤ sourceSpectralBound r hr R := singularHillLowerBoundConstant_nonneg _

/-- The original endpoint norm bound controls the identical original H-minus-one potential. -/
theorem sourceComplexHminusOne_norm_le_on_ball (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) :
    ‖sourceComplexHminusOne r hr q‖ ≤ ‖sourceHminusOneInclusion r hr‖*R :=
  ((sourceHminusOneInclusion r hr).le_opNorm q).trans
    (mul_le_mul_of_nonneg_left hq (norm_nonneg _))

/-- The full original complex source spectrum has a uniform lower real-part bound on norm balls. -/
theorem sourceHillSpectrum_re_lower_bound_on_ball (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q) : -sourceSpectralBound r hr R ≤ z.re := by
  obtain ⟨f,hf0,hf⟩ := (sourceHillSpectrum_mem_iff r hr q z).mp hz
  exact singularHill_eigenvalue_re_lower_bound_of_norm_le _ _
    (sourceComplexHminusOne_norm_le_on_ball r hr R q hq) z f hf0 hf

/-- A bound above on the real part bounds the full spectral value uniformly on original norm balls. -/
theorem sourceHillSpectrum_norm_le_on_ball (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q) : ‖z‖ ≤ 2*z.re+4*sourceSpectralBound r hr R := by
  obtain ⟨f,hf0,hf⟩ := (sourceHillSpectrum_mem_iff r hr q z).mp hz
  have h := singularHill_eigenvalue_norm_le _ z f hf0 hf
  have hC := singularHillLowerBoundConstant_mono (norm_nonneg (sourceComplexHminusOne r hr q))
    (sourceComplexHminusOne_norm_le_on_ball r hr R q hq)
  exact h.trans (by dsimp [sourceSpectralBound]; linarith)

/-- The imaginary parts of the full original complex spectrum have the same uniform sector bound. -/
theorem sourceHillSpectrum_abs_im_le_on_ball (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q) : |z.im| ≤ z.re+2*sourceSpectralBound r hr R := by
  obtain ⟨f,hf0,hf⟩ := (sourceHillSpectrum_mem_iff r hr q z).mp hz
  have h := singularHill_eigenvalue_abs_im_le _ z f hf0 hf
  have hC := singularHillLowerBoundConstant_mono (norm_nonneg (sourceComplexHminusOne r hr q))
    (sourceComplexHminusOne_norm_le_on_ball r hr R q hq)
  exact h.trans (by dsimp [sourceSpectralBound]; linarith)

/-- The left of the uniform lower bound is in the full original physical resolvent. -/
theorem sourceHillPencil_bijective_of_re_lt_on_ball (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (z : ℂ) (hz : z.re < -sourceSpectralBound r hr R) :
    Function.Bijective (singularHillOperator (sourceComplexHminusOne r hr q)-z • singularHillDomainInclusion) := by
  by_contra hnot
  exact not_le.mpr hz (sourceHillSpectrum_re_lower_bound_on_ball r hr R q hq z hnot)

/-- Every central left half-plane contains only finitely many actual source spectral values. -/
theorem finite_sourceHillSpectrum_re_le (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (T : ℝ) :
    Set.Finite {z : ℂ | z ∈ sourceHillSpectrum r hr q ∧ z.re ≤ T} := by
  rw [sourceHillSpectrum_eq]
  exact finite_endpointHillSpectrum_re_le r hr.1 hr.2 (sourceEndpointCoefficients r q) T

/-- The original native real physical source has an actual lowest spectral value. -/
theorem sourceHillSpectrum_exists_lowest (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    ∃ a : ℝ, (a:ℂ) ∈ sourceHillSpectrum r hr q.val ∧ ∀ z ∈ sourceHillSpectrum r hr q.val, a ≤ z.re := by
  simp only [sourceHillSpectrum_eq]
  apply endpointHillSpectrum_exists_lowest_of_real r hr.1 hr.2 (sourceEndpointCoefficients r q.val)
  rw [sourceEndpointCoefficients_HminusOne_val]
  exact q.property.1

/-- The finite actual central spectrum strictly below the high-region edge. -/
def sourceCentralSpectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) : Finset ℂ :=
  (show Set.Finite {z : ℂ | z ∈ sourceHillSpectrum r hr q ∧ z.re < freeHillValue N-12*(N:ℝ)} from
    (finite_sourceHillSpectrum_re_le r hr q (freeHillValue N-12*(N:ℝ))).subset
      (fun _ h => ⟨h.1,h.2.le⟩)).toFinset

/-- Central membership means membership in the actual original operator spectrum. -/
theorem mem_sourceCentralSpectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) (z : ℂ) :
    z ∈ sourceCentralSpectrum r hr q N ↔ z ∈ sourceHillSpectrum r hr q ∧ z.re < freeHillValue N-12*(N:ℝ) := by
  simp only [sourceCentralSpectrum,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

/-- The actual finite central algebraic count; its value is not assumed. -/
def sourceCentralAlgebraicCount (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) : ℕ :=
  ∑ z ∈ sourceCentralSpectrum r hr q N, sourceHillAlgebraicMultiplicity r hr q z

/-- Every central spectral point has positive actual physical algebraic multiplicity. -/
theorem sourceCentral_multiplicity_pos (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) (z : ℂ)
    (hz : z ∈ sourceCentralSpectrum r hr q N) : 0 < sourceHillAlgebraicMultiplicity r hr q z :=
  (sourceHillAlgebraicMultiplicity_pos_iff r hr q z).mpr ((mem_sourceCentralSpectrum r hr q N z).mp hz).1

end NLS.Articles.KdVPseudomeasures
