import NLS.Articles.KdVPseudomeasures.SourceSpaces
import NLS.KdV.PseudomeasureReduction
import NLS.KdV.PseudomeasureEllipticRegularity

/-! # Section 2 reduction for the exact original source potentials

The determinant criterion below quantifies over the article's original real,
mean-zero, physically period-one potentials. A single cutoff is chosen before
the potential, the mode and the spectral parameter. The physical eigenspace
is the entire original period-two H1 domain.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The exact source Fourier coefficients in the unit spectral weight convention. -/
def sourceEndpointCoefficients (r : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  ⟨(sobolevCoefficients (-r) ⊤ q).val, by
    have h := (sobolevCoefficients (-r) ⊤ q).property
    change Memℓp (fun k => (SpectralWeight.one.negativeSobolev r k:ℂ)*
      (sobolevCoefficients (-r) ⊤ q).val k) ⊤
    change Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*
      (sobolevCoefficients (-r) ⊤ q).val k) ⊤ at h
    simpa only [SpectralWeight.negativeSobolev_eq_product, SpectralWeight.one_apply, one_mul] using h⟩

@[simp] theorem sourceEndpointCoefficients_apply (r : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (k : ℤ) :
    (sourceEndpointCoefficients r q).val k = q.val (mode (-k)) := rfl

/-- No norm or normalization change is hidden in the unit-weight realization. -/
theorem norm_sourceEndpointCoefficients (r : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    ‖sourceEndpointCoefficients r q‖ = ‖q‖ := by
  rw [← (sobolevCoefficients (L := 2) (-r) ⊤).norm_map q]
  change ‖WeightedCoeff.weightEquiv _ ⊤ (sourceEndpointCoefficients r q)‖ =
    ‖WeightedCoeff.weightEquiv _ ⊤ (sobolevCoefficients (-r) ⊤ q)‖
  congr 1
  ext k
  simp only [WeightedCoeff.weightEquiv_apply, SpectralWeight.negativeSobolev_eq_product,
    SpectralWeight.one_apply, one_mul, sourceEndpointCoefficients_apply, sobolevCoefficients_apply]

/-- The H-minus-one inclusion retains every original smooth-test action,
also for an arbitrary complex inhomogeneous right-hand side. -/
theorem sourceEndpointCoefficients_HminusOne_val (r : ℝ) (hr : r < 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    (NLS.KdV.endpointHillHminusOne SpectralWeight.one r hr (sourceEndpointCoefficients r q)).val =
      q.val := by
  apply Distribution.ext_coefficients
  intro k
  rw [NLS.KdV.endpointHillHminusOne_coefficient, sourceEndpointCoefficients_apply]

/-- The potential entering the physical operator is the identical original
source distribution included in H-minus-one. -/
theorem sourceEndpointCoefficients_HminusOne (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) :
    NLS.KdV.endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q.val) =
      potentialHminusOne r hr q := by
  apply Subtype.ext
  rw [potentialHminusOne_val]
  apply Distribution.ext_coefficients
  intro k
  rw [NLS.KdV.endpointHillHminusOne_coefficient, sourceEndpointCoefficients_apply]

/-- Lemma 2.7 and equation (17), with the corrected strip radius 6n:
uniformly on every source norm ball, the explicit effective determinant
vanishes exactly at nonzero full-domain physical Hill eigenvectors.
Spectral labels and algebraic multiplicities are not part of this equivalence. -/
theorem sourceLemma2_7_uniform_physical_reduction (r : ℝ)
    (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n →
      ∀ (z : ℂ) (hz : z ∈ NLS.KdV.reducedHillStrip n),
      ∃ hsmall : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q.val‖ ≤ 1/2,
        (NLS.KdV.endpointHillReducedOperator r hr.1 hr.2 n hn z hz
          (sourceEndpointCoefficients r q.val) hsmall).toLinearMap.det = 0 ↔
          ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
            NLS.KdV.singularHillOperator (potentialHminusOne r hr q) f =
              z • NLS.KdV.singularHillDomainInclusion f := by
  obtain ⟨N,hN,hred⟩ := NLS.KdV.exists_endpointHill_uniform_physical_reduction r hr.1 hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hnN z hz
  obtain ⟨hs,hB⟩ := hred (sourceEndpointCoefficients r q.val)
    (by simpa only [norm_sourceEndpointCoefficients] using hq) n hn hnN z hz
  exact ⟨hs,by simpa only [sourceEndpointCoefficients_HminusOne r hr q] using hB⟩

/-- Appendix C, Lemma C.2, for the exact original physical source potential,
every original endpoint right-hand side, and every complex spectral parameter. -/
theorem sourceLemmaC_2 (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (g : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : (NLS.KdV.singularHillOperator (potentialHminusOne r hr q) f).val -
      z • f.val = g.val) :
    ∃ u : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val = f.val := by
  have hfE : NLS.KdV.singularHillOperator
      (NLS.KdV.endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q.val)) f -
      z • NLS.KdV.singularHillDomainInclusion f =
        NLS.KdV.endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r g) := by
    apply Subtype.ext
    change (NLS.KdV.singularHillOperator _ f).val -
      z • (NLS.KdV.singularHillDomainInclusion f).val = _
    rw [sourceEndpointCoefficients_HminusOne r hr q, NLS.KdV.singularHillDomainInclusion_val,
      sourceEndpointCoefficients_HminusOne_val]
    exact hf
  have h := NLS.KdV.singularHill_inhomogeneous_memlp r hr.1 hr.2
    (sourceEndpointCoefficients r q.val) (sourceEndpointCoefficients r g) z f hfE
  have h' : Memℓp (fun k => (Weight.sobolev (-r+2) k:ℂ)*f.val (mode (-k))) ⊤ := by
    simpa only [SpectralWeight.negativeSobolev_eq_product, SpectralWeight.one_apply, one_mul,
      show -(r-2) = -r+2 by ring] using h
  let a : WeightedCoeff (Weight.sobolev (-r+2)) ⊤ := ⟨fun k => f.val (mode (-k)),h'⟩
  refine ⟨(sobolevCoefficients (-r+2) ⊤).symm a,?_⟩
  apply Distribution.ext_coefficients
  intro k
  change ((sobolevCoefficients (-r+2) ⊤) ((sobolevCoefficients (-r+2) ⊤).symm a)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]

end NLS.Articles.KdVPseudomeasures
