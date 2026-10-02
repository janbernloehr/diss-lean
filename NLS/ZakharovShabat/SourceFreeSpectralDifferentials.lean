import NLS.ZakharovShabat.SourceFreePotentialCotangents
import NLS.ZakharovShabat.SourcePeriodicIsospectral
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential
import NLS.ZakharovShabat.SourceNormalizedActionFree
import NLS.ZakharovShabat.SourceDeletedFreeSine

/-! # The actual free spectral differentials

At zero source the discriminant is stationary in every direction.
The Dirichlet root derivative is the half-sum of two Fourier coordinates;
the moving anti-discriminant derivative is their signed difference.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every potential direction is infinitesimally isospectral at zero. -/
theorem sourceIsospectralDirection_zero (h : CoeffPair 2) :
    SourceIsospectralDirection (by simp) 0 h := by
  intro z
  rw [sourceDiscriminantCotangent_zero]
  rfl

/-- The full derivative of every periodic midpoint vanishes at zero. -/
theorem fderiv_canonicalPeriodicMidpoint_zero : ∀ n : ℤ,
    fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodicMidpoint (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) 0 = 0 := by
  intro n
  ext h
  exact (fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero
    (by simp) (by norm_num) 0 (by simp) h (sourceIsospectralDirection_zero h) n).1

/-- The free boundary-root derivative has its exact component and
frequency signs for both ordinary boundary conditions. -/
theorem fderiv_canonicalPeriodOneBoundaryRoot_zero
    (b : BoundaryCondition) (n : ℤ) (h : CoeffPair 2) :
    (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) b ψ n) 0) h =
      BoundaryCondition.extensionSign b / 2 * (h.fst (-n)+h.snd n) := by
  have hc : cos ((Real.pi : ℂ)*n) ≠ 0 := by
    intro hz
    have hn := norm_cos_freeCenter n
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hchar : periodOneBoundaryCharacteristic (p := 2) (by simp) (by norm_num) b 0 = sin :=
    funext (periodOneBoundaryCharacteristic_zero (by simp) (by norm_num) b)
  rw [fderiv_canonicalPeriodOneBoundaryRoot_apply (by simp) (by norm_num) b 0 (by simp) n h,
    canonicalPeriodOneBoundaryRoots_zero,hchar,Complex.deriv_sin,sourceBoundaryCharacteristicCotangent_zero]
  field_simp

/-- The moving-terminal derivative includes the root motion; its
spectral correction is zero at the identically zero free anti-discriminant. -/
theorem fderiv_sourceBoundaryTerminalAntiDiscriminant_zero
    (n : ℤ) (h : CoeffPair 2) :
    (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant (p := 2) (by simp) (by norm_num) .dirichlet n) 0) h =
      I*cos ((Real.pi : ℂ)*n) * (h.fst (-n)-h.snd n) := by
  have hanti : sourceAntiDiscriminantCandidate (p := 2) (by simp) (by norm_num) 0 = (fun _ => 0) :=
    funext (sourceAntiDiscriminantCandidate_zero (by simp) (by norm_num))
  rw [fderiv_sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet n 0 (by simp)]
  simp only [canonicalPeriodOneBoundaryRoots_zero,hanti,deriv_const]
  change (sourceAntiDiscriminantCotangent (by simp) (by norm_num) ((Real.pi : ℂ)*n) 0 +
    (0 : ℂ) • _) h = _
  simpa only [add_apply, smul_apply, smul_eq_mul, zero_mul, add_zero] using
    sourceAntiDiscriminantCotangent_zero n h

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The omitted free root product at the removed root is the nonzero
signed cosine, not an undefined sine quotient. -/
theorem sourceStandardRootOmittedProduct_zero_center
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) ((Real.pi : ℂ)*n) = cos ((Real.pi : ℂ)*n) := by
  rw [sourceStandardRootOmittedProduct_zero_source_eq_deleted]
  exact (congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient hp hp1 n) _).trans
    (freeSineQuotient_center n)

end NLS.ZakharovShabat
