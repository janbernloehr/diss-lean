import NLS.ZakharovShabat.SingleSpectralFiniteChangeRatio
import NLS.ZakharovShabat.SourceFiniteGap
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic

/-! # A finite product for the actual finite-gap boundary quotient

At every closed periodic gap both ordinary boundary roots coincide.
Consequently the Dirichlet/Neumann characteristic quotient has only the
finitely many open-gap factors, with the exact original normalization.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Closing every gap outside a finite set cancels those boundary factors exactly. -/
theorem sourceBoundaryCharacteristic_ratio_of_closed_off_finset
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (s : Finset ℤ)
    (hs : ∀ n ∉ s, canonicalPeriodicGap hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (z : ℂ) (hz : ∀ n : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n ≠ z) :
    periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z /
      periodOneBoundaryCharacteristic hp hp1 .neumann φ z =
      ∏ n ∈ s, (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n-z) /
        (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n-z) := by
  have he (n : ℤ) (hn : n ∉ s) :
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n =
        canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n := by
    have he := (sub_eq_zero.mp (hs n hn)).symm
    exact (canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap hp hp1 .dirichlet φ hφ n he).trans
      (canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap hp hp1 .neumann φ hφ n he).symm
  rw [periodOneBoundaryCharacteristic_eq_canonicalProduct,
    periodOneBoundaryCharacteristic_eq_canonicalProduct]
  change ((-1/2 : ℂ) * entireSingleSpectralProduct _ z) /
      ((-1/2 : ℂ) * entireSingleSpectralProduct _ z) = _
  rw [mul_div_mul_left _ _ (by norm_num : (-1/2 : ℂ) ≠ 0)]
  exact entireSingleSpectralProduct_ratio_of_finite_change hp _ _
    (sourceBoundaryDisplacement hp hp1 .dirichlet φ).property
    (sourceBoundaryDisplacement hp hp1 .neumann φ).property s he z hz

/-- An actual finite-gap source has one finite boundary-quotient formula valid off the real axis. -/
theorem exists_sourceFiniteGap_boundaryCharacteristic_ratio
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ s : Finset ℤ,
      (∀ n : ℤ, n ∈ s ↔ canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) ∧
      ∀ z : ℂ, z.im ≠ 0 →
        periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val z /
          periodOneBoundaryCharacteristic hp hp1 .neumann φ.val z =
        ∏ n ∈ s, (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n-z) /
          (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ.val n-z) := by
  classical
  let s : Finset ℤ := hf.toFinset
  have hs (n : ℤ) : n ∈ s ↔ canonicalPeriodicGap hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 :=
    Set.Finite.mem_toFinset hf
  refine ⟨s,hs,fun z hz => ?_⟩
  apply sourceBoundaryCharacteristic_ratio_of_closed_off_finset hp hp1 φ.val φ.property s
  · intro n hn
    exact not_ne_iff.mp (fun hg => hn ((hs n).mpr hg))
  · intro n he
    apply hz
    rw [← he]
    exact canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .neumann φ.val φ.property n

/-- Two real boundary roots in the same indexed gap differ by at most its length. -/
theorem norm_boundaryRoots_sub_le_periodicGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (b c : BoundaryCondition) (n : ℤ) :
    ‖canonicalPeriodOneBoundaryRoots hp hp1 b φ n - canonicalPeriodOneBoundaryRoots hp hp1 c φ n‖ ≤
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ := by
  have hb := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hφ n
  have hc := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 c φ hφ n
  have him : (canonicalPeriodOneBoundaryRoots hp hp1 b φ n -
      canonicalPeriodOneBoundaryRoots hp hp1 c φ n).im = 0 := by
    simp only [sub_im, canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ n,
      canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 c φ hφ n, sub_self]
  calc
    _ ≤ |(canonicalPeriodOneBoundaryRoots hp hp1 b φ n).re -
        (canonicalPeriodOneBoundaryRoots hp hp1 c φ n).re| := by
      simpa only [him, abs_zero, add_zero, sub_re] using
        Complex.norm_le_abs_re_add_abs_im (canonicalPeriodOneBoundaryRoots hp hp1 b φ n -
          canonicalPeriodOneBoundaryRoots hp hp1 c φ n)
    _ ≤ (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re := by
      apply abs_le.mpr
      constructor <;> linarith [hb.1, hb.2, hc.1, hc.2]
    _ ≤ _ := by
      simpa only [canonicalPeriodicGap, sub_re] using Complex.re_le_norm
        (canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)

end NLS.ZakharovShabat
