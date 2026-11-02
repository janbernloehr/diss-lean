import NLS.KdV.HillReduction
import NLS.SequenceSpaces.SobolevHomogeneous
import NLS.SequenceSpaces.SobolevEmbedding

/-!
# The Sobolev domain of the Fourier Hill operator

The second-order domain is the actual weighted Hilbert space, with weight
`(1+abs(k))^2`. Every summable Fourier eigenvector automatically lies in
this domain. Consequently the two-mode determinant criterion applies to
the constructed operator on this domain, rather than to a formal equation
with an unproved regularity hypothesis.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- A square-summable Hill second moment recovers the full H2 coefficient norm. -/
theorem memlp_sobolev_two_of_hillMoment (a : Coeff 2)
    (hm : Memℓp (fun k => (freeHillValue k : ℂ)*a k) 2) :
    Memℓp (fun k => (Weight.sobolev 2 k : ℂ)*a k) 2 := by
  have hb := ((lp.memℓp a).norm.add hm.norm).const_mul (2 : ℝ)
  apply hb.mono
  intro k
  have hpos : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
  have he : ‖(freeHillValue k : ℂ)*a k‖ = freeHillValue k*‖a k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
  have hw : Weight.sobolev 2 k ≤ 2*(1+freeHillValue k) := by
    simp only [Weight.sobolev_apply, Real.rpow_two, freeHillValue]
    have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_abs (k : ℝ), sq_nonneg (|(k : ℝ)|-1),
      mul_nonneg (sub_nonneg.mpr hpi) (sq_nonneg (k : ℝ))]
  change ‖(Weight.sobolev 2 k : ℂ)*a k‖ ≤ 2*(‖a k‖+‖(freeHillValue k : ℂ)*a k‖)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Weight.sobolev 2 |>.positive k).le]
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hw (norm_nonneg (a k))]

/-- The periodic second-order Hilbert coefficient domain. -/
abbrev HillSobolevDomain := WeightedCoeff (Weight.sobolev 2) 2

/-- H2 domain inclusion into the existing one-derivative domain. -/
def hillDomainToH1 : HillSobolevDomain →L[ℂ] WeightedCoeff (Weight.sobolev 1) 2 :=
  WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ) ≤ 2)

/-- The Sobolev domain is continuously included in absolutely summable coefficients. -/
def hillDomainToL1 : HillSobolevDomain →L[ℂ] Coeff 1 :=
  (WeightedCoeff.sobolevToL1CLM 2 (by simp)).comp hillDomainToH1

@[simp] theorem hillDomainToL1_apply (f : HillSobolevDomain) (k : ℤ) :
    hillDomainToL1 f k = f.val k := by simp [hillDomainToL1, hillDomainToH1]

/-- The same domain, included in the underlying Hilbert space. -/
def hillDomainToL2 : HillSobolevDomain →L[ℂ] Coeff 2 :=
  WeightedCoeff.sobolevToL2 (by norm_num : (0 : ℝ) ≤ 2)

@[simp] theorem hillDomainToL2_apply (f : HillSobolevDomain) (k : ℤ) :
    hillDomainToL2 f k = f.val k := WeightedCoeff.sobolevToL2_apply _ f k

theorem hillDomainToL2_injective : Function.Injective hillDomainToL2 := by
  intro f g he
  apply Subtype.ext
  funext k
  simpa only [hillDomainToL2_apply] using congrArg (fun a : Coeff 2 => a k) he

/-- The positive free Hill operator, with symbol pi^2*k^2, on its H2 domain. -/
def hillLaplacian : HillSobolevDomain →L[ℂ] Coeff 2 :=
  (WeightedCoeff.weightIsometry Weight.one 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM (Weight.sobolev 2) Weight.one
      (fun k => (freeHillValue k : ℂ)) (Real.pi^2) (by positivity) (by
        intro k
        have hpos : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
        rw [Weight.one_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
        simp only [freeHillValue, Weight.sobolev_apply, Real.rpow_two]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg Real.pi)
        nlinarith [sq_abs (k : ℝ), abs_nonneg (k : ℝ)]))

@[simp] theorem hillLaplacian_apply (f : HillSobolevDomain) (k : ℤ) :
    hillLaplacian f k = (freeHillValue k : ℂ)*f.val k := by
  simp [hillLaplacian, WeightedCoeff.weightIsometry, WeightedCoeff.weightEquiv_apply]

/-- The Hill operator on the actual H2 coefficient domain for an arbitrary L2 potential. -/
def hillOperator (q : Coeff 2) : HillSobolevDomain →L[ℂ] Coeff 2 :=
  hillLaplacian + (Coeff.convolutionCLM q).comp hillDomainToL1

theorem hillOperator_apply (q : Coeff 2) (f : HillSobolevDomain) (k : ℤ) :
    hillOperator q f k = (freeHillValue k : ℂ)*f.val k +
      ∑' j : ℤ, q (k-j)*f.val j := by
  simp [hillOperator, Coeff.convolution_apply]

/-- Domain data in the unit-weight summable space used by the two-mode reduction. -/
def hillDomainAsSummable : HillSobolevDomain →L[ℂ] WeightedCoeff SpectralWeight.one.toWeight 1 :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    hillDomainToL1

@[simp] theorem hillDomainAsSummable_apply (f : HillSobolevDomain) (k : ℤ) :
    (hillDomainAsSummable f).val k = f.val k := by
  change hillDomainToL1 f k / (SpectralWeight.one k : ℂ) = _
  simp

theorem hillDomainAsSummable_injective : Function.Injective hillDomainAsSummable := by
  intro f g h
  apply Subtype.ext
  funext k
  simpa using congrArg (fun b : WeightedCoeff SpectralWeight.one.toWeight 1 => b.val k) h

/-- The operator eigen-equation is exactly the full Fourier equation on its domain. -/
theorem hillOperator_eigen_iff (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (z : ℂ) (f : HillSobolevDomain) :
    hillOperator (SpectralWeight.one.toCoeff q) f = z • hillDomainToL2 f ↔
      IsHillFourierEigenvector SpectralWeight.one q z (hillDomainAsSummable f) := by
  constructor
  · intro he k
    have hk := congrArg (fun a : Coeff 2 => a k) he
    simp only [hillOperator_apply, SpectralWeight.toCoeff_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, hillDomainToL2_apply] at hk
    change (z-(freeHillValue k : ℂ))*(hillDomainAsSummable f).val k = _
    simp only [hillDomainAsSummable_apply, SpectralWeight.convolution_apply]
    linear_combination -hk
  · intro hf
    ext k
    have hk := hf k
    simp only [hillDomainAsSummable_apply, SpectralWeight.convolution_apply] at hk
    simp only [hillOperator_apply, SpectralWeight.toCoeff_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, hillDomainToL2_apply]
    linear_combination -hk

/-- Eigenvectors from the determinant reduction have H2 regularity automatically. -/
theorem hillFourierEigenvector_memlp_sobolev_two
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillFourierEigenvector SpectralWeight.one q z f) :
    Memℓp (fun k => (Weight.sobolev 2 k : ℂ)*f.val k) 2 := by
  let a : Coeff 2 := SpectralWeight.one.toCoeff
    (WeightedCoeff.exponentInclusion SpectralWeight.one.toWeight (by norm_num : (1 : ℝ≥0∞) ≤ 2) f)
  have ha (k : ℤ) : a k = f.val k := by simp [a]
  have hm : Memℓp (fun k => (freeHillValue k : ℂ)*a k) 2 := by
    have he (k : ℤ) : (freeHillValue k : ℂ)*a k =
        (z • a - SpectralWeight.one.toCoeff (SpectralWeight.one.convolution q f)) k := by
      simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        SpectralWeight.toCoeff_apply, ha]
      rw [← hf k]
      ring
    simp only [he]
    exact lp.memℓp _
  simpa only [ha] using memlp_sobolev_two_of_hillMoment a hm

/-- The recovered domain element retains every original raw coefficient. -/
def hillEigenvectorLift (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillFourierEigenvector SpectralWeight.one q z f) : HillSobolevDomain :=
  ⟨f.val, hillFourierEigenvector_memlp_sobolev_two q z f hf⟩

@[simp] theorem hillEigenvectorLift_apply (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (z : ℂ) (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillFourierEigenvector SpectralWeight.one q z f) (k : ℤ) :
    (hillEigenvectorLift q z f hf).val k = f.val k := rfl

@[simp] theorem hillDomainAsSummable_eigenvectorLift
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillFourierEigenvector SpectralWeight.one q z f) :
    hillDomainAsSummable (hillEigenvectorLift q z f hf) = f := by
  apply Subtype.ext
  funext k
  simp

/-- The determinant criterion now uses eigenvectors in the genuine H2 coefficient domain. -/
theorem hillReduced_det_eq_zero_iff_domainEigenvector
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    (hillReducedOperator SpectralWeight.one q n hn z hz hcut).toLinearMap.det = 0 ↔
      ∃ f : HillSobolevDomain, f ≠ 0 ∧
        hillOperator (SpectralWeight.one.toCoeff q) f = z • hillDomainToL2 f := by
  rw [hillReduced_det_eq_zero_iff]
  constructor
  · rintro ⟨f, hf0, hf⟩
    refine ⟨hillEigenvectorLift q z f hf, ?_, (hillOperator_eigen_iff q z _).mpr ?_⟩
    · intro hlift
      have he := congrArg hillDomainAsSummable hlift
      simp only [hillDomainAsSummable_eigenvectorLift, map_zero] at he
      exact hf0 he
    · simpa using hf
  · rintro ⟨f, hf0, hf⟩
    refine ⟨hillDomainAsSummable f, ?_, (hillOperator_eigen_iff q z f).mp hf⟩
    exact fun hzero => hf0 (hillDomainAsSummable_injective (hzero.trans (map_zero _).symm))

end NLS.KdV
