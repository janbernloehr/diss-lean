import NLS.KdV.HillWeightIndependence
import NLS.SequenceSpaces.Pairing

/-! # Symmetry and real characteristic roots of the physical Hill operator

A real scalar potential has conjugate-reflected Fourier coefficients.
The existing absolutely convergent convolution adjoint identity and the
real free Hill symbol prove symmetry on the actual H2 domain. Positive
Hilbert energy then forces every eigenvalue to be real. No first-order
self-adjointness assertion is substituted for this Hill calculation.
-/

noncomputable section
open scoped ENNReal ComplexConjugate
open MeasureTheory
namespace NLS.KdV

/-- Fourier reality of the scalar physical potential. Individual Fourier
coefficients need not be real. -/
def IsRealHillPotential (q : Coeff 2) : Prop := ∀ k : ℤ, q (-k) = conj (q k)

theorem IsRealHillPotential.smul_real {q : Coeff 2} (hq : IsRealHillPotential q) (t : ℝ) :
    IsRealHillPotential ((t : ℂ) • q) := by
  intro k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, hq k]

/-- Almost-everywhere reality of the actual L2 function gives precisely
the conjugate-reflected Fourier condition used below. -/
theorem isRealHillPotential_of_physical (q : Coeff 2)
    (hq : ∀ᵐ x : AddCircle (2 : ℝ) ∂AddCircle.haarAddCircle,
      conj (Fourier.l2Synthesis q x) = Fourier.l2Synthesis q x) : IsRealHillPotential q := by
  intro k
  rw [← Fourier.fourierCoeff_l2Synthesis q (-k), ← Fourier.fourierCoeff_l2Synthesis q k]
  simp only [fourierCoeff, neg_neg, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [hq] with x hx
  simp only [map_mul, hx, ← fourier_neg, neg_neg]

theorem hillDomain_pairing_conj (f g : HillSobolevDomain) :
    conj (Coeff.pairing (hillDomainToL2 g) (hillDomainToL1 f)) =
      Coeff.pairing (hillDomainToL2 f) (hillDomainToL1 g) := by
  unfold Coeff.pairing
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [hillDomainToL2_apply, hillDomainToL1_apply, map_mul, starRingEnd_self_apply]
  ring

/-- The quadratic pairing is the exact normalized Hilbert energy. -/
theorem hillDomain_pairing_self (f : HillSobolevDomain) :
    Coeff.pairing (hillDomainToL2 f) (hillDomainToL1 f) = (‖hillDomainToL2 f‖^2 : ℝ) := by
  rw [Coeff.pairing_self_eq _ _ (fun k => by simp)]
  congr 1
  have h := (lp.hasSum_norm (p := 2) (by norm_num) (hillDomainToL2 f)).tsum_eq
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.normSq_eq_norm_sq] using h

theorem hillDomain_pairing_self_re_pos (f : HillSobolevDomain) (hf : f ≠ 0) :
    0 < (Coeff.pairing (hillDomainToL2 f) (hillDomainToL1 f)).re := by
  have hne : hillDomainToL2 f ≠ 0 :=
    fun hz => hf (hillDomainToL2_injective (hz.trans (map_zero _).symm))
  rw [hillDomain_pairing_self, Complex.ofReal_re]
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

theorem hillLaplacian_pairing_symmetric (f g : HillSobolevDomain) :
    Coeff.pairing (hillLaplacian f) (hillDomainToL1 g) =
      conj (Coeff.pairing (hillLaplacian g) (hillDomainToL1 f)) := by
  unfold Coeff.pairing
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [hillLaplacian_apply, hillDomainToL1_apply, map_mul,
    Complex.conj_ofReal, starRingEnd_self_apply]
  ring

/-- The actual Hill operator is symmetric on its genuine H2 domain. -/
theorem hillOperator_pairing_symmetric (q : Coeff 2) (hq : IsRealHillPotential q)
    (f g : HillSobolevDomain) :
    Coeff.pairing (hillOperator q f) (hillDomainToL1 g) =
      conj (Coeff.pairing (hillOperator q g) (hillDomainToL1 f)) := by
  change Coeff.pairing (hillLaplacian f+Coeff.convolution q (hillDomainToL1 f)) (hillDomainToL1 g) =
    conj (Coeff.pairing (hillLaplacian g+Coeff.convolution q (hillDomainToL1 g)) (hillDomainToL1 f))
  rw [Coeff.pairing_add_left, Coeff.pairing_add_left, map_add, hillLaplacian_pairing_symmetric]
  congr 1
  exact Coeff.pairing_convolution_conj q q
    (fun k => by simpa only [neg_neg] using hq (-k)) (hillDomainToL1 f) (hillDomainToL1 g)

theorem hillOperator_quadratic_im_zero (q : Coeff 2) (hq : IsRealHillPotential q)
    (f : HillSobolevDomain) :
    (Coeff.pairing (hillOperator q f) (hillDomainToL1 f)).im = 0 := by
  have h := congrArg Complex.im (hillOperator_pairing_symmetric q hq f f)
  simp only [Complex.conj_im] at h
  linarith

/-- Every nonzero periodic H2 eigenvector for a real L2 potential has a real eigenvalue. -/
theorem hillEigenvalue_im_zero (q : Coeff 2) (hq : IsRealHillPotential q)
    (lambda : ℂ) (f : HillSobolevDomain) (hf : f ≠ 0)
    (he : hillOperator q f = lambda • hillDomainToL2 f) : lambda.im = 0 := by
  have hp := hillDomain_pairing_self_re_pos f hf
  have hi : (Coeff.pairing (hillDomainToL2 f) (hillDomainToL1 f)).im = 0 := by
    rw [hillDomain_pairing_self]
    rfl
  have h := hillOperator_quadratic_im_zero q hq f
  rw [he, Coeff.pairing_smul_left] at h
  simp only [Complex.mul_im, hi, mul_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_right (ne_of_gt hp)

/-- Distinct physical Hill eigenvalues have orthogonal eigenvectors,
in the actual normalized coefficient Hilbert pairing. -/
theorem hillEigenvectors_orthogonal (q : Coeff 2) (hq : IsRealHillPotential q)
    (lambda mu : ℂ) (hneq : lambda ≠ mu) (f g : HillSobolevDomain)
    (hef : hillOperator q f = lambda • hillDomainToL2 f)
    (heg : hillOperator q g = mu • hillDomainToL2 g) :
    Coeff.pairing (hillDomainToL2 f) (hillDomainToL1 g) = 0 := by
  by_cases hg : g = 0
  · subst g
    simp [Coeff.pairing]
  have hmu := hillEigenvalue_im_zero q hq mu g hg heg
  have hc : conj mu = mu := by
    apply Complex.ext <;> simp [hmu]
  have h := hillOperator_pairing_symmetric q hq f g
  rw [hef, heg, Coeff.pairing_smul_left, Coeff.pairing_smul_left, map_mul,
    hillDomain_pairing_conj, hc] at h
  have hz : (lambda-mu)*Coeff.pairing (hillDomainToL2 f) (hillDomainToL1 g) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hneq)

/-- A real Hill eigenvector cannot be the image of an associated vector.
This rules out a nontrivial length-two Jordan chain on the actual domain. -/
theorem hillEigenvector_no_associatedVector (q : Coeff 2) (hq : IsRealHillPotential q)
    (lambda : ℂ) (f : HillSobolevDomain) (hf : f ≠ 0)
    (hef : hillOperator q f = lambda • hillDomainToL2 f) (g : HillSobolevDomain) :
    hillOperator q g-lambda • hillDomainToL2 g ≠ hillDomainToL2 f := by
  intro hg
  have him := hillEigenvalue_im_zero q hq lambda f hf hef
  have hc : conj lambda = lambda := by apply Complex.ext <;> simp [him]
  have h := congrArg (fun a : Coeff 2 => Coeff.pairing a (hillDomainToL1 f))
    (sub_eq_iff_eq_add.mp hg)
  rw [Coeff.pairing_add_left, Coeff.pairing_smul_left, hillOperator_pairing_symmetric q hq g f,
    hef, Coeff.pairing_smul_left, map_mul, hillDomain_pairing_conj, hc] at h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re] at hr
  linarith [hillDomain_pairing_self_re_pos f hf]

/-- Every actual energy-characteristic root for a real period-one L2 potential is real. -/
theorem hillL2Discriminant_root_im_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (lambda : ℂ) (hd : hillL2Discriminant (SpectralWeight.one.toCoeff q) lambda ^ 2 = 4) :
    lambda.im = 0 := by
  obtain ⟨f, hf, he⟩ := (hill_eigenvector_iff_l2Discriminant q heven lambda).mpr hd
  exact hillEigenvalue_im_zero _ hreal lambda f hf he

theorem hillReduced_real_root_im_zero (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (heven : w.toCoeff q ∈ Coeff.paritySubspace 0) (hreal : IsRealHillPotential (w.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (lambda : ℂ) (hz : lambda ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (hd : hillReducedDeterminant w n (q,lambda) = 0) :
    lambda.im = 0 := by
  have heven1 : SpectralWeight.one.toCoeff (hillForgetWeight w 2 q) ∈ Coeff.paritySubspace 0 := by
    rwa [toCoeff_hillForgetWeight]
  have hreal1 : IsRealHillPotential (SpectralWeight.one.toCoeff (hillForgetWeight w 2 q)) := by
    rwa [toCoeff_hillForgetWeight]
  have hD := (hillReduced_weighted_zero_iff_l2Discriminant w q heven n hn lambda hz hcut).mp hd
  rw [← toCoeff_hillForgetWeight w 2 q] at hD
  exact hillL2Discriminant_root_im_zero _ heven1 hreal1 lambda hD

end NLS.KdV
