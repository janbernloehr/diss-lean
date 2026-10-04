import NLS.ZakharovShabat.SourcePsiSharedActualGapMajorant
import NLS.ZakharovShabat.SourceAbelianMomentSquareMajorants
import NLS.ZakharovShabat.SourceAbelianMomentSecondError

/-! # The actual diagonal second-moment error sequence

The shared quotient majorant controls every diagonal regular numerator.
Combining it with the square-error sequence yields one refined sequence
for the difference from the leading pi term. The exact factorization
also holds at collapsed gaps, where the coefficient is defined as zero
by the totalized quotient and the actual moment vanishes.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual diagonal correction to the leading pi term. -/
def sourceSecondMomentDiagonalCoefficient (A : SourceAbelianMomentAtlas hp hp1 W s)
    (ψ : CoeffPair p) (k : ℤ) : ℂ :=
  4*(A.moment k k 2 ψ-(Real.pi:ℂ)*(sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4)/
    (sourcePeriodicGapDisplacement hp hp1 ψ k)^2

variable {A : SourceAbelianMomentAtlas hp hp1 W s}
namespace SourceAbelianMomentErrorDomain

/-- The diagonal coefficient estimate uses the actual filled quotient,
with the normalization constant and the closed-gap case explicit. -/
theorem diagonal_coefficient_bound
    (D : SourceAbelianMomentErrorDomain A) (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (k : ℤ) (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hS : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)+sourceAngularSelectedPolynomial hp hp1 ψ k z‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*E)
    (hQ : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceSingleRootQuotientJointProduct hp hp1 k
        (z,(sourcePsiFillDeletedRoot k (s k ψ) (sourceStandardRootMidpoint hp hp1 ψ k),ψ))-1‖ ≤ F) :
    ‖sourceSecondMomentDiagonalCoefficient A ψ k‖ ≤ 8*Real.pi*(E*(F+1)+F/4) ∧
      A.moment k k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4*
        ((Real.pi:ℂ)+sourceSecondMomentDiagonalCoefficient A ψ k) := by
  have hR : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceMomentRegularNumerator hp hp1 k k (s k ψ : Coeff p) ψ z-Complex.I‖ ≤ F := by
    intro z hz
    rw [← sourceMomentRegularNumerator_fillDeletedRoot hp hp1 k k (s k ψ)
      (sourceStandardRootMidpoint hp hp1 ψ k),sourceMomentRegularNumerator_diagonal]
    rw [← mul_sub_one,norm_mul,norm_I,one_mul]
    exact hQ z hz
  have hb := D.diagonal_error_bound ψ hψ k E F hE hS hR
  rw [← sourcePeriodicGapDisplacement_apply hp hp1 ψ k] at hb
  rw [norm_mul,norm_inv,norm_mul,norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] at hb
  have hb' : ‖A.moment k k 2 ψ-(Real.pi:ℂ)*(sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*(E*(F+1)+F/4)*(2*Real.pi) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mp
    simpa only [div_eq_mul_inv,mul_comm] using hb
  by_cases hγ : sourcePeriodicGapDisplacement hp hp1 ψ k = 0
  · have hz : A.moment k k 2 ψ = 0 := by
      simp only [hγ,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_div,sub_zero,zero_mul] at hb'
      exact norm_eq_zero.mp (le_antisymm hb' (norm_nonneg _))
    constructor
    · simp only [sourceSecondMomentDiagonalCoefficient,hγ,zero_pow (by norm_num : (2:ℕ) ≠ 0),div_zero,norm_zero]
      positivity
    · simp only [hz,hγ,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,zero_mul]
  · constructor
    · unfold sourceSecondMomentDiagonalCoefficient
      rw [norm_div,norm_mul,norm_ofNat,norm_pow]
      apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hγ) 2)).mpr
      nlinarith
    · unfold sourceSecondMomentDiagonalCoefficient
      field_simp
      ring

/-- One locally uniform refined sequence describes all actual diagonal
second moments. Its source neighborhood precedes the exponent. -/
theorem exists_local_diagonal_secondMoment_coefficients
    (D : SourceAbelianMomentErrorDomain A)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφV : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ D.domain ∩ V ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∃ a : Coeff r,
          (∀ k, a k = sourceSecondMomentDiagonalCoefficient A ψ k) ∧ ‖a‖ ≤ M ∧
          ∀ k : ℤ, A.moment k k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4*((Real.pi:ℂ)+a k) := by
  obtain ⟨Ts,hTs,hφs,_,hsquare⟩ := A.exists_local_refined_square_gap_majorants φ
  obtain ⟨Tf,hTf,hφf,hfV,hquot⟩ := hs.exists_local_shared_actualGap_quotient_majorant φ hφV
  refine ⟨(Ts ∩ Tf) ∩ D.domain,(hTs.inter hTf).inter D.isOpen_domain,
    ⟨⟨hφs,hφf⟩,D.real_subset φ.property⟩,fun _ h => ⟨h.2,hfV h.1.2⟩,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨Ms,hMs,hsrows⟩ := hsquare r hr hr1 hpr
  obtain ⟨Mf,hMf,hfrows⟩ := hquot r hr hr1 hpr
  let L := 8*Real.pi*(Mf+1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨L*(Ms+Mf),by positivity,?_⟩
  intro ψ hψ
  obtain ⟨E,hE,hS⟩ := hsrows ψ hψ.1.1
  obtain ⟨F,hF,hQ⟩ := hfrows ψ hψ.1.2
  let B := (L:ℂ) • (Coeff.magnitude E+Coeff.magnitude F)
  have hBpoint (k : ℤ) : ‖B k‖ = L*(‖E k‖+‖F k‖) := by
    simp only [B,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hL,
      lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,Complex.norm_real]
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hBnorm : ‖B‖ ≤ L*(Ms+Mf) := by
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hL]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (by simpa only [Coeff.norm_magnitude] using add_le_add hE hF)) hL
  have hcoeff (k : ℤ) := D.diagonal_coefficient_bound ψ hψ.2 k ‖E k‖ ‖F k‖
    (norm_nonneg _) (norm_nonneg _) (hS k) (hQ k k)
  have hpoint (k : ℤ) : ‖sourceSecondMomentDiagonalCoefficient A ψ k‖ ≤ ‖B k‖ := by
    apply (hcoeff k).1.trans
    rw [hBpoint]
    have hk : ‖F k‖ ≤ Mf := (lp.norm_apply_le_norm (zero_lt_one.trans hr1).ne' F k).trans hF
    have herror : ‖E k‖*(‖F k‖+1)+‖F k‖/4 ≤ (Mf+1)*(‖E k‖+‖F k‖) := by
      nlinarith [norm_nonneg (F k),mul_nonneg (norm_nonneg (E k)) (sub_nonneg.mpr hk),mul_nonneg hMf (norm_nonneg (F k))]
    dsimp only [L]
    nlinarith [mul_le_mul_of_nonneg_left herror (by positivity : 0 ≤ 8*Real.pi)]
  let a : Coeff r := ⟨sourceSecondMomentDiagonalCoefficient A ψ,(lp.memℓp B).mono' hpoint⟩
  exact ⟨a,fun k => rfl,(lp.norm_mono (zero_lt_one.trans hr1).ne' hpoint).trans hBnorm,
    fun k => (hcoeff k).2⟩

end SourceAbelianMomentErrorDomain
end NLS.ZakharovShabat
