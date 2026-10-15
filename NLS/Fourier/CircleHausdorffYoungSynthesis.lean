import NLS.Fourier.PolynomialHausdorffYoung

/-!
# Continuous Fourier synthesis into physical Lp spaces

Finite polynomial synthesis extends by density to a continuous linear map
with norm at most one. Coefficient recovery identifies its actual Lp representative
with the original periodic distribution.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Finite coefficient data realized in the actual Lᑫ quotient. -/
def finiteCircleSynthesis : (ℤ →₀ ℂ) →ₗ[ℂ] Lp ℂ q (AddCircle.haarAddCircle (T := L)) :=
  (ContinuousMap.toLp q AddCircle.haarAddCircle ℂ).toLinearMap.comp (Finsupp.linearCombination ℂ fourier)

theorem finiteCircleSynthesis_eq (a : ℤ →₀ ℂ) :
    finiteCircleSynthesis (L := L) (q := q) a =
      ContinuousMap.toLp q AddCircle.haarAddCircle ℂ (continuousFourierPolynomial a.support a) := rfl

omit [Fact (1 ≤ p)] in
theorem norm_ofFinsupp_eq_piLp (hp : 0 < p.toReal) (a : ℤ →₀ ℂ) :
    ‖Coeff.ofFinsupp (p := p) a‖ = ‖WithLp.toLp p (fun n : a.support => a n.val)‖ := by
  rw [lp.norm_eq_tsum_rpow hp,PiLp.norm_eq_sum hp]
  congr 1
  rw [tsum_eq_sum (s := a.support) (fun n hn => by simp [Coeff.ofFinsupp_apply,Finsupp.notMem_support_iff.mp hn,hp.ne'])]
  simp only [Coeff.ofFinsupp_apply]
  exact (Finset.sum_attach a.support (fun n => ‖a n‖^p.toReal)).symm

theorem norm_finiteCircleSynthesis_le_finite (hp₂ : p ≤ 2) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (a : ℤ →₀ ℂ) : ‖finiteCircleSynthesis (L := L) (q := q) a‖ ≤ ‖Coeff.ofFinsupp (p := p) a‖ := by
  rw [finiteCircleSynthesis_eq,norm_ofFinsupp_eq_piLp hp]
  exact norm_polynomial_toLp_le hp₂ hp hq a.support a

/-- The ℓ¹ endpoint includes the actual L∞ quotient. -/
theorem norm_finiteCircleSynthesis_le_top (a : ℤ →₀ ℂ) :
    ‖finiteCircleSynthesis (L := L) (q := ⊤) a‖ ≤ ‖Coeff.ofFinsupp (p := 1) a‖ := by
  have ht : ‖ContinuousMap.toLp (E := ℂ) ⊤ (AddCircle.haarAddCircle (T := L)) ℂ‖ ≤ 1 := by
    simpa using ContinuousMap.toLp_norm_le (p := ⊤) (𝕜 := ℂ) (μ := AddCircle.haarAddCircle (T := L)) (E := ℂ)
  rw [finiteCircleSynthesis_eq]
  calc
    _ ≤ ‖continuousFourierPolynomial (L := L) a.support a‖ := by
      simpa only [one_mul] using (ContinuousMap.toLp (E := ℂ) ⊤ (AddCircle.haarAddCircle (T := L)) ℂ).le_of_opNorm_le ht
        (continuousFourierPolynomial (L := L) a.support a)
    _ ≤ ∑ n ∈ a.support, ‖a n‖ := by
      unfold continuousFourierPolynomial
      simpa only [norm_smul,fourier_norm,mul_one] using
        norm_sum_le a.support (fun n => a n • (fourier n : C(AddCircle L,ℂ)))
    _ = _ := by
      rw [norm_ofFinsupp_eq_piLp (p := 1) (by simp),PiLp.norm_eq_sum (by simp : 0 < (1:ℝ≥0∞).toReal)]
      simp only [ENNReal.toReal_one,Real.rpow_one,div_self one_ne_zero]
      exact (Finset.sum_attach a.support (fun n => ‖a n‖)).symm

/-- Constant-one synthesis estimate for the full inclusive range 1 ≤ p ≤ 2. -/
theorem norm_finiteCircleSynthesis_le (hp₂ : p ≤ 2) (a : ℤ →₀ ℂ) :
    ‖finiteCircleSynthesis (L := L) (q := q) a‖ ≤ ‖Coeff.ofFinsupp (p := p) a‖ := by
  by_cases hq : q = ⊤
  · have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq
    subst p
    subst q
    exact norm_finiteCircleSynthesis_le_top a
  · exact norm_finiteCircleSynthesis_le_finite hp₂
      ((ENNReal.toReal_pos_iff_ne_top p).mpr (ne_top_of_le_ne_top (by norm_num) hp₂))
      ((ENNReal.toReal_pos_iff_ne_top q).mpr hq) a

/-- Continuous extension of polynomial synthesis; its estimates apply for 1 ≤ p ≤ 2. -/
def circleSynthesis : Coeff p →L[ℂ] Lp ℂ q (AddCircle.haarAddCircle (T := L)) :=
  finiteCircleSynthesis.extendOfNorm Coeff.ofFinsupp

theorem circleSynthesis_finite (hp₂ : p ≤ 2)
    (a : ℤ →₀ ℂ) : circleSynthesis (L := L) (p := p) (q := q) (Coeff.ofFinsupp a) = finiteCircleSynthesis a := by
  apply LinearMap.extendOfNorm_eq (f := finiteCircleSynthesis (L := L) (q := q))
    (e := Coeff.ofFinsupp (p := p)) (Coeff.denseRange_ofFinsupp (ne_top_of_le_ne_top (by norm_num) hp₂))
  exact ⟨1,fun a => by simpa only [one_mul] using norm_finiteCircleSynthesis_le hp₂ a⟩

theorem norm_circleSynthesis_le (hp₂ : p ≤ 2) :
    ‖circleSynthesis (L := L) (p := p) (q := q)‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (f := finiteCircleSynthesis (L := L) (q := q))
    (e := Coeff.ofFinsupp (p := p)) (Coeff.denseRange_ofFinsupp (ne_top_of_le_ne_top (by norm_num) hp₂)) zero_le_one
  intro a
  simpa only [one_mul] using norm_finiteCircleSynthesis_le hp₂ a

end NLS.Fourier

namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem integral_norm_circleLp_le (f : Lp ℂ q (AddCircle.haarAddCircle (T := L))) :
    (∫ x, ‖f x‖ ∂AddCircle.haarAddCircle) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.memLp f).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (Fact.out : 1 ≤ q) (Lp.memLp f).aestronglyMeasurable)

/-- A continuous Fourier-coefficient functional on any Banach Lᑫ space. -/
def circleLpCoefficient (n : ℤ) : Lp ℂ q (AddCircle.haarAddCircle (T := L)) →L[ℂ] ℂ :=
  let F : Lp ℂ q (AddCircle.haarAddCircle (T := L)) →ₗ[ℂ] ℂ := {
    toFun f := fourierCoeff f n
    map_add' f g := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),fourierCoeff.add
        ((Lp.memLp f).integrable (Fact.out : 1 ≤ q)) ((Lp.memLp g).integrable (Fact.out : 1 ≤ q))]
      rfl
    map_smul' c f := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f),fourierCoeff.const_smul]
      rfl }
  F.mkContinuous 1 (by
    intro f
    change ‖fourierCoeff f n‖ ≤ 1*‖f‖
    simpa only [one_mul] using (norm_fourierCoeff_le_integral_norm f n).trans (integral_norm_circleLp_le f))

theorem circleLpCoefficient_apply (n : ℤ) (f : Lp ℂ q (AddCircle.haarAddCircle (T := L))) :
    circleLpCoefficient n f = fourierCoeff f n := rfl

theorem finiteCircleSynthesis_coefficient (a : ℤ →₀ ℂ) (n : ℤ) :
    fourierCoeff (finiteCircleSynthesis (L := L) (q := q) a) n = a n := by
  rw [finiteCircleSynthesis_eq,fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _),
    continuousFourierPolynomial_coefficient]
  split_ifs with hn
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hn).symm

variable [p.HolderConjugate q]
/-- Synthesis recovers every coefficient, including at p = 1, q = ∞. -/
theorem circleSynthesis_coefficient (hp₂ : p ≤ 2)
    (a : Coeff p) (n : ℤ) : fourierCoeff (circleSynthesis (L := L) (q := q) a) n = a n := by
  have he : (fun a : Coeff p => circleLpCoefficient (L := L) (q := q) n (circleSynthesis a)) = fun a => a n := by
    apply (Coeff.denseRange_ofFinsupp (ne_top_of_le_ne_top (by norm_num) hp₂)).equalizer
      ((circleLpCoefficient n).continuous.comp circleSynthesis.continuous) (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous
    funext b
    change circleLpCoefficient (L := L) (q := q) n (circleSynthesis (Coeff.ofFinsupp b)) = b n
    rw [circleSynthesis_finite hp₂,circleLpCoefficient_apply,finiteCircleSynthesis_coefficient]
  exact congrFun he a

open SmoothPeriodicTest

/-- The synthesized function represents the full original smooth-test distribution. -/
theorem circleSynthesis_represents (hp₂ : p ≤ 2)
    (u : PeriodicFourierLebesgue L Weight.one p) :
    Distribution.ofCircleL1 (circleSynthesis (q := q) (PeriodicFourierLebesgue.unweightedCoefficients p u))
      ((Lp.memLp _).integrable (Fact.out : 1 ≤ q)) = u.val := by
  apply Distribution.ext_coefficients
  intro n
  rw [Distribution.ofCircleL1_coefficient,circleSynthesis_coefficient hp₂,
    PeriodicFourierLebesgue.unweightedCoefficients_apply]

end NLS.Fourier
