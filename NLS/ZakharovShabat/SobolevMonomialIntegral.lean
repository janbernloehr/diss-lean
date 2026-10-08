import NLS.ZakharovShabat.SobolevJetInterpolation
import NLS.ZakharovShabat.SobolevOddRemainderBounds
import NLS.DifferentialPolynomial.TwoFactorSplit

/-! # Two physical L² factors in each remainder monomial -/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MeasureTheory Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The first lower jet is the actual derivative representative. -/
theorem lowerSobolevJet_first_apply (m k : ℕ) (hk : k < m) (a : SobolevSource m) (x : ℝ) :
    lowerSobolevJet m (false,k) a (x : AddCircle (2:ℝ)) =
      hierarchySobolevJetContinuous m k hk a.1 (x : AddCircle (2:ℝ)) := by
  simp only [lowerSobolevJet,hk,↓reduceDIte,Bool.false_eq_true,↓reduceIte,ContinuousLinearMap.comp_apply]
  rfl

/-- Cauchy–Schwarz for the actual physical norms, with unit-interval Parseval. -/
theorem integral_lowerSobolevJet_norm_mul_le (m i j : ℕ) (hi : i < m) (hj : j < m)
    (a : SobolevSource m) :
    (∫ x in (0:ℝ)..1, ‖lowerSobolevJet m (false,i) a (x : AddCircle (2:ℝ))‖*
      ‖lowerSobolevJet m (false,j) a (x : AddCircle (2:ℝ))‖) ≤
      ‖hierarchySobolevJetL2 m i hi.le a.1‖*‖hierarchySobolevJetL2 m j hj.le a.1‖ := by
  let f := fun x : ℝ => hierarchySobolevJetContinuous m i hi a.1 (x : AddCircle (2:ℝ))
  let g := fun x : ℝ => hierarchySobolevJetContinuous m j hj a.1 (x : AddCircle (2:ℝ))
  have hf : Continuous f := (hierarchySobolevJetContinuous m i hi a.1).continuous.comp continuous_quotient_mk'
  have hg : Continuous g := (hierarchySobolevJetContinuous m j hj a.1).continuous.comp continuous_quotient_mk'
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc (0:ℝ) 1))
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (Filter.Eventually.of_forall (fun x => norm_nonneg (g x)))
    (by simpa using (memLp_two_interval hf 0 1 (by norm_num)).norm)
    (by simpa using (memLp_two_interval hg 0 1 (by norm_num)).norm)
  have hf2 : (∫ x in (0:ℝ)..1, ‖f x‖^2) = ‖hierarchySobolevJetL2 m i hi.le a.1‖^2 :=
    integral_norm_sq_hierarchySobolevJetContinuous m i hi a.1
  have hg2 : (∫ x in (0:ℝ)..1, ‖g x‖^2) = ‖hierarchySobolevJetL2 m j hj.le a.1‖^2 :=
    integral_norm_sq_hierarchySobolevJetContinuous m j hj a.1
  simp only [Real.rpow_two,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    hf2,hg2,← Real.sqrt_eq_rpow,Real.sqrt_sq (norm_nonneg _)] at h
  simpa only [lowerSobolevJet_first_apply m i hi,lowerSobolevJet_first_apply m j hj,f,g] using h

/-- Extract two L² factors and bound all other factors by their continuous norms. -/
theorem integral_sobolevRealMonomial_le_split (m : ℕ) (d : Monomial)
    (i j : ℕ) (hi : i < m) (hj : j < m) (ν : ℕ → ℕ)
    (hμ : ∀ k ∈ Finset.range m, jetMultiplicity d k =
      ν k+(if k=i then 1 else 0)+(if k=j then 1 else 0)) (a : SobolevSource m) :
    (∫ x in (0:ℝ)..1, sobolevRealMonomial m d a x) ≤
      (∏ k ∈ Finset.range m, ‖lowerSobolevJet m (false,k) a‖^ν k)*
      ‖hierarchySobolevJetL2 m i hi.le a.1‖*‖hierarchySobolevJetL2 m j hj.le a.1‖ := by
  let K := ∏ k ∈ Finset.range m, ‖lowerSobolevJet m (false,k) a‖^ν k
  have hK : 0 ≤ K := Finset.prod_nonneg (fun k _ => pow_nonneg (norm_nonneg _) _)
  let F := fun k (x : ℝ) => ‖lowerSobolevJet m (false,k) a (x : AddCircle (2:ℝ))‖
  have hF (k : ℕ) : Continuous (F k) := by dsimp [F]; fun_prop
  have hp (x : ℝ) : sobolevRealMonomial m d a x ≤ K*(F i x*F j x) := by
    rw [sobolevRealMonomial,prod_pow_two_factor_split (Finset.range m) (jetMultiplicity d) ν i j
      (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hμ]
    change (∏ k ∈ Finset.range m, F k x^ν k)*F i x*F j x ≤ _
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply Finset.prod_le_prod (fun k _ => pow_nonneg (norm_nonneg _) _)
    intro k _
    exact pow_le_pow_left₀ (norm_nonneg _) ((lowerSobolevJet m (false,k) a).norm_coe_le_norm _) _
  calc
    _ ≤ ∫ x in (0:ℝ)..1, K*(F i x*F j x) := intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_sobolevRealMonomial m d a).intervalIntegrable 0 1)
      ((continuous_const.mul ((hF i).mul (hF j))).intervalIntegrable 0 1) (fun x _ => hp x)
    _ = K*(∫ x in (0:ℝ)..1, F i x*F j x) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (integral_lowerSobolevJet_norm_mul_le m i j hi hj a) hK

end NLS.ZakharovShabat
