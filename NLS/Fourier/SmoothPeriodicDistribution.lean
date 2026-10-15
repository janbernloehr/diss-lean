import NLS.Fourier.ArbitraryPeriodDistributionPairing
import NLS.Fourier.SmoothPeriodicTestSpace

/-! # Original periodic distributions and actual tempered distributions

The original smooth-test dual is equivalent to actual periodic tempered
distributions at every positive physical period. Both directions preserve
normalized Fourier coefficients and the action on every smooth test.
-/
noncomputable section
open Set Filter Topology
open scoped SchwartzMap ContDiff BoundedContinuousFunction
namespace NLS.Fourier
namespace SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

def ofPeriodization (g : 𝓢(ℝ,ℂ)) : SmoothPeriodicTest L :=
  ⟨fun x => periodizationCLM g (((L/2)⁻¹*x : ℝ) : AddCircle (2:ℝ)),
    (contDiff_periodization g).comp (by fun_prop),by
      intro x
      have hL : 0 < L := Fact.out
      dsimp only
      rw [show (L/2)⁻¹*(x+L) = (L/2)⁻¹*x+2 by field_simp]
      simp⟩

def periodizationLM : 𝓢(ℝ,ℂ) →ₗ[ℂ] SmoothPeriodicTest L where
  toFun := ofPeriodization
  map_add' f g := by ext x; exact congrArg (fun h : C(AddCircle (2:ℝ),ℂ) => h _) (map_add periodizationCLM f g)
  map_smul' c f := by ext x; exact congrArg (fun h : C(AddCircle (2:ℝ),ℂ) => h _) (map_smul periodizationCLM c f)

theorem derivative_ofPeriodization (g : 𝓢(ℝ,ℂ)) (k : ℕ) (x : ℝ) :
    derivative (Fact.out : 0 < L).ne' k (ofPeriodization g : SmoothPeriodicTest L) x =
      ((L/2)⁻¹)^k • periodizationDerivCLM k g (((L/2)⁻¹*x : ℝ) : AddCircle (2:ℝ)) := by
  change iteratedDeriv k (fun x => periodizationCLM g (((L/2)⁻¹*x : ℝ) : AddCircle (2:ℝ))) x = _
  rw [iteratedDeriv_comp_const_smul (contDiff_infty.mp (contDiff_periodization g) k),iteratedDeriv_periodization]

theorem norm_derivative_ofPeriodization (g : 𝓢(ℝ,ℂ)) (k : ℕ) :
    ‖derivative (Fact.out : 0 < L).ne' k (ofPeriodization g : SmoothPeriodicTest L)‖ =
      |(L/2)⁻¹|^k*‖periodizationDerivCLM k g‖ := by
  have hL : 0 < L := Fact.out
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    rw [derivative_ofPeriodization,norm_smul,norm_pow,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) (by positivity)
  · have he : |(L/2)⁻¹|^k*‖periodizationDerivCLM k g‖ = ‖(((L/2)⁻¹)^k : ℝ) • periodizationDerivCLM k g‖ := by
      rw [norm_smul,norm_pow,Real.norm_eq_abs]
    rw [he]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro y
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
    have h := BoundedContinuousFunction.norm_coe_le_norm (derivative (Fact.out : 0 < L).ne' k (ofPeriodization g : SmoothPeriodicTest L)) ((L/2)*x)
    rw [derivative_ofPeriodization,inv_mul_cancel_left₀ (by positivity : L/2 ≠ 0)] at h
    exact h

def periodizationCLM : 𝓢(ℝ,ℂ) →L[ℂ] SmoothPeriodicTest L where
  toLinearMap := periodizationLM
  cont := by
    apply withSeminorms.continuous_of_continuous_comp
    intro N
    change Continuous (fun g : 𝓢(ℝ,ℂ) => cNorm (Fact.out : 0 < L).ne' N (ofPeriodization g : SmoothPeriodicTest L))
    simp only [cNorm_apply,norm_derivative_ofPeriodization]
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul (NLS.Fourier.periodizationDerivCLM j).continuous.norm)

/-- The actual physical exponential exp(i 2 pi n x/L). -/
def mode (n : ℤ) : SmoothPeriodicTest L :=
  ⟨fun x => wave n ((L/2)⁻¹*x),
    (contDiff_wave_infty n).comp (by fun_prop),by
      intro x
      have hL : 0 < L := Fact.out
      dsimp only
      rw [show (L/2)⁻¹*(x+L) = (L/2)⁻¹*x+2 by field_simp]
      rw [← fourier_two_eq_wave,← fourier_two_eq_wave]
      simp⟩

theorem ofPeriodization_coefficientTest (n : ℤ) :
    (ofPeriodization (coefficientTest n) : SmoothPeriodicTest L) = (1/2:ℂ) • mode (-n) := by
  ext x
  change NLS.Fourier.periodizationCLM (coefficientTest n) _ = (1/2:ℂ)*wave (-n) _
  rw [periodization_coefficientTest]
  simp only [ContinuousMap.smul_apply,smul_eq_mul,fourier_two_eq_wave]

/-- An original periodic distribution, with its original smooth-test topology. -/
abbrev Distribution (L : ℝ) [Fact (0 < L)] := SmoothPeriodicTest L →L[ℂ] ℂ

/-- Transfer to actual tempered distributions after rescaling the period to two. -/
def Distribution.toTemperedTwo (u : Distribution L) : 𝓢'(ℝ,ℂ) := (2:ℂ) • u.comp periodizationCLM

theorem Distribution.toTemperedTwo_periodic (u : Distribution L) : IsPeriodTwoDistribution u.toTemperedTwo := by
  intro g
  change 2*u (ofPeriodization (SchwartzMap.compSubConstCLM ℂ 2 g)) = 2*u (ofPeriodization g)
  congr 2
  apply ext
  intro x
  exact congrArg (fun h : C(AddCircle (2:ℝ),ℂ) => h _) (periodization_translate_two g)

theorem Distribution.toTemperedTwo_coefficient (u : Distribution L) (n : ℤ) :
    u.toTemperedTwo (coefficientTest n) = u (mode (-n)) := by
  change 2*u (ofPeriodization (coefficientTest n)) = _
  rw [ofPeriodization_coefficientTest,map_smul]
  simp only [smul_eq_mul]
  ring

/-- Rescaling any original test to period two, then lifting and periodizing, recovers it exactly. -/
theorem ofPeriodization_lift (f : SmoothPeriodicTest L) :
    (ofPeriodization (smoothPeriodicTestLift (fun x => f ((L/2)*x))) : SmoothPeriodicTest L) = f := by
  have hL : 0 < L := Fact.out
  ext x
  change NLS.Fourier.periodizationCLM (smoothPeriodicTestLift _) _ = _
  have he := periodization_smoothPeriodicTestLift (fun y : ℝ => f ((L/2)*y))
    (f.smooth.comp (by fun_prop)) (periodic_periodTwoDilation L _ f.periodic) ((L/2)⁻¹*x)
  simpa only [mul_inv_cancel_left₀ (by positivity : L/2 ≠ 0)] using he

theorem Distribution.toTemperedTwo_injective : Function.Injective (Distribution.toTemperedTwo (L := L)) := by
  intro u v h
  apply ContinuousLinearMap.ext
  intro f
  have he := congrArg (fun T : 𝓢'(ℝ,ℂ) => T (smoothPeriodicTestLift (fun x => f ((L/2)*x)))) h
  change 2*u (ofPeriodization _) = 2*v (ofPeriodization _) at he
  rw [ofPeriodization_lift] at he
  exact mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0) he

/-- Uniqueness is on all original smooth periodic tests. -/
theorem Distribution.ext_coefficients {u v : Distribution L}
    (h : ∀ n : ℤ, u (mode (-n)) = v (mode (-n))) : u = v := by
  apply Distribution.toTemperedTwo_injective
  apply periodicDistribution_ext u.toTemperedTwo_periodic v.toTemperedTwo_periodic
  intro n
  rw [u.toTemperedTwo_coefficient,v.toTemperedTwo_coefficient,h n]

/-- Actual periodic tempered distributions act continuously on every original smooth test. -/
def Distribution.ofTempered (T : 𝓢'(ℝ,ℂ)) : Distribution L :=
  T.comp (windowCLM (periodCoefficientTest L Fact.out 0))

theorem Distribution.ofTempered_coefficient (T : 𝓢'(ℝ,ℂ)) (hT : IsPeriodicDistribution L T) (n : ℤ) :
    (Distribution.ofTempered T : Distribution L) (mode (-n)) = T (periodCoefficientTest L Fact.out n) := by
  have hL : 0 < L := Fact.out
  change T (SchwartzMap.smulLeftCLM ℂ (mode (-n) : SmoothPeriodicTest L) (periodCoefficientTest L hL 0)) = _
  rw [← distributionDilation_window_action L hL T _ (mode (-n)).smooth (mode (-n)).periodic]
  have he : (fun x => (mode (-n) : SmoothPeriodicTest L) ((L/2)*x)) = wave (-n) := by
    funext x
    change wave (-n) ((L/2)⁻¹*((L/2)*x)) = _
    rw [inv_mul_cancel_left₀ (by positivity : L/2 ≠ 0)]
  rw [he,(isPeriodTwoDistribution_dilation L hL T hT).wave_window,neg_neg,distributionDilation_periodCoefficientTest]


namespace Distribution
/-- An original smooth-test functional as an actual distribution of the same physical period. -/
def toTempered (u : Distribution L) : 𝓢'(ℝ,ℂ) :=
  distributionDilation (L/2)⁻¹ (inv_ne_zero (by have hL : 0 < L := Fact.out; positivity)) u.toTemperedTwo

theorem toTempered_periodic (u : Distribution L) : IsPeriodicDistribution L u.toTempered := by
  have hL : 0 < L := Fact.out
  have h := distributionDilation_periodic (L/2)⁻¹ (inv_ne_zero (by positivity)) 2 u.toTemperedTwo u.toTemperedTwo_periodic
  have he : 2/(L/2)⁻¹ = L := by field_simp
  rw [he] at h
  exact h

theorem toTempered_coefficient (u : Distribution L) (n : ℤ) :
    u.toTempered (periodCoefficientTest L Fact.out n) = u (mode (-n)) := by
  rw [← distributionDilation_periodCoefficientTest]
  change distributionDilation (L/2) (by have hL : 0 < L := Fact.out; positivity)
    (distributionDilation (L/2)⁻¹ _ u.toTemperedTwo) (coefficientTest n) = _
  rw [distributionDilation_inverse_right,u.toTemperedTwo_coefficient]

theorem ofTempered_toTempered (u : Distribution L) : ofTempered u.toTempered = u := by
  apply ext_coefficients
  intro n
  rw [ofTempered_coefficient _ u.toTempered_periodic,u.toTempered_coefficient]

theorem toTempered_ofTempered (T : 𝓢'(ℝ,ℂ)) (hT : IsPeriodicDistribution L T) :
    (ofTempered T : Distribution L).toTempered = T := by
  apply periodicDistribution_ext_arbitraryPeriod L Fact.out (ofTempered T).toTempered_periodic hT
  intro n
  rw [toTempered_coefficient,ofTempered_coefficient T hT]

/-- The original smooth-test dual is equivalent to actual periodic tempered distributions. -/
def periodicTemperedEquiv : Distribution L ≃ {T : 𝓢'(ℝ,ℂ) // IsPeriodicDistribution L T} where
  toFun u := ⟨u.toTempered,u.toTempered_periodic⟩
  invFun T := ofTempered T.val
  left_inv := ofTempered_toTempered
  right_inv T := Subtype.ext (toTempered_ofTempered T.val T.property)
end Distribution

end SmoothPeriodicTest
end NLS.Fourier
