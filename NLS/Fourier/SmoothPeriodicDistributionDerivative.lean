import NLS.Fourier.PeriodicDistributionFourierGrowth
/-! # Differentiation of original periodic distributions

The original-dual derivative has the physical signed Fourier multiplier and
agrees with the derivative of the actual tempered realization. All period
and dilation factors are retained.
-/
noncomputable section
open Set Filter Topology
open scoped SchwartzMap BoundedContinuousFunction
namespace NLS.Fourier.SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

def derivLM : SmoothPeriodicTest L →ₗ[ℂ] SmoothPeriodicTest L where
  toFun f := ⟨iteratedDeriv 1 (f : ℝ → ℂ), f.smooth_deriv 1,
    DifferentialPolynomial.periodic_iteratedDeriv _ L f.periodic 1⟩
  map_add' f g := by
    ext x
    exact congrArg (fun h : ℝ →ᵇ ℂ => h x) (map_add (derivative (Fact.out : 0 < L).ne' 1) f g)
  map_smul' c f := by
    ext x
    exact congrArg (fun h : ℝ →ᵇ ℂ => h x) (map_smul (derivative (Fact.out : 0 < L).ne' 1) c f)

theorem derivLM_apply (f : SmoothPeriodicTest L) (x : ℝ) : derivLM f x = deriv (f : ℝ → ℂ) x := by
  change iteratedDeriv 1 _ x = _
  rw [iteratedDeriv_one]

theorem derivative_derivLM (k : ℕ) (f : SmoothPeriodicTest L) :
    derivative (Fact.out : 0 < L).ne' k (derivLM f) = derivative (Fact.out : 0 < L).ne' (k+1) f := by
  ext x
  change iteratedDeriv k (iteratedDeriv 1 (f : ℝ → ℂ)) x = _
  rw [iteratedDeriv_one,← iteratedDeriv_succ']
  rfl

theorem cNorm_derivLM_le (N : ℕ) (f : SmoothPeriodicTest L) :
    cNorm (Fact.out : 0 < L).ne' N (derivLM f) ≤ (N+1)*cNorm (Fact.out : 0 < L).ne' (N+1) f := by
  rw [cNorm_apply]
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1), cNorm (Fact.out : 0 < L).ne' (N+1) f := by
      apply Finset.sum_le_sum
      intro j hj
      rw [derivative_derivLM]
      exact derivative_norm_le_cNorm _ f (by have hj' := Finset.mem_range.mp hj; omega)
    _ = _ := by simp

def derivCLM : SmoothPeriodicTest L →L[ℂ] SmoothPeriodicTest L where
  toLinearMap := derivLM
  cont := by
    apply withSeminorms.continuous_of_isBounded withSeminorms
    intro N
    refine ⟨{N+1},⟨(N:ℝ)+1,by positivity⟩,?_⟩
    simp only [Finset.sup_singleton]
    change ∀ f, cNorm (Fact.out : 0 < L).ne' N (derivLM f) ≤ (N+1)*cNorm (Fact.out : 0 < L).ne' (N+1) f
    exact cNorm_derivLM_le N

/-- The derivative of a physical Fourier mode has exactly the source multiplier. -/
theorem derivCLM_mode (n : ℤ) : derivCLM (mode n : SmoothPeriodicTest L) =
    (Complex.I*(2*(n:ℂ)*(Real.pi:ℂ)/(L:ℂ))) • mode n := by
  ext x
  change derivLM (mode n : SmoothPeriodicTest L) x = _
  rw [derivLM_apply]
  change deriv (fun x => wave n ((L/2)⁻¹*x)) x = (Complex.I*(2*(n:ℂ)*(Real.pi:ℂ)/(L:ℂ)))*wave n ((L/2)⁻¹*x)
  have h := (hasDerivAt_wave n ((L/2)⁻¹*x)).scomp x ((hasDerivAt_id x).const_mul (L/2)⁻¹)
  calc
    _ = ((L/2)⁻¹*1) • (Complex.I*(Real.pi:ℂ)*n*wave n ((L/2)⁻¹*x)) := h.deriv
    _ = _ := by
      simp only [mul_one,Complex.real_smul]
      push_cast
      field_simp

theorem derivCLM_ofPeriodization (g : 𝓢(ℝ,ℂ)) :
    derivCLM (ofPeriodization g : SmoothPeriodicTest L) =
      (((L/2)⁻¹:ℝ):ℂ) • ofPeriodization (SchwartzMap.derivCLM ℂ ℂ g) := by
  ext x
  change SmoothPeriodicTest.derivative (Fact.out : 0 < L).ne' 1 (ofPeriodization g : SmoothPeriodicTest L) x = _
  rw [derivative_ofPeriodization]
  simp only [pow_one,periodizationDerivCLM_succ,periodizationDerivCLM_zero,Complex.real_smul]
  rfl

namespace Distribution
/-- The distributional derivative acts by minus the physical test derivative. -/
def derivative (u : Distribution L) : Distribution L := -u.comp derivCLM

theorem derivative_apply (u : Distribution L) (f : SmoothPeriodicTest L) :
    u.derivative f = -u (derivCLM f) := rfl

/-- The exact signed Fourier multiplier in Appendix A. -/
theorem derivative_coefficient (u : Distribution L) (n : ℤ) :
    u.derivative (mode (-n)) = (Complex.I*(2*(n:ℂ)*(Real.pi:ℂ)/(L:ℂ)))*u (mode (-n)) := by
  rw [derivative_apply,derivCLM_mode,map_smul]
  simp only [smul_eq_mul,Int.cast_neg]
  ring

theorem derivative_hasOrderAtMost {u : Distribution L} {N : ℕ} (h : u.HasOrderAtMost N) :
    u.derivative.HasOrderAtMost (N+1) := by
  obtain ⟨C,hC,hb⟩ := h
  refine ⟨C*(N+1),by positivity,fun f => ?_⟩
  rw [derivative_apply,norm_neg]
  change ‖u (derivLM f)‖ ≤ C*(N+1)*cNorm (Fact.out : 0 < L).ne' (N+1) f
  exact (hb (derivLM f)).trans (by
    have h := mul_le_mul_of_nonneg_left (cNorm_derivLM_le N f) hC.le
    simpa only [mul_assoc] using h)

theorem derivative_order_le (u : Distribution L) : u.derivative.order ≤ u.order+1 :=
  order_le (derivative_hasOrderAtMost u.hasOrderAtMost_order)
theorem toTemperedTwo_derivative (u : Distribution L) :
    u.derivative.toTemperedTwo = (((L/2)⁻¹:ℝ):ℂ) • TemperedDistribution.derivCLM ℂ u.toTemperedTwo := by
  ext g
  rw [_root_.smul_apply,TemperedDistribution.derivCLM_apply_apply,map_neg]
  change 2*(-u (derivCLM (ofPeriodization g))) = (((L/2)⁻¹:ℝ):ℂ)*(-(2*u (ofPeriodization (SchwartzMap.derivCLM ℂ ℂ g))))
  rw [derivCLM_ofPeriodization,map_smul]
  simp only [smul_eq_mul]
  ring
end Distribution
end NLS.Fourier.SmoothPeriodicTest

namespace NLS.Fourier

theorem schwartz_deriv_dilation (c : ℝ) (hc : c ≠ 0) (g : 𝓢(ℝ,ℂ)) :
    SchwartzMap.derivCLM ℂ ℂ (schwartzDilationCLM c hc g) =
      (c:ℂ) • schwartzDilationCLM c hc (SchwartzMap.derivCLM ℂ ℂ g) := by
  ext x
  change deriv (fun x => g (c*x)) x = (c:ℂ)*deriv (g : ℝ → ℂ) (c*x)
  have h := (g.differentiable (c*x)).hasDerivAt.scomp x ((hasDerivAt_id x).const_mul c)
  calc
    _ = (c*1) • deriv (g : ℝ → ℂ) (c*x) := h.deriv
    _ = _ := by simp [Complex.real_smul]

theorem distributionDilation_deriv (c : ℝ) (hc : c ≠ 0) (T : 𝓢'(ℝ,ℂ)) :
    TemperedDistribution.derivCLM ℂ (distributionDilation c hc T) =
      (c:ℂ) • distributionDilation c hc (TemperedDistribution.derivCLM ℂ T) := by
  ext g
  simp only [_root_.smul_apply,smul_eq_mul,TemperedDistribution.derivCLM_apply_apply,distributionDilation_apply,
    map_neg,schwartz_deriv_dilation,map_smul,Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hc]

namespace SmoothPeriodicTest.Distribution
variable {L : ℝ} [Fact (0 < L)]
theorem toTempered_derivative (u : Distribution L) :
    u.derivative.toTempered = TemperedDistribution.derivCLM ℂ u.toTempered := by
  have hL : 0 < L := Fact.out
  rw [toTempered,toTempered,toTemperedTwo_derivative,distributionDilation_deriv]
  change distributionDilationCLM (L/2)⁻¹ (inv_ne_zero (by positivity : L/2 ≠ 0)) ((((L/2)⁻¹:ℝ):ℂ) • TemperedDistribution.derivCLM ℂ u.toTemperedTwo) = _
  rw [map_smul]
  rfl
end SmoothPeriodicTest.Distribution
end NLS.Fourier
