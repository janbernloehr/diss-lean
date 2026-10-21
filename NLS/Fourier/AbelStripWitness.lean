import NLS.Fourier.GeometricPeriodOne
import NLS.Fourier.SmoothPeriodicCoefficients
import NLS.SequenceSpaces.ExponentialSpectralWeights

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory
open scoped ContDiff ENNReal
namespace NLS.Fourier

/-- A period-one rational Fourier series with geometric ratio one third. -/
def section23StripWitness (z : ℂ) : ℂ :=
  (1-(1/3:ℂ)*Complex.exp (2*(Real.pi:ℂ)*I*z))⁻¹

/-- On the entire printed closed strip, the geometric denominator stays away from zero. -/
theorem section23StripWitness_ratio_bound (z : ℂ)
    (hz : |z.im| ≤ Real.log 2/(2*Real.pi)) :
    ‖(1/3:ℂ)*Complex.exp (2*(Real.pi:ℂ)*I*z)‖ ≤ 2/3 := by
  have hp : 0 < 2*Real.pi := by positivity
  have hh := (le_div_iff₀ hp).mp ((neg_le_abs z.im).trans hz)
  have he : -2*Real.pi*z.im ≤ Real.log 2 := by nlinarith
  have hr : (2*(Real.pi:ℂ)*I*z).re = -2*Real.pi*z.im := by
    simp [Complex.mul_re,Complex.mul_im]
  rw [norm_mul,Complex.norm_exp,hr]
  norm_num
  have hb := Real.exp_le_exp.mpr he
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hb
  simp only [neg_mul] at hb
  linarith

theorem section23StripWitness_denominator_ne_zero (z : ℂ)
    (hz : |z.im| ≤ Real.log 2/(2*Real.pi)) :
    1-(1/3:ℂ)*Complex.exp (2*(Real.pi:ℂ)*I*z) ≠ 0 := by
  intro h
  have he : (1/3:ℂ)*Complex.exp (2*(Real.pi:ℂ)*I*z) = 1 := (sub_eq_zero.mp h).symm
  have hb := section23StripWitness_ratio_bound z hz
  rw [he,norm_one] at hb
  norm_num at hb

/-- The witness is holomorphic on a neighborhood of every point of the printed closed strip. -/
theorem section23StripWitness_analytic_closed_strip :
    AnalyticOnNhd ℂ section23StripWitness {z | |z.im| ≤ Real.log 2/(2*Real.pi)} := by
  intro z hz
  unfold section23StripWitness
  exact AnalyticAt.inv (by fun_prop) (section23StripWitness_denominator_ne_zero z hz)

/-- Every horizontal trace in the printed strip is smooth, including both boundary lines. -/
theorem section23StripWitness_trace_smooth (y : ℝ) (hy : |y| ≤ Real.log 2/(2*Real.pi)) :
    ContDiff ℝ ∞ (fun x : ℝ => section23StripWitness (x+I*y)) := by
  unfold section23StripWitness
  have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  apply ContDiff.inv (by fun_prop)
  intro x
  apply section23StripWitness_denominator_ne_zero
  simpa using hy

/-- Each horizontal trace retains the original physical period one. -/
theorem section23StripWitness_trace_periodic (y : ℝ) :
    Function.Periodic (fun x : ℝ => section23StripWitness (x+I*y)) 1 := by
  intro x
  unfold section23StripWitness
  have he : 2*(Real.pi:ℂ)*I*((x+1:ℝ)+I*y) =
      2*(Real.pi:ℂ)*I*(x+I*y)+2*Real.pi*I := by push_cast; ring
  dsimp only
  rw [he,Complex.exp_periodic]

/-- At the real axis the actual Fourier coefficients have ratio one third. -/
theorem section23StripWitness_coefficient (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => section23StripWitness x) n =
      geometricPeriodOneCoefficients (1/3) n := by
  have he : (fun x : ℝ => section23StripWitness x) = (fun x => (1-(1/3:ℂ)*wave 2 x)⁻¹) := by
    funext x
    unfold section23StripWitness wave
    push_cast
    congr 3
    ring
  rw [he]
  exact periodOneCoefficient_geometric (1/3) (by norm_num) n


/-- Every trace in the printed closed strip belongs to the physical H0 coefficient space. -/
theorem section23StripWitness_trace_mem_two (y : ℝ) (hy : |y| ≤ Real.log 2/(2*Real.pi)) :
    Memℓp (periodOneCoefficient (fun x : ℝ => section23StripWitness (x+I*y))) 2 := by
  have h := memlp_periodOneCoefficient_sobolev_one 0 (by norm_num)
    (fun x : ℝ => section23StripWitness (x+I*y))
    (section23StripWitness_trace_smooth y hy) (section23StripWitness_trace_periodic y)
  simp only [Weight.sobolev_apply,Real.rpow_zero,Complex.ofReal_one,one_mul] at h
  exact h.of_exponent_ge (by norm_num : (1:ℝ≥0∞) ≤ 2)

/-- The source's Abel weight at a=log 2 and s=0. -/
def section23AbelWitnessWeight : SpectralWeight :=
  SpectralWeight.abel 0 (Real.log 2) (by norm_num) (Real.log_nonneg (by norm_num))

/-- Sampling at the original even physical index gives four to the nth power. -/
theorem section23AbelWitnessWeight_even_nat (n : ℕ) :
    section23AbelWitnessWeight (2*n) = (4:ℝ)^n := by
  simp only [section23AbelWitnessWeight,SpectralWeight.abel_apply,Real.rpow_zero,one_mul,
    Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),Nat.abs_cast]
  rw [show Real.log 2*(2*(n:ℝ)) = (n:ℝ)*(Real.log 2+Real.log 2) by ring,
    Real.exp_nat_mul,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  norm_num

/-- The weighted actual Fourier coefficients grow geometrically instead of being square summable. -/
theorem section23StripWitness_weighted_coefficient_norm (n : ℕ) :
    ‖(section23AbelWitnessWeight (2*n):ℂ)*
      periodOneCoefficient (fun x : ℝ => section23StripWitness x) n‖ = (4/3:ℝ)^n := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (section23AbelWitnessWeight.positive _),section23AbelWitnessWeight_even_nat,
    section23StripWitness_coefficient,geometricPeriodOneCoefficients_nat,norm_pow]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat]
  rw [← mul_pow]
  congr 1
  norm_num

/-- With the original even-index weight, the holomorphic strip witness is not in the Abel space. -/
theorem section23StripWitness_not_abel :
    ¬ Memℓp (fun n : ℤ => (section23AbelWitnessWeight (2*n):ℂ)*
      periodOneCoefficient (fun x : ℝ => section23StripWitness x) n) 2 := by
  intro h
  obtain ⟨C,hC⟩ := (h.of_exponent_ge (show (2:ℝ≥0∞) ≤ ⊤ from le_top)).bddAbove
  have ht := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 4/3)
  obtain ⟨n,hn⟩ := (ht.eventually (eventually_gt_atTop C)).exists
  have hb := hC (mem_range_self (n:ℤ))
  rw [section23StripWitness_weighted_coefficient_norm] at hb
  exact (not_le_of_gt hn) hb


/-- Both printed boundary traces are actual square-integrable functions on the unit interval. -/
theorem section23StripWitness_trace_memLp (y : ℝ) (hy : |y| ≤ Real.log 2/(2*Real.pi)) :
    MemLp (fun x : ℝ => section23StripWitness (x+I*y)) 2 (volume.restrict (Ioc 0 1)) := by
  have hc := (section23StripWitness_trace_smooth y hy).continuous
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn (s := Icc (0:ℝ) 1))
  apply MemLp.of_bound hc.aestronglyMeasurable R
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hR x ⟨hx.1.le,hx.2⟩

theorem section23AbelWitness_parameter_positive : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

/-- The printed half-width with H0 boundary traces does not characterize the
literal Abel space in the dissertation's original even-frequency convention. -/
theorem section23PrintedStrip_counterexample :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {z | |z.im| ≤ Real.log 2/(2*Real.pi)} ∧
      (∀ y : ℝ, |y| ≤ Real.log 2/(2*Real.pi) →
        Function.Periodic (fun x : ℝ => f (x+I*y)) 1 ∧
        ContDiff ℝ ∞ (fun x : ℝ => f (x+I*y)) ∧
        MemLp (fun x : ℝ => f (x+I*y)) 2 (volume.restrict (Ioc 0 1))) ∧
      ¬ Memℓp (fun n : ℤ => (section23AbelWitnessWeight (2*n):ℂ)*
        periodOneCoefficient (fun x : ℝ => f x) n) 2 := by
  exact ⟨section23StripWitness,section23StripWitness_analytic_closed_strip,
    fun y hy => ⟨section23StripWitness_trace_periodic y,
      section23StripWitness_trace_smooth y hy,section23StripWitness_trace_memLp y hy⟩,
    section23StripWitness_not_abel⟩

end NLS.Fourier
