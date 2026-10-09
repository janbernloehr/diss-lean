import NLS.Fourier.UnitIntervalC1FourierLebesgue
import NLS.SequenceSpaces.Translation
import NLS.ComplexAnalysis.ScalarDuhamel

/-! # Uniform Fourier bounds for exponentials near the pi lattice

Integer Fourier modulation preserves the sequence norm. Removing n/2
leaves a bounded residual frequency, including for negative odd indices.
All coefficients are the actual integrals on [0,1]; matching endpoint
values and periodicity of the unextended exponential are not assumed.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Fourier

/-- The exponential appearing in Lemma E.3, before its periodic interval interpretation. -/
def unitIntervalExponential (z : ℂ) (x : ℝ) : ℂ := exp (Complex.I*z*x)

@[fun_prop] theorem contDiff_unitIntervalExponential (z : ℂ) : ContDiff ℝ 1 (unitIntervalExponential z) := by
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem deriv_unitIntervalExponential (z : ℂ) (x : ℝ) :
    deriv (unitIntervalExponential z) x = unitIntervalExponential z x*(Complex.I*z) :=
  (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (Complex.I*z) x).deriv

/-- A bounded frequency gives uniform C1 bounds on the whole unit interval. -/
theorem unitIntervalExponential_bounds (z : ℂ) {B : ℝ} (hB : 0 ≤ B) (hz : ‖z‖ ≤ B)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    ‖unitIntervalExponential z x‖ ≤ Real.exp B ∧
      ‖deriv (unitIntervalExponential z) x‖ ≤ B*Real.exp B := by
  have hb : ‖Complex.I*z*(x:ℂ)‖ ≤ B := by
    rw [norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_of_nonneg hx.1]
    exact (mul_le_mul_of_nonneg_right hz hx.1).trans (mul_le_of_le_one_right hB hx.2)
  have he : ‖unitIntervalExponential z x‖ ≤ Real.exp B :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hb)
  refine ⟨he,?_⟩
  rw [deriv_unitIntervalExponential,norm_mul,norm_mul,norm_I,one_mul]
  exact (mul_le_mul he hz (norm_nonneg _) (Real.exp_pos B).le).trans_eq (mul_comm _ _)

/-- Free pi-lattice frequencies recover the exact period-one overlap integral. -/
theorem intervalFourierCoefficient_exponential_lattice (n m : ℤ) :
    intervalFourierCoefficient 1 (unitIntervalExponential ((Real.pi:ℂ)*n)) m =
      unitIntegral (n-2*m) := by
  simp only [intervalFourierCoefficient,div_one,Complex.ofReal_one,one_mul,unitIntegral]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  unfold unitIntervalExponential wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The original unit-interval Fourier integrals of exp(i*z*x), at any q>1. -/
def exponentialFourierCoefficients (hq : 1 < q) (z : ℂ) : Coeff q :=
  unitIntervalC1Coefficients hq (unitIntervalExponential z) (contDiff_unitIntervalExponential z)

omit [Fact (1 ≤ q)] in
@[simp] theorem exponentialFourierCoefficients_apply (hq : 1 < q) (z : ℂ) (m : ℤ) :
    exponentialFourierCoefficients hq z m = intervalFourierCoefficient 1 (unitIntervalExponential z) m := rfl

/-- The actual Fourier-Lebesgue norm is uniformly bounded on every frequency norm ball. -/
theorem norm_exponentialFourierCoefficients_le (hq : 1 < q) (z : ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hz : ‖z‖ ≤ B) :
    ‖exponentialFourierCoefficients hq z‖ ≤ (2+B)*Real.exp B*unitIntervalC1FourierConstant hq := by
  apply (norm_unitIntervalC1Coefficients_le hq _ (contDiff_unitIntervalExponential z)
    (Real.exp B) (B*Real.exp B) (Real.exp_pos B).le (by positivity)
    (fun x hx => (unitIntervalExponential_bounds z hB hz x hx).1)
    (fun x hx => (unitIntervalExponential_bounds z hB hz x hx).2)).trans_eq
  ring

/-- An integer modulation shifts the literal physical Fourier integral by exactly that integer. -/
theorem intervalFourierCoefficient_exponential_modulation (z : ℂ) (k m : ℤ) :
    intervalFourierCoefficient 1 (unitIntervalExponential (z+2*(Real.pi:ℂ)*k)) m =
      intervalFourierCoefficient 1 (unitIntervalExponential z) (m-k) := by
  simp only [intervalFourierCoefficient,div_one,Complex.ofReal_one,one_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  unfold unitIntervalExponential wave
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Modulation is the previously constructed coefficient-shift isometry. -/
theorem exponentialFourierCoefficients_modulation (hq : 1 < q) (z : ℂ) (k : ℤ) :
    exponentialFourierCoefficients hq (z+2*(Real.pi:ℂ)*k) =
      Coeff.shift k (exponentialFourierCoefficients hq z) := by
  ext m
  exact intervalFourierCoefficient_exponential_modulation z k m

/-- Integer modulation does not change the norm, including q=infinity. -/
theorem norm_exponentialFourierCoefficients_modulation (hq : 1 < q) (z : ℂ) (k : ℤ) :
    ‖exponentialFourierCoefficients hq (z+2*(Real.pi:ℂ)*k)‖ =
      ‖exponentialFourierCoefficients hq z‖ := by
  rw [exponentialFourierCoefficients_modulation,Coeff.norm_shift]

/-- Removing the even part of n leaves a uniformly bounded complex frequency.
Euclidean integer division handles negative odd n without a sign exception. -/
theorem norm_exponential_residual_frequency_le (n : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    ‖z-2*(Real.pi:ℂ)*(n/2:ℤ)‖ ≤ 5*Real.pi/4 := by
  have hr : n%2 = 0 ∨ n%2 = 1 := by omega
  have hn : ‖((n%2:ℤ):ℂ)‖ ≤ 1 := by rcases hr with h | h <;> simp [h]
  have hnorm : ‖(Real.pi:ℂ)*((n%2:ℤ):ℂ)‖ ≤ Real.pi := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact mul_le_of_le_one_right Real.pi_pos.le hn
  have hid : n = 2*(n/2)+n%2 := by omega
  have he : z-2*(Real.pi:ℂ)*(n/2:ℤ) =
      (z-(Real.pi:ℂ)*n)+(Real.pi:ℂ)*((n%2:ℤ):ℂ) := by
    have hc : (n:ℂ) = 2*(n/2:ℤ)+(n%2:ℤ) := by exact_mod_cast hid
    rw [hc]
    ring
  rw [he]
  have hb := (norm_add_le (z-(Real.pi:ℂ)*n) ((Real.pi:ℂ)*((n%2:ℤ):ℂ))).trans (add_le_add hz hnorm)
  linarith

/-- Uniform Fourier-Lebesgue control near every pi-lattice point, including negative odd indices. -/
theorem norm_exponentialFourierCoefficients_near_lattice (hq : 1 < q) (n : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    ‖exponentialFourierCoefficients hq z‖ ≤
      (2+5*Real.pi/4)*Real.exp (5*Real.pi/4)*unitIntervalC1FourierConstant hq := by
  have he := norm_exponentialFourierCoefficients_modulation hq
    (z-2*(Real.pi:ℂ)*(n/2:ℤ)) (n/2)
  rw [sub_add_cancel] at he
  rw [he]
  exact norm_exponentialFourierCoefficients_le hq _ (by positivity)
    (norm_exponential_residual_frequency_le n z hz)

end NLS.Fourier
