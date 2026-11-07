import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.FiniteExponentTail

/-! A literal weighted squared-gap majorant controls the sharp
frequency weight. Its positive coordinates give a vanishing tail. -/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem sobolev_gap_remainder_bound
    (t : ℝ) (n : ℤ) (γ e : ℂ) (M : ℝ)
    (he : Weight.sobolev (t-1) n*‖e‖≤‖γ‖^2*M) :
    Weight.sobolev (3*t-1) n*‖e‖≤M*(Weight.sobolev (2*t) n*‖γ‖^2) := by
  have h := mul_le_mul_of_nonneg_left he ((Weight.sobolev (2*t)).positive n).le
  have hw : Weight.sobolev (3*t-1) n=Weight.sobolev (2*t) n*Weight.sobolev (t-1) n := by
    rw [show 3*t-1=2*t+(t-1) by ring,Weight.sobolev_add]
  rw [hw]
  calc
    _=Weight.sobolev (2*t) n*(Weight.sobolev (t-1) n*‖e‖) := by ring
    _≤Weight.sobolev (2*t) n*(‖γ‖^2*M) := h
    _=M*(Weight.sobolev (2*t) n*‖γ‖^2) := by ring

theorem tendsto_norm_positive_apply (g : Coeff 1) :
    Tendsto (fun n : ℕ => ‖g ((n+1 : ℕ):ℤ)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_natAbs_norm_lt (by norm_num : 0<(1 : ℝ≥0∞).toReal) g hε
  refine ⟨N,fun n hn => ?_⟩
  have h := hN ((n+1 : ℕ):ℤ) (by simpa only [Int.natAbs_natCast] using Nat.le_succ_of_le hn)
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using h

theorem tendsto_positive_weighted_remainder_of_majorant
    (w : ℤ → ℝ) (hw : ∀ n, 0≤w n) (f : ℕ+ → ℂ) (g : Coeff 1)
    (M : ℝ) (K : ℕ)
    (hb : ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖f n‖≤M*‖g (n:ℤ)‖) :
    Tendsto (fun n : ℕ => w ((n+1 : ℕ):ℤ)*‖f ⟨n+1,by omega⟩‖) atTop (𝓝 0) := by
  have ht := (tendsto_norm_positive_apply g).const_mul M
  rw [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => mul_nonneg (hw _) (norm_nonneg _))) ?_ ht
  filter_upwards [eventually_ge_atTop K] with n hn
  exact hb ⟨n+1,by omega⟩ (by change K≤n+1;omega)

theorem tendsto_positive_weighted_of_eq
    (w : ℤ → ℝ) (f g : ℕ+ → ℂ) (hfg : ∀ n, f n=g n)
    (hf : Tendsto (fun n : ℕ => w ((n+1:ℕ):ℤ)*‖f ⟨n+1,by omega⟩‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => w ((n+1:ℕ):ℤ)*‖g ⟨n+1,by omega⟩‖) atTop (𝓝 0) := by
  apply hf.congr'
  exact Filter.Eventually.of_forall (fun n =>
    congrArg (fun z : ℂ => w ((n+1:ℕ):ℤ)*‖z‖) (hfg ⟨n+1,by omega⟩))

end NLS.Coeff
