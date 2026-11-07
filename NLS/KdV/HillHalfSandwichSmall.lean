import NLS.KdV.HillHalfSandwich
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform smallness of the ACTUAL normalized periodic perturbation, on
every original H^(-r) ball with 0<=r<1, including all source -1<t<-1/2. -/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The actual squared sandwich majorant tends to zero for every r<1. -/
theorem tendsto_hillHalfSandwich_majorant (r R : ℝ) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => (128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2))*R^2)
      atTop (𝓝 0) := by
  have ht := (isLittleO_log_rpow_atTop (show 0 < 2-2*r by linarith)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have he (n : ℕ) : Real.log (n:ℝ)/(n:ℝ)^(2-2*r) = Real.log (n:ℝ)*(n:ℝ)^(2*r-2) := by
    rw [div_eq_mul_inv,← Real.rpow_neg (Nat.cast_nonneg n),show -(2-2*r)=2*r-2 by ring]
  simp only [Function.comp_def,he] at ht
  have h := (ht.const_mul (128*(8*Real.exp 1+2))).mul_const (R^2)
  simpa only [mul_zero,zero_mul,mul_assoc] using h

/-- ONE threshold before ALL original H^(-r) potentials on a specified
norm ball and ALL source-circle parameters makes the ACTUAL normalized
physical perturbation at most ONE HALF in L2 operator norm. -/
theorem exists_uniform_hillPhysicalHalfSandwich_small (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 < Real.log (n:ℝ) ∧
      ∀ q : WeightedCoeff (Weight.sobolev (-r)) 2, ‖q‖ ≤ R →
        ∀ z ∈ sphere (freeHillValue n:ℂ) (n:ℝ), ‖hillPhysicalHalfSandwich r q z‖ ≤ 1/2 := by
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp
    ((tendsto_hillHalfSandwich_majorant r R hr1).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)))
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NL,hNL⟩ := eventually_atTop.mp (hl.eventually_gt_atTop (1:ℝ))
  refine ⟨max 2 (max N0 NL),by omega,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hlog := hNL n (by omega)
  refine ⟨hlog,?_⟩
  intro q hq z hz
  have hs := norm_sq_hillPhysicalHalfSandwich_le r hr hr1.le q n hn1 hlog z hz
  have hq2 := pow_le_pow_left₀ (norm_nonneg q) hq 2
  have hb := mul_le_mul_of_nonneg_left hq2
    (show 0 ≤ 128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2) by
      positivity [show 0 ≤ Real.log (n:ℝ) by linarith])
  have hsmall := hN0 n (by omega)
  have hp := hs.trans hb
  nlinarith [norm_nonneg (hillPhysicalHalfSandwich r q z)]

end NLS.KdV
