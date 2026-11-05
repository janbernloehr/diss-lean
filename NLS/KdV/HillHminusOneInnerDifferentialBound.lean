import NLS.KdV.HillHminusOneInnerRootBound
import NLS.KdV.HillHminusOneCriticalPoints
import NLS.ComplexAnalysis.DiscBounds
/-! # Uniform decay of the actual trace differential on inner contours

Cauchy estimates on the outer discs and actual root separation give a C/k
bound on one complex rough-source ball before all positive contour indices.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminus_frequency_derivative_eq (q : PeriodOneHminusOne) (z : ℂ) :
    deriv (fun w : ℂ => hillHminusDiscriminant q (w^2)) z =
      (2*z)*hillHminusDiscriminantDerivative (z^2,q) := by
  have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hD : AnalyticAt ℂ (hillHminusDiscriminant q) (z^2) :=
    (analyticOnNhd_hillHminusDiscriminant_joint _ (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hd := hD.differentiableAt.hasDerivAt.comp z hsq
  exact hd.deriv.trans (by dsimp only [hillHminusDiscriminantDerivative]; ring)

theorem norm_ge_half_free_center (k : ℕ+) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    Real.pi/2*(k : ℝ) ≤ ‖z‖ := by
  have ht := norm_sub_norm_le ((Real.pi : ℂ)*(k : ℕ)) z
  rw [norm_sub_rev] at ht
  have hc : ‖(Real.pi : ℂ)*(k : ℕ)‖ = Real.pi*(k : ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_natCast]
  rw [hc] at ht
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hd := mem_closedBall_iff_norm.mp hz
  nlinarith [Real.pi_pos]

theorem exists_hillHminus_uniform_inner_differential_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ k : ℕ+,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8),
          (z^2,q) ∈ hillHminusContinuationDomain ∧
          ‖hillHminusDiscriminantDerivative (z^2,q)/hillHminusContinuedRoot (z^2,q)‖ ≤ C/(k : ℝ) := by
  obtain ⟨δ,b,hδ,hb,htrace,hroot⟩ := exists_hillHminus_uniform_inner_root_bound
    (Real.pi/8) (by positivity) (by linarith [Real.pi_pos])
  let B := 1+2*Real.exp (Real.pi/4)
  let L := B/(Real.pi/4-Real.pi/8)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hL : 0 < L := div_pos hB (by linarith [Real.pi_pos])
  refine ⟨δ,L/(Real.pi*b),hδ,by positivity,?_⟩
  intro q hq k z hz
  obtain ⟨ht,hr⟩ := hroot q hq k z hz
  have hzsmall := mem_closedBall_iff_norm.mp (sphere_subset_closedBall hz)
  have hzdisc : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
    closedBall_subset_closedBall (by linarith [Real.pi_pos]) (sphere_subset_closedBall hz)
  have hf : Differentiable ℂ (fun w : ℂ => hillHminusDiscriminant q (w^2)) := by
    intro w
    exact (((analyticOnNhd_hillHminusDiscriminant_joint (w^2,q) (mem_univ _)).comp
      (f := fun v : ℂ => (v^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)).differentiableAt)
  have hd := norm_deriv_le_of_closedDisc_bound hf ((Real.pi : ℂ)*(k : ℕ))
    (show Real.pi/8 < Real.pi/4 by linarith [Real.pi_pos]) B
    (fun w hw => htrace q hq k w (mem_closedBall_iff_norm.mpr hw)) hzsmall
  rw [hillHminus_frequency_derivative_eq,norm_mul,norm_mul,norm_ofNat] at hd
  have hzlower := norm_ge_half_free_center k z hzdisc
  have hk : (0 : ℝ) < k := by positivity
  have hden : 0 < Real.pi*(k : ℝ) := mul_pos Real.pi_pos hk
  have hD : ‖hillHminusDiscriminantDerivative (z^2,q)‖ ≤ L/(Real.pi*(k : ℝ)) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right hzlower (norm_nonneg (hillHminusDiscriminantDerivative (z^2,q)))
    change 2*‖z‖*‖hillHminusDiscriminantDerivative (z^2,q)‖ ≤ L at hd
    nlinarith
  refine ⟨ht,?_⟩
  rw [norm_div]
  calc
    _ ≤ (L/(Real.pi*(k : ℝ)))/b := by
      gcongr
    _ = (L/(Real.pi*b))/(k : ℝ) := by ring
end NLS.KdV
