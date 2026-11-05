import NLS.MKdV.L2QuasiHillWeakEquation
import NLS.MKdV.L2QuasiHillScalarNontrivial
import NLS.FunctionalAnalysis.IntervalH1Conjugation
import NLS.FunctionalAnalysis.IntervalCurveMass

/-! # Strictly positive Dirichlet energies for a real physical Miura profile

The actual weak Green identity is the factorization identity with
ordinary physical L2 masses. Both masses are positive for the normalized
Dirichlet column: the position is nonzero and the momentum starts at one.
No profile derivative or endpoint trace of the L2 profile is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

theorem l2QuasiHillDirichlet_energy_pos_of_real_profile (u : IntervalL2) (hu : star u = u)
    (mu : ℝ) (hz : extend (l2QuasiHillPosition u mu (0,1)) 1 = 0) : 0 < mu := by
  let y := l2QuasiHillPosition u mu (0,1)
  let w := l2QuasiHillMomentum u mu (0,1)
  have hy := absolutelyContinuous_l2QuasiHillPosition u mu (0,1)
  have hy₂ := memLp_deriv_l2QuasiHillPosition u mu (0,1)
  have hy₀ : extend y 0 = 0 := l2QuasiHillPosition_initial _ _ _
  have hy₁ : extend y 1 = 0 := hz
  have hφ₀ : extend (star y) 0 = 0 := by change conj (extend y 0) = 0; rw [hy₀,map_zero]
  have hφ₁ : extend (star y) 1 = 0 := by change conj (extend y 1) = 0; rw [hy₁,map_zero]
  have hg := l2QuasiHill_weak_green_identity u mu 0 (0,1) (star y)
    (absolutelyContinuous_curve_star y hy) (memLp_deriv_curve_star y hy₂)
  rw [hφ₀,hφ₁,mul_zero,mul_zero,sub_self,zero_add,sub_zero] at hg
  have huAE : (fun t => conj (u t)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] u := by
    have h := Lp.coeFn_star u
    rw [hu] at h
    exact h.symm
  have hf : shiftedMiuraWeakForm u 0 y (star y) =
      ∫ t in (0 : ℝ)..1, extend w t*conj (extend w t) := by
    unfold shiftedMiuraWeakForm
    rw [zero_mul,sub_zero]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [ae_deriv_l2QuasiHillPosition u mu (0,1),huAE] with t ht huT
    change deriv (extend y) t = u t*extend y t+extend w t at ht
    change (deriv (extend y) t-u t*extend y t)*
      (deriv (extend (star y)) t-u t*conj (extend y t)) = extend w t*conj (extend w t)
    rw [deriv_extend_curve_star]
    dsimp only
    rw [ht,map_add,map_mul,huT]
    ring
  rw [hf] at hg
  have hw : w ≠ 0 := by
    intro he
    have h := l2QuasiHillMomentum_initial u mu ((0,1) : ℂ × ℂ)
    change extend w 0 = 1 at h
    rw [he] at h
    norm_num [NLS.LinearVolterra.extend] at h
  have hm := integral_curve_mul_conj_re_pos w hw
  have hyMass := integral_curve_mul_conj_re_pos y (l2QuasiHillPosition_ne_zero u mu (0,1) (by simp))
  have he := congrArg Complex.re hg
  change (∫ t in (0 : ℝ)..1, extend w t*conj (extend w t)).re =
    ((mu : ℂ)*(∫ t in (0 : ℝ)..1, extend y t*conj (extend y t))).re at he
  rw [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] at he
  exact pos_of_mul_pos_left (he ▸ hm) hyMass.le

end NLS.MKdV
