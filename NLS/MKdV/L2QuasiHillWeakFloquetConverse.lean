import NLS.MKdV.L2QuasiHillWeakReconstruction
import NLS.MKdV.L2QuasiHillScalarNontrivial

/-! # The weak Floquet equation recovers both state endpoint conditions

An actual H1 test with endpoints one and sigma inverse recovers the
momentum multiplier from Green's identity. Together with weak local
reconstruction, every nonzero scalar weak Floquet solution is an actual
nonzero quasi-Hill initial-value state with that same multiplier.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

theorem l2QuasiHillSolution_multiplier_of_weak_equation (u : IntervalL2) (c lambda σ : ℂ) (hσ : σ ≠ 0)
    (v : ℂ × ℂ)
    (hyend : extend (l2QuasiHillPosition u (lambda+c) v) 1 = σ*extend (l2QuasiHillPosition u (lambda+c) v) 0)
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 1 = σ⁻¹*extend φ 0 →
      shiftedMiuraWeakForm u c (l2QuasiHillPosition u (lambda+c) v) φ =
        lambda*(∫ s in (0 : ℝ)..1, extend (l2QuasiHillPosition u (lambda+c) v) s*extend φ s)) :
    l2QuasiHillSolution u (lambda+c) v ⟨1,by constructor <;> norm_num⟩ = σ • v := by
  have hi : IntervalIntegrable (fun _ : ℝ => σ⁻¹-1) volume 0 1 := continuous_const.intervalIntegrable 0 1
  let G := unitIntervalPrimitiveCurve (fun _ : ℝ => σ⁻¹-1) hi
  let φ : Curve ℂ := ContinuousMap.const _ 1+G
  have hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1 :=
    absolutelyContinuousOnInterval_const_add (absolutelyContinuous_unitIntervalPrimitiveCurve _ hi) 1
  have hφ₀ : extend φ 0 = 1 := by
    change 1+extend G 0 = 1
    rw [unitIntervalPrimitiveCurve_zero,add_zero]
  have hφ₁ : extend φ 1 = σ⁻¹ := by
    change 1+extend G 1 = _
    rw [unitIntervalPrimitiveCurve_one,intervalIntegral.integral_const]
    simp only [sub_zero,one_smul]
    ring
  have hdφ : deriv (extend φ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun _ => σ⁻¹-1 := by
    filter_upwards [ae_hasDerivAt_unitIntervalPrimitiveCurve (fun _ : ℝ => σ⁻¹-1) hi] with s hs
    exact (hs.const_add 1).deriv
  have hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_congr_ae hdφ).mpr (memLp_const _)
  have he := hw φ hφ hφ₂ (by rw [hφ₀,hφ₁,mul_one])
  have hg := l2QuasiHill_weak_green_identity u (lambda+c) c v φ hφ hφ₂
  rw [add_sub_cancel_right,hφ₀,hφ₁,mul_one] at hg
  have hb : extend (l2QuasiHillMomentum u (lambda+c) v) 1*σ⁻¹-
      extend (l2QuasiHillMomentum u (lambda+c) v) 0 = 0 := by
    linear_combination he-hg
  have hendW : extend (l2QuasiHillMomentum u (lambda+c) v) 1 =
      σ*extend (l2QuasiHillMomentum u (lambda+c) v) 0 := by
    calc
      _ = (σ*σ⁻¹)*extend (l2QuasiHillMomentum u (lambda+c) v) 1 := by rw [mul_inv_cancel₀ hσ,one_mul]
      _ = σ*(extend (l2QuasiHillMomentum u (lambda+c) v) 1*σ⁻¹) := by ring
      _ = _ := by rw [sub_eq_zero.mp hb]
  apply Prod.ext
  · have he₁ := hyend
    rw [l2QuasiHillPosition_initial] at he₁
    change (extend (l2QuasiHillSolution u (lambda+c) v)
      ((⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℝ)).1 = σ*v.1 at he₁
    rw [extend_coe] at he₁
    exact he₁
  · rw [l2QuasiHillMomentum_initial] at hendW
    change (extend (l2QuasiHillSolution u (lambda+c) v)
      ((⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℝ)).2 = σ*v.2 at hendW
    rw [extend_coe] at hendW
    exact hendW

/-- No quasi-derivative or state endpoint condition is assumed: both are
recovered from the scalar H1 weak formulation and its scalar multiplier. -/
theorem exists_nonzero_Floquet_initial_state_of_weak_equation (u : IntervalL2) (c lambda σ : ℂ) (hσ : σ ≠ 0)
    (y : Curve ℂ) (hy0 : y ≠ 0) (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hyend : extend y 1 = σ*extend y 0)
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 1 = σ⁻¹*extend φ 0 →
      shiftedMiuraWeakForm u c y φ = lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)) :
    ∃ v : ℂ × ℂ, v ≠ 0 ∧ y = l2QuasiHillPosition u (lambda+c) v ∧
      l2QuasiHillSolution u (lambda+c) v ⟨1,by constructor <;> norm_num⟩ = σ • v := by
  obtain ⟨v,hv,he⟩ := exists_nonzero_initial_state_of_weak_Hill_equation u c lambda y hy0 hy hy₂ (by
    intro φ hφ hφ₂ hφ₀ hφ₁
    exact hw φ hφ hφ₂ (by rw [hφ₀,hφ₁,mul_zero]))
  refine ⟨v,hv,he,?_⟩
  apply l2QuasiHillSolution_multiplier_of_weak_equation u c lambda σ hσ v
  · rw [← he]
    exact hyend
  · intro φ hφ hφ₂ hφend
    rw [← he]
    exact hw φ hφ hφ₂ hφend

end NLS.MKdV
