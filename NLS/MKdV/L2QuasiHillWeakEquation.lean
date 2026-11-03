import NLS.MKdV.L2QuasiHillRegularity

/-! # The actual rough Hill weak equation and its boundary term

The shifted Miura form uses the scalar position and its weak first
derivative. Every actual quasi-Hill solution satisfies its Green identity
against every absolutely continuous test with L2 derivative. Boundary
terms involve the continuous quasi-derivative, never point values of u.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

/-- The bilinear weak form of -d^2+(u'+u^2)-c, factorized at the actual
L2 profile u. Each interval has length one and ordinary Lebesgue measure. -/
def shiftedMiuraWeakForm (u : IntervalL2) (c : ℂ) (y φ : Curve ℂ) : ℂ :=
  (∫ s in (0 : ℝ)..1, (deriv (extend y) s-u s*extend y s)*
    (deriv (extend φ) s-u s*extend φ s))-c*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)

theorem intervalIntegrable_of_memLp_two {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) : IntervalIntegrable f volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (hf.integrable (by norm_num))

/-- The form integrand is genuinely integrable on every pair of H1
curves, before applying an eigen-equation. -/
theorem intervalIntegrable_shiftedMiuraWeakIntegrand (u : IntervalL2) (y φ : Curve ℂ)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    IntervalIntegrable (fun s => (deriv (extend y) s-u s*extend y s)*
      (deriv (extend φ) s-u s*extend φ s)) volume 0 1 := by
  have hy := hy₂.sub (memLp_intervalL2_mul_curve u y)
  have hφ := hφ₂.sub (memLp_intervalL2_mul_curve u φ)
  have hp : MemLp (fun s => (deriv (extend y) s-u s*extend y s)*
      (deriv (extend φ) s-u s*extend φ s)) 1 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hφ.mul hy
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (hp.integrable le_rfl)

/-- Green's identity retains the full endpoint term, so it applies to
Dirichlet, periodic, antiperiodic and reciprocal Floquet tests. -/
theorem l2QuasiHill_weak_green_identity (u : IntervalL2) (μ c : ℂ) (v : ℂ × ℂ)
    (φ : Curve ℂ) (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    shiftedMiuraWeakForm u c (l2QuasiHillPosition u μ v) φ =
      extend (l2QuasiHillMomentum u μ v) 1*extend φ 1-
        extend (l2QuasiHillMomentum u μ v) 0*extend φ 0+
        (μ-c)*(∫ s in (0 : ℝ)..1, extend (l2QuasiHillPosition u μ v) s*extend φ s) := by
  let y := extend (l2QuasiHillPosition u μ v)
  let w := extend (l2QuasiHillMomentum u μ v)
  let ψ := extend φ
  have hw := absolutelyContinuous_l2QuasiHillMomentum u μ v
  have hwi := intervalIntegrable_of_memLp_two (memLp_deriv_l2QuasiHillMomentum u μ v)
  have hψi := intervalIntegrable_of_memLp_two hφ₂
  have hwψd := hψi.continuousOn_mul hw.continuousOn
  have hwuψ := (intervalIntegrable_of_memLp_two (memLp_intervalL2_mul_curve u φ)).continuousOn_mul hw.continuousOn
  have hyψ : IntervalIntegrable (fun s => y s*ψ s) volume 0 1 :=
    (((continuous_extend (l2QuasiHillPosition u μ v)).mul (continuous_extend φ)).intervalIntegrable 0 1)
  have hμyψ := hyψ.const_mul (-μ)
  have he : (∫ s in (0 : ℝ)..1, deriv w s*ψ s) =
      -μ*(∫ s in (0 : ℝ)..1, y s*ψ s)-(∫ s in (0 : ℝ)..1, w s*(u s*ψ s)) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, -μ*(y s*ψ s)-w s*(u s*ψ s) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        filter_upwards [ae_deriv_l2QuasiHillMomentum u μ v] with s hs
        change deriv w s = -μ*y s-u s*w s at hs
        rw [hs]
        ring
      _ = _ := by rw [intervalIntegral.integral_sub hμyψ hwuψ,intervalIntegral.integral_const_mul]
  have hip := integral_mul_deriv_eq_complex hw hφ hwi hψi
  change (∫ s in (0 : ℝ)..1, w s*deriv ψ s) =
    w 1*ψ 1-w 0*ψ 0-∫ s in (0 : ℝ)..1, deriv w s*ψ s at hip
  rw [he] at hip
  have hfactor : (∫ s in (0 : ℝ)..1, (deriv y s-u s*y s)*(deriv ψ s-u s*ψ s)) =
      ∫ s in (0 : ℝ)..1, w s*(deriv ψ s-u s*ψ s) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [ae_deriv_l2QuasiHillPosition u μ v] with s hs
    change deriv y s = u s*y s+w s at hs
    rw [hs,add_sub_cancel_left]
  change (∫ s in (0 : ℝ)..1, (deriv y s-u s*y s)*(deriv ψ s-u s*ψ s))-
    c*(∫ s in (0 : ℝ)..1, y s*ψ s) = _
  rw [hfactor]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hwψd hwuψ,hip]
  ring

/-- Zero test endpoints give the actual weak scalar eigen-equation. -/
theorem l2QuasiHill_weak_equation_zero_endpoints (u : IntervalL2) (μ c : ℂ) (v : ℂ × ℂ)
    (φ : Curve ℂ) (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₀ : extend φ 0 = 0) (hφ₁ : extend φ 1 = 0) :
    shiftedMiuraWeakForm u c (l2QuasiHillPosition u μ v) φ =
      (μ-c)*(∫ s in (0 : ℝ)..1, extend (l2QuasiHillPosition u μ v) s*extend φ s) := by
  rw [l2QuasiHill_weak_green_identity u μ c v φ hφ hφ₂,hφ₀,hφ₁]
  ring

end NLS.MKdV
