import NLS.MKdV.L2QuasiHillWeakEquation
import NLS.FunctionalAnalysis.UnitIntervalWeakDerivativeAC

/-! # Recovering the continuous quasi-derivative of a weak Hill solution

The raw momentum y'-u*y lies in L2. The weak scalar equation proves its
L1 weak derivative equation against every H1 Dirichlet test. The interval
regularity theorem constructs its absolutely continuous representative,
with both actual first-order state equations holding almost everywhere.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

def rawWeakHillMomentum (u : IntervalL2) (y : Curve ℂ) (s : ℝ) : ℂ :=
  deriv (extend y) s-u s*extend y s

theorem memLp_rawWeakHillMomentum (u : IntervalL2) (y : Curve ℂ)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (rawWeakHillMomentum u y) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  hy₂.sub (memLp_intervalL2_mul_curve u y)

def rawWeakHillMomentumRhs (u : IntervalL2) (μ : ℂ) (y : Curve ℂ) (s : ℝ) : ℂ :=
  -u s*rawWeakHillMomentum u y s-μ*extend y s

theorem intervalIntegrable_rawWeakHillMomentumRhs (u : IntervalL2) (μ : ℂ) (y : Curve ℂ)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    IntervalIntegrable (rawWeakHillMomentumRhs u μ y) volume 0 1 := by
  have hprod : MemLp (fun s => u s*rawWeakHillMomentum u y s) 1 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_rawWeakHillMomentum u y hy₂).mul (Lp.memLp u)
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hprod.integrable le_rfl)
  change IntervalIntegrable (fun s => -u s*rawWeakHillMomentum u y s-μ*extend y s) volume 0 1
  simp only [neg_mul]
  exact hi.neg.sub (((continuous_extend y).intervalIntegrable 0 1).const_mul μ)

/-- The full H1 test class supplies the weak derivative of raw momentum;
no continuous quasi-derivative is assumed in the hypotheses. -/
theorem rawWeakHillMomentum_weak_equation (u : IntervalL2) (c lambda : ℂ) (y : Curve ℂ)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      shiftedMiuraWeakForm u c y φ = lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s))
    (φ : Curve ℂ) (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₀ : extend φ 0 = 0) (hφ₁ : extend φ 1 = 0) :
    (∫ s in (0 : ℝ)..1, rawWeakHillMomentum u y s*deriv (extend φ) s) =
      -(∫ s in (0 : ℝ)..1, rawWeakHillMomentumRhs u (lambda+c) y s*extend φ s) := by
  have hP := memLp_rawWeakHillMomentum u y hy₂
  have hi₁ : IntervalIntegrable (fun s => rawWeakHillMomentum u y s*deriv (extend φ) s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((show MemLp (fun s => rawWeakHillMomentum u y s*deriv (extend φ) s) 1
        (volume.restrict (Ioc (0 : ℝ) 1)) from hφ₂.mul hP).integrable le_rfl)
  have hi₂ : IntervalIntegrable (fun s => rawWeakHillMomentum u y s*(u s*extend φ s)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((show MemLp (fun s => rawWeakHillMomentum u y s*(u s*extend φ s)) 1
        (volume.restrict (Ioc (0 : ℝ) 1)) from (memLp_intervalL2_mul_curve u φ).mul hP).integrable le_rfl)
  have hiY : IntervalIntegrable (fun s => extend y s*extend φ s) volume 0 1 :=
    ((continuous_extend y).mul (continuous_extend φ)).intervalIntegrable 0 1
  have he := hw φ hφ hφ₂ hφ₀ hφ₁
  change (∫ s in (0 : ℝ)..1, rawWeakHillMomentum u y s*(deriv (extend φ) s-u s*extend φ s))-
    c*(∫ s in (0 : ℝ)..1, extend y s*extend φ s) = _ at he
  simp_rw [mul_sub] at he
  rw [intervalIntegral.integral_sub hi₁ hi₂] at he
  have hg : (∫ s in (0 : ℝ)..1, rawWeakHillMomentumRhs u (lambda+c) y s*extend φ s) =
      -(∫ s in (0 : ℝ)..1, rawWeakHillMomentum u y s*(u s*extend φ s))-
        (lambda+c)*(∫ s in (0 : ℝ)..1, extend y s*extend φ s) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, -(rawWeakHillMomentum u y s*(u s*extend φ s))-
          (lambda+c)*(extend y s*extend φ s) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only [rawWeakHillMomentumRhs]
        ring
      _ = _ := by
        have hn : IntervalIntegrable (fun s => -(rawWeakHillMomentum u y s*(u s*extend φ s))) volume 0 1 := by
          simpa only [Pi.neg_apply] using! hi₂.neg
        rw [intervalIntegral.integral_sub hn (hiY.const_mul (lambda+c)),
          intervalIntegral.integral_neg,intervalIntegral.integral_const_mul]
  rw [hg]
  linear_combination he

/-- Every weak scalar solution has a genuine absolutely continuous
momentum, and the two actual first-order equations hold a.e. -/
theorem exists_AC_momentum_of_weak_Hill_equation (u : IntervalL2) (c lambda : ℂ) (y : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      shiftedMiuraWeakForm u c y φ = lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)) :
    ∃ W : Curve ℂ, AbsolutelyContinuousOnInterval (extend W) 0 1 ∧
      ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
        HasDerivAt (extend y) (u s*extend y s+extend W s) s ∧
        HasDerivAt (extend W) (-(lambda+c)*extend y s-u s*extend W s) s := by
  obtain ⟨W,hW,hWAC,hWd⟩ := exists_AC_curve_of_H1_weak_derivative (rawWeakHillMomentum u y)
    (rawWeakHillMomentumRhs u (lambda+c) y) (memLp_rawWeakHillMomentum u y hy₂)
    (intervalIntegrable_rawWeakHillMomentumRhs u (lambda+c) y hy₂)
    (rawWeakHillMomentum_weak_equation u c lambda y hy₂ hw)
  refine ⟨W,hWAC,?_⟩
  filter_upwards [hW,hWd,ae_restrict_of_ae (ae_differentiableAt_complex hy),
    ae_restrict_mem measurableSet_Ioc] with s hs hd hyD hmem
  have hi : s ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using Ioc_subset_Icc_self hmem
  have he : deriv (extend y) s = u s*extend y s+extend W s := by
    change deriv (extend y) s-u s*extend y s = extend W s at hs
    linear_combination hs
  refine ⟨by rw [← he]; exact (hyD hi).hasDerivAt,?_⟩
  convert! hd using 1
  dsimp only [rawWeakHillMomentumRhs]
  rw [hs]
  ring

end NLS.MKdV
