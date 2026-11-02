import NLS.MKdV.QuasiHillPhysicalEquation
import NLS.FunctionalAnalysis.LinearVolterraRegularity

/-! # Uniqueness in the physical scalar Miura–Hill equation

An absolutely continuous scalar solution with absolutely continuous first
derivative is exactly the independent quasi-Hill IVP solution with the same
initial position and derivative. Thus the quasi-derivative construction is
characterized by the physical second-order equation and its initial data.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra
open NLS.FunctionalAnalysis
namespace NLS.MKdV

/-- The independent scalar column and its actual first derivative have the
absolute continuity required for the physical second-order IVP. -/
theorem quasiHillSolution_scalar_regular
    (U : Curve ℂ) (u : ℝ → ℂ) (hU : ∀ t, U t = u t)
    (hu : AbsolutelyContinuousOnInterval u 0 1) (μ : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (fun x => (quasiHillSolution U μ v x).1) 0 1 ∧
      AbsolutelyContinuousOnInterval (deriv (fun x => (quasiHillSolution U μ v x).1)) 0 1 := by
  have hF := absolutelyContinuous_solution (realCoefficient (quasiHillCoefficientCurve U μ)) v
  have hG := absolutelyContinuousOnInterval_clm hF (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hW := absolutelyContinuousOnInterval_clm hF (ContinuousLinearMap.snd ℝ ℂ ℂ)
  change AbsolutelyContinuousOnInterval (fun x => (quasiHillSolution U μ v x).1) 0 1 at hG
  change AbsolutelyContinuousOnInterval (fun x => (quasiHillSolution U μ v x).2) 0 1 at hW
  have hsum : AbsolutelyContinuousOnInterval
      (fun x => u x*(quasiHillSolution U μ v x).1+(quasiHillSolution U μ v x).2) 0 1 := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.add_def] using! (hu.smul hG).add hW
  refine ⟨hG, absolutelyContinuousOnInterval_congr hsum ?_⟩
  intro x hx
  have hxi : x ∈ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hx
  have hd := (hasDerivAt_fst_quasiHillSolution U μ v ⟨x,hxi⟩).deriv
  rw [hU ⟨x,hxi⟩] at hd
  exact hd.symm

/-- Physical scalar solutions determine the independent quasi-Hill solution. -/
theorem physicalMiuraSolution_eq_quasiHill
    (U : Curve ℂ) (u : ℝ → ℂ) (hU : ∀ t, U t = u t)
    (hu : AbsolutelyContinuousOnInterval u 0 1) (μ : ℂ)
    (g : ℝ → ℂ) (hg : AbsolutelyContinuousOnInterval g 0 1)
    (hdg : AbsolutelyContinuousOnInterval (deriv g) 0 1)
    (heq : ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      -deriv (deriv g) x+miuraPotential u x*g x = μ*g x) :
    EqOn (fun x => (g x,deriv g x-u x*g x))
      (quasiHillSolution U μ (g 0,deriv g 0-u 0*g 0)) (Icc 0 1) := by
  have hug : AbsolutelyContinuousOnInterval (fun x => u x*g x) 0 1 := by
    simpa only [Pi.smul_def, smul_eq_mul] using! hu.smul hg
  have hw : AbsolutelyContinuousOnInterval (fun x => deriv g x-u x*g x) 0 1 := by
    simpa only [Pi.sub_apply] using! hdg.sub hug
  have h1 := absolutelyContinuousOnInterval_clm hg (ContinuousLinearMap.inl ℝ ℂ ℂ)
  have h2 := absolutelyContinuousOnInterval_clm hw (ContinuousLinearMap.inr ℝ ℂ ℂ)
  have hstate : AbsolutelyContinuousOnInterval (fun x => (g x,deriv g x-u x*g x)) 0 1 := by
    apply absolutelyContinuousOnInterval_congr (h1.add h2)
    intro x _
    simp only [Pi.add_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
      Prod.add_def, add_zero, zero_add]
  apply solution_unique_of_ac (realCoefficient (quasiHillCoefficientCurve U μ)) _ hstate
  filter_upwards [ae_differentiableAt_complex hu, ae_differentiableAt_complex hg,
    ae_differentiableAt_complex hdg, heq,
    (show ∀ᵐ x : ℝ, x ≠ (0 : ℝ) from by simp [ae_iff, measure_singleton]),
    (show ∀ᵐ x : ℝ, x ≠ (1 : ℝ) from by simp [ae_iff, measure_singleton])] with x hxU hxG hxDG hxE hx0 hx1
  intro hxi
  have hxI : x ∈ uIcc (0 : ℝ) 1 := by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact hxi
  have hxO : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hxi.1 (Ne.symm hx0), lt_of_le_of_ne hxi.2 hx1⟩
  have hd := (hxG hxI).hasDerivAt.prodMk
    ((hxDG hxI).hasDerivAt.sub ((hxU hxI).hasDerivAt.mul (hxG hxI).hasDerivAt))
  have hC : extend (realCoefficient (quasiHillCoefficientCurve U μ)) x =
      (quasiHillCoefficient (u x) μ).restrictScalars ℝ := by
    rw [extend_coe _ ⟨x,hxi⟩]
    simp only [realCoefficient, ContinuousMap.coe_mk, quasiHillCoefficientCurve_apply, hU ⟨x,hxi⟩]
  rw [hC]
  convert! hd using 1
  apply Prod.ext
  · change u x*g x+(deriv g x-u x*g x) = deriv g x
    ring
  · have h := hxE hxO
    dsimp [miuraPotential] at h
    change -μ*g x-u x*(deriv g x-u x*g x) =
      deriv (deriv g) x-(deriv u x*g x+u x*deriv g x)
    linear_combination h

end NLS.MKdV
