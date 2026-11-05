import NLS.MKdV.L2QuasiHillWeakMomentum
import NLS.MKdV.L2QuasiHillUniqueness

/-! # Arbitrary scalar weak solutions are actual rough Hill IVP solutions

The recovered AC momentum and position form an actual AC state. Its
first-order equation integrates to the original representative Volterra
problem, whose proved uniqueness identifies the entire state and scalar
position with the prescribed-data solution.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

theorem l2QuasiHillSolution_eq_of_AC_state (u : IntervalL2) (μ : ℂ) (y W : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hW : AbsolutelyContinuousOnInterval (extend W) 0 1)
    (hd : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend y) (u s*extend y s+extend W s) s ∧
      HasDerivAt (extend W) (-μ*extend y s-u s*extend W s) s) :
    y.prodMk W = l2QuasiHillSolution u μ (extend y 0,extend W 0) := by
  let Y := y.prodMk W
  have hyP := absolutelyContinuousOnInterval_clm hy
    ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))
  have hWP := absolutelyContinuousOnInterval_clm hW
    ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ))
  have hAC : AbsolutelyContinuousOnInterval (extend Y) 0 1 := by
    simpa only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply,Pi.add_def,
      Prod.mk_add_mk,add_zero,zero_add] using! hyP.add hWP
  have hder : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend Y) (quasiHillCoefficient (u s) μ (extend Y s)) s :=
    hd.mono (fun _ hs => hs.1.prodMk hs.2)
  rw [ae_restrict_iff' measurableSet_Ioc] at hder
  have hn : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by simp [ae_iff]
  have hglobal : ∀ᵐ s : ℝ ∂volume, s ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (extend Y) (quasiHillCoefficient (u s) μ (extend Y s)) s := by
    filter_upwards [hder,hn] with s hs hn hx
    have hxi : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact hs ⟨lt_of_le_of_ne hxi.1 (Ne.symm hn),hxi.2⟩
  apply l2QuasiHillSolution_unique_integral
  intro t
  have hsub : uIcc (0 : ℝ) t.val ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le t.property.1,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl t.property.2
  have hi := intervalIntegrable_quasiHillCoefficient u μ Y t
  have he := integral_eq_sub_of_ac_of_ae_hasDerivAt (hAC.mono hsub) hi
    (hglobal.mono (fun _ hs hx => hs (hsub hx)))
  rw [extend_coe Y t] at he
  change Y t = extend Y 0+∫ s in (0 : ℝ)..t.val, quasiHillCoefficient (u s) μ (extend Y s)
  rw [he]
  abel

theorem exists_initial_state_of_weak_Hill_equation (u : IntervalL2) (c lambda : ℂ) (y : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      shiftedMiuraWeakForm u c y φ = lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)) :
    ∃ v : ℂ × ℂ, y = l2QuasiHillPosition u (lambda+c) v := by
  obtain ⟨W,hW,hd⟩ := exists_AC_momentum_of_weak_Hill_equation u c lambda y hy hy₂ hw
  have he := l2QuasiHillSolution_eq_of_AC_state u (lambda+c) y W hy hW hd
  refine ⟨(extend y 0,extend W 0),?_⟩
  apply ContinuousMap.ext
  intro t
  exact congrArg Prod.fst (congrArg (fun F : Curve (ℂ × ℂ) => F t) he)

theorem l2QuasiHillPosition_zero_initial (u : IntervalL2) (μ : ℂ) : l2QuasiHillPosition u μ 0 = 0 := by
  apply ContinuousMap.ext
  intro t
  change (quasiHillFixedState (l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ)
    (quasiHillFixedStateInv 0) t)).1 = 0
  rw [map_zero,l2SolutionCurve_zero_initial]
  simp only [ContinuousMap.zero_apply,map_zero,Prod.fst_zero]

theorem exists_nonzero_initial_state_of_weak_Hill_equation (u : IntervalL2) (c lambda : ℂ) (y : Curve ℂ)
    (hy0 : y ≠ 0) (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      shiftedMiuraWeakForm u c y φ = lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)) :
    ∃ v : ℂ × ℂ, v ≠ 0 ∧ y = l2QuasiHillPosition u (lambda+c) v := by
  obtain ⟨v,he⟩ := exists_initial_state_of_weak_Hill_equation u c lambda y hy hy₂ hw
  refine ⟨v,?_,he⟩
  intro hv
  rw [hv,l2QuasiHillPosition_zero_initial] at he
  exact hy0 he

end NLS.MKdV
