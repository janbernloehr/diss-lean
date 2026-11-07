import NLS.MKdV.QuasiHillL2DirichletCriterion

/-! # Physical interval functions as actual quasi-Hill weak states

Both rows are given by their independent almost-everywhere ODE. Restriction
to the closed interval and constant endpoint extension preserve the full weak
state; no boundary condition is imposed on the second component.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.FunctionalAnalysis
open NLS.Fourier
namespace NLS.MKdV

/-- A continuous physical position/quasi-derivative pair on the source interval. -/
def quasiHillIntervalState (Y G : ℝ → ℂ) (hY : Continuous Y) (hG : Continuous G) :
    Curve (ℂ × ℂ) :=
  ⟨fun t => (Y t.val,G t.val), (hY.prodMk hG).comp continuous_subtype_val⟩

@[simp] theorem quasiHillIntervalState_apply (Y G : ℝ → ℂ)
    (hY : Continuous Y) (hG : Continuous G) (t : Icc (0:ℝ) 1) :
    quasiHillIntervalState Y G hY hG t = (Y t.val,G t.val) := rfl

/-- Constant extension agrees with both original physical functions on the entire interval. -/
theorem extend_quasiHillIntervalState (Y G : ℝ → ℂ)
    (hY : Continuous Y) (hG : Continuous G) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    extend (quasiHillIntervalState Y G hY hG) t = (Y t,G t) := by
  exact (extend_coe (quasiHillIntervalState Y G hY hG) ⟨t,ht⟩)

/-- The two actual physical rows produce an actual absolutely continuous
quasi-Hill weak state with the original physical L2 coefficient. -/
theorem isQuasiHillL2Solution_intervalState (u : NLS.Coeff 2) (lambda : ℂ)
    (Y G : ℝ → ℂ) (hY : Continuous Y) (hG : Continuous G)
    (hYa : AbsolutelyContinuousOnInterval Y 0 1)
    (hGa : AbsolutelyContinuousOnInterval G 0 1)
    (hYd : ∀ᵐ x ∂volume.restrict (Ioc 0 1),
      HasDerivAt Y (unitL2SynthesisEquiv u x*Y x+G x) x)
    (hGd : ∀ᵐ x ∂volume.restrict (Ioc 0 1),
      HasDerivAt G (-lambda*Y x-unitL2SynthesisEquiv u x*G x) x) :
    IsQuasiHillL2Solution u lambda (quasiHillIntervalState Y G hY hG) := by
  have h1 : AbsolutelyContinuousOnInterval (fun x => (Y x,(0:ℂ))) 0 1 :=
    absolutelyContinuousOnInterval_clm hYa (ContinuousLinearMap.inl ℝ ℂ ℂ)
  have h2 : AbsolutelyContinuousOnInterval (fun x => ((0:ℂ),G x)) 0 1 :=
    absolutelyContinuousOnInterval_clm hGa (ContinuousLinearMap.inr ℝ ℂ ℂ)
  have hp : AbsolutelyContinuousOnInterval (fun x => (Y x,G x)) 0 1 := by
    simpa only [Pi.add_def, Prod.add_def, add_zero, zero_add] using h1.add h2
  refine ⟨absolutelyContinuousOnInterval_congr hp ?_, ?_⟩
  · intro x hx
    exact (extend_quasiHillIntervalState Y G hY hG (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)).symm
  · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by simp [ae_iff]
    filter_upwards [hYd, hGd, ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with x hy hg hx hx1
    have hxi : x ∈ Ioo (0:ℝ) 1 := ⟨hx.1,lt_of_le_of_ne hx.2 hx1⟩
    have he : extend (quasiHillIntervalState Y G hY hG) =ᶠ[𝓝 x]
        (fun y => (Y y,G y)) := by
      filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
      exact extend_quasiHillIntervalState Y G hY hG ⟨hy.1.le,hy.2.le⟩
    have hd := (hy.prodMk hg).congr_of_eventuallyEq he
    rw [extend_quasiHillIntervalState Y G hY hG ⟨hx.1.le,hx.2⟩]
    exact hd

end NLS.MKdV
