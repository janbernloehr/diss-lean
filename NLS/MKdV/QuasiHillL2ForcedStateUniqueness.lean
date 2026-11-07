import NLS.MKdV.QuasiHillL2ForcedCurve
import NLS.MKdV.QuasiHillL2IntervalState

/-! # Physical forced states and uniqueness from their scalar positions -/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.MKdV
open NLS.Fourier

/-- The actual forced physical rows give the AC curve state with exactly
the supplied preceding scalar position. -/
theorem isQuasiHillL2ForcedSolution_intervalState (u : Coeff 2) (lambda : ℂ)
    (v : Curve (ℂ × ℂ)) (Y G : ℝ → ℂ) (hY : Continuous Y) (hG : Continuous G)
    (hYa : AbsolutelyContinuousOnInterval Y 0 1) (hGa : AbsolutelyContinuousOnInterval G 0 1)
    (hYd : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt Y
      (unitL2SynthesisEquiv u x*Y x+G x) x)
    (hGd : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
      (-lambda*Y x-unitL2SynthesisEquiv u x*G x-(extend v x).1) x) :
    IsQuasiHillL2ForcedSolution u lambda v (quasiHillIntervalState Y G hY hG) := by
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
    convert! hd using 1
    apply Prod.ext <;> simp [quasiHillCoefficient_apply, sub_eq_add_neg]

/-- Equal scalar positions determine the ENTIRE forced states, even when
their preceding states differ. Only the common first physical row is used. -/
theorem IsQuasiHillL2ForcedSolution.eq_of_position_eq (u : Coeff 2) (lambda : ℂ)
    (v w v' z : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2ForcedSolution u lambda v w)
    (hz : IsQuasiHillL2ForcedSolution u lambda v' z)
    (hp : ∀ t : Icc (0:ℝ) 1, (w t).1 = (z t).1) : w = z := by
  have hf : (fun x : ℝ => (extend w x).1) = fun x => (extend z x).1 :=
    funext fun x => hp _
  have hae : extend w =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend z := by
    filter_upwards [hw.position_row u lambda v w, hz.position_row u lambda v' z] with x hx hy
    have hy' : HasDerivAt (fun t => (extend w t).1)
        (unitL2SynthesisEquiv u x*(extend z x).1+(extend z x).2) x := by
      rw [hf]
      exact hy
    have he := hx.unique hy'
    have h1 := congrFun hf x
    rw [h1] at he
    exact Prod.ext h1 (add_left_cancel he)
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae
  have he := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0:ℝ) ≠ 1) hae
    (continuous_extend w).continuousOn (continuous_extend z).continuousOn
  apply ContinuousMap.ext
  intro t
  simpa only [extend_coe] using he t.property

end NLS.MKdV
