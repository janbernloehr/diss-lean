import NLS.MKdV.QuasiHillPeriodicBasepoint
import NLS.MKdV.QuasiHillDirichletCharacteristic
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! # Actual release of a parabolic Dirichlet terminal by spatial translation

The translated characteristic equals minus the parabolic lower entry
times the square of the original Dirichlet column. A nontrivial lower
entry therefore removes that terminal for every sufficiently small
positive shift. Identifying the open-gap endpoint hypotheses is separate.
-/
noncomputable section
open Set Complex Matrix Filter Topology NLS.LinearVolterra
namespace NLS.MKdV

private theorem upper_right_of_parabolic_intertwine
    (A X : Matrix (Fin 2) (Fin 2) ℂ) (ε c : ℂ)
    (hX : X.det = 1) (h : A*X = X*!![ε,0;c,ε]) : A 0 1 = -c*(X 0 1)^2 := by
  have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp [Matrix.mul_apply,Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hX
  linear_combination -(X 0 1)*h0+(X 0 0)*h1-(A 0 1)*hX

theorem quasiHillDirichletCharacteristic_translate_parabolic (U : C(ℝ,ℂ)) (hp : Function.Periodic U 1)
    (z : ℂ) (hz : z ≠ 0) (ε c : ℂ)
    (hpar : quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve U) (z^2) 1 = !![ε,0;c,ε])
    (τ : Icc (0:ℝ) 1) :
    quasiHillDirichletCharacteristic (periodicScalarProfileUnitCurve (periodicScalarProfileTranslate U τ)) (z^2) =
      -c*((quasiHillSolution (periodicScalarProfileUnitCurve U) (z^2) (0,1) τ).1)^2 := by
  have h := quasiHillMonodromy_translate_intertwine U hp z hz τ
  rw [periodicQuasiHillFundamentalMatrix_on_unit U z hz τ,hpar] at h
  exact upper_right_of_parabolic_intertwine _ _ ε c
    (det_quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve U) (z^2) τ) h

theorem quasiHillDirichletPosition_eventually_ne_zero (U : Curve ℂ) (E : ℂ) :
    ∀ᶠ τ in 𝓝[≠] (0:ℝ),(quasiHillSolution U E (0,1) τ).1 ≠ 0 := by
  have hd := hasDerivAt_fst_quasiHillSolution U E (0,1) ⟨0,by norm_num⟩
  have hd' : HasDerivAt (fun τ : ℝ => (quasiHillSolution U E (0,1) τ).1) (1:ℂ) 0 := by
    simpa only [quasiHillSolution_zero,mul_zero,zero_add] using hd
  exact hd'.eventually_ne (by norm_num)

theorem quasiHillDirichletCharacteristic_translate_parabolic_eventually_ne_zero
    (U : C(ℝ,ℂ)) (hp : Function.Periodic U 1) (z : ℂ) (hz : z ≠ 0) (ε c : ℂ) (hc : c ≠ 0)
    (hpar : quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve U) (z^2) 1 = !![ε,0;c,ε]) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ),
      quasiHillDirichletCharacteristic (periodicScalarProfileUnitCurve (periodicScalarProfileTranslate U τ)) (z^2) ≠ 0 := by
  have hpos : ∀ᶠ τ in 𝓝[>] (0:ℝ),0 < τ := self_mem_nhdsWithin
  have hupper0 : ∀ᶠ τ in 𝓝 (0:ℝ),τ < 1 := Iio_mem_nhds (by norm_num)
  have hupper : ∀ᶠ τ in 𝓝[>] (0:ℝ),τ < 1 := hupper0.filter_mono nhdsWithin_le_nhds
  have hstate := (quasiHillDirichletPosition_eventually_ne_zero (periodicScalarProfileUnitCurve U) (z^2)).filter_mono (nhdsGT_le_nhdsNE 0)
  filter_upwards [hpos,hupper,hstate] with τ hτ hτ1 hs
  rw [quasiHillDirichletCharacteristic_translate_parabolic U hp z hz ε c hpar ⟨τ,hτ.le,hτ1.le⟩]
  exact mul_ne_zero (neg_ne_zero.mpr hc) (pow_ne_zero 2 hs)

end NLS.MKdV
