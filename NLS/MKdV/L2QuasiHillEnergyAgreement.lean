import NLS.MKdV.QuasiHillL2Sobolev
import NLS.MKdV.L2QuasiHillDiscriminant
import NLS.MKdV.SobolevMiuraPhysicalClass

/-! # Agreement of the two energy-affine rough Hill IVP realizations

Both fixed state changes recover the same actual continuous-profile IVP.
Density in the original L2 norm identifies their entire solution curves,
with the original scalar initial data and no zero-energy exception.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.Fourier NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

theorem unitL2Synthesis_scalarInclusion_eq_continuousQuasiHillL2 (a : ScalarDomain 2) :
    unitL2SynthesisEquiv (scalarInclusion a) = continuousQuasiHillL2 (periodOneMiuraCurve a) := by
  apply Lp.ext
  filter_upwards [unitL2Synthesis_scalarInclusion_representative a,
    continuousQuasiHillL2_representative (periodOneMiuraCurve a),
    ae_restrict_mem measurableSet_Ioc] with s hs ht hx
  rw [hs,ht]
  rw [show s = ((⟨s,⟨hx.1.le,hx.2⟩⟩ : Icc (0 : ℝ) 1) : ℝ) from rfl,
    extend_coe,periodOneMiuraCurve_apply]

/-- Equality of the full state curves, rather than only traces or zeros. -/
theorem quasiHillL2SolutionCurve_eq_physical (u : Coeff 2) (mu : ℂ) (v : ℂ × ℂ) :
    quasiHillL2SolutionCurve u mu v = l2QuasiHillSolution (unitL2SynthesisEquiv u) mu v := by
  have hL : Continuous (fun p : Coeff 2 => quasiHillL2SolutionCurve p mu v) :=
    (analyticOnNhd_quasiHillL2SolutionCurve_joint v).continuous.comp
      (f := fun p : Coeff 2 => (mu,p)) (continuous_const.prodMk continuous_id)
  have hR : Continuous (fun p : Coeff 2 => l2QuasiHillSolution (unitL2SynthesisEquiv p) mu v) :=
    (analyticOnNhd_l2QuasiHillSolution_joint v).continuous.comp
      (f := fun p : Coeff 2 => (mu,unitL2SynthesisEquiv p))
      (continuous_const.prodMk unitL2SynthesisEquiv.continuous)
  have he := (scalarInclusion_denseRange (p := 2) (by simp)).equalizer hL hR (by
    funext a
    apply ContinuousMap.ext
    intro t
    dsimp only [Function.comp_def]
    rw [quasiHillL2SolutionCurve_scalarInclusion,
      unitL2Synthesis_scalarInclusion_eq_continuousQuasiHillL2,l2QuasiHillSolution_continuous])
  exact congrFun he u

theorem quasiHillL2Dirichlet_eq_physical (u : Coeff 2) (mu : ℂ) :
    quasiHillL2Dirichlet u mu =
      (l2QuasiHillSolution (unitL2SynthesisEquiv u) mu (0,1)
        ⟨1,by constructor <;> norm_num⟩).1 := by
  rw [quasiHillL2Dirichlet,quasiHillL2SolutionCurve_eq_physical]

end NLS.MKdV
