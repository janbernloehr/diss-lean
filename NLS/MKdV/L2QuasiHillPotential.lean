import NLS.MKdV.QuasiHillAffineCoordinates
import NLS.ZakharovShabat.L2Discriminant
import NLS.ZakharovShabat.ContinuousPotentialL2Bound

/-! # The affine physical L2 coefficient of the rough quasi-Hill system

Only Lebesgue L2 classes occur. The representative identity is almost
everywhere, so no point values or endpoint traces of the rough profile
are chosen as hypotheses.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def intervalL2Diagonal : IntervalL2 →L[ℂ] IntervalPairL2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ IntervalL2 IntervalL2).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ IntervalL2).prod (ContinuousLinearMap.id ℂ IntervalL2))

def quasiHillAffineOffset : IntervalPairL2 :=
  continuousPotentialL2Class (ContinuousMap.const _ (-I/2,I/2))

def l2QuasiHillPotential (u : IntervalL2) (μ : ℂ) : IntervalPairL2 :=
  intervalL2Diagonal u+(μ-1) • quasiHillAffineOffset

theorem l2QuasiHillPotential_representative (u : IntervalL2) (μ : ℂ) :
    intervalL2Representative (l2QuasiHillPotential u μ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun x => quasiHillAffinePotential (u x) μ) := by
  filter_upwards [intervalL2Representative_add (intervalL2Diagonal u) ((μ-1) • quasiHillAffineOffset),
    intervalL2Representative_smul (μ-1) quasiHillAffineOffset,
    continuousPotentialL2Class_representative (ContinuousMap.const _ (-I/2,I/2))] with x ha hs hc
  rw [l2QuasiHillPotential,ha,hs]
  change (u x,u x)+(μ-1) • intervalL2Representative quasiHillAffineOffset x = _
  rw [show intervalL2Representative quasiHillAffineOffset x = (-I/2,I/2) from hc]
  apply Prod.ext <;> dsimp [quasiHillAffinePotential] <;> ring

theorem analyticOnNhd_l2QuasiHillPotential_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × IntervalL2 => l2QuasiHillPotential p.2 p.1) univ := by
  intro p _
  exact ((intervalL2Diagonal.analyticAt p.2).comp analyticAt_snd).add
    ((analyticAt_fst.sub analyticAt_const).smul analyticAt_const)

/-- The scalar physical class of a continuous profile. -/
def continuousQuasiHillL2 (u : Curve ℂ) : IntervalL2 :=
  (continuousPotentialL2Class (u.prodMk u)).ofLp.1

theorem continuousQuasiHillL2_representative (u : Curve ℂ) :
    continuousQuasiHillL2 u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend u := by
  exact (continuousPotentialL2Class_representative (u.prodMk u)).fun_comp Prod.fst

def quasiHillAffineCurve (u : Curve ℂ) (μ : ℂ) : Curve (ℂ × ℂ) :=
  ⟨fun t => quasiHillAffinePotential (u t) μ,by
    exact (u.continuous.sub continuous_const).prodMk (u.continuous.add continuous_const)⟩

theorem l2QuasiHillPotential_continuous (u : Curve ℂ) (μ : ℂ) :
    l2QuasiHillPotential (continuousQuasiHillL2 u) μ = continuousPotentialL2Class (quasiHillAffineCurve u μ) := by
  apply intervalL2Representative_injective
  filter_upwards [l2QuasiHillPotential_representative (continuousQuasiHillL2 u) μ,
    continuousQuasiHillL2_representative u,continuousPotentialL2Class_representative (quasiHillAffineCurve u μ)]
    with x hl hu hr
  rw [hl,hu,hr]
  rfl

/-- Density uses the first coordinate of continuous approximants to a
physical diagonal class, without requiring diagonal approximants. -/
theorem denseRange_continuousQuasiHillL2 : DenseRange continuousQuasiHillL2 := by
  intro u
  let l := continuousPotentialL2Filter (intervalL2Diagonal u)
  let : NeBot l := continuousPotentialL2Filter_neBot _
  have hp : Tendsto continuousPotentialL2Class l (𝓝 (intervalL2Diagonal u)) := tendsto_comap
  have hf : Continuous (fun p : IntervalPairL2 => p.ofLp.1) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ IntervalL2 IntervalL2).continuous.fst
  have ht : Tendsto (fun φ => (continuousPotentialL2Class φ).ofLp.1) l (𝓝 u) := by
    simpa only [Function.comp_def,intervalL2Diagonal,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,WithLp.prodContinuousLinearEquiv_symm_apply,
      WithLp.ofLp_toLp,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] using
      hf.continuousAt.tendsto.comp hp
  have he (φ : Curve (ℂ × ℂ)) :
      continuousQuasiHillL2 ((ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1) (ContinuousLinearMap.fst ℂ ℂ ℂ)) φ) =
        (continuousPotentialL2Class φ).ofLp.1 := by
    apply Lp.ext
    exact (continuousQuasiHillL2_representative _).trans
      ((continuousPotentialL2Class_representative φ).fun_comp Prod.fst).symm
  apply mem_closure_of_tendsto ht
  exact Filter.Eventually.of_forall (fun φ => ⟨_,he φ⟩)

end NLS.MKdV
