import NLS.KdV.SingularDirichletRieszKernel
import NLS.KdV.SingularDirichletResolventFamily
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Analyticity of the actual continuous-output Dirichlet projection

The original fixed contour is integrated in the full H1 operator norm,
then composed with the physical inclusions defining the original operator.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletProjectionAnalyticH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletProjectionAnalyticH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletProjectionAnalyticBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletProjectionAnalyticBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

theorem analyticOnNhd_singularDirichletRieszToH1
    (V : Set (FourierLebesgueSpace (2:ℝ) (-1) 2)) (hV : IsOpen V)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : ∀ q ∈ V, sphere c r ⊆ singularDirichletResolventSet q) :
    AnalyticOnNhd ℂ (fun q => singularDirichletRieszToH1 q c r) V := by
  let D := {p : ℂ × FourierLebesgueSpace (2:ℝ) (-1) 2 |
    p.1 ∈ singularDirichletResolventSet p.2}
  have hD : IsOpen D := isOpen_singularDirichletJointResolvent.preimage continuous_swap
  let F := fun p : ℂ × FourierLebesgueSpace (2:ℝ) (-1) 2 =>
    -singularDirichletResolventToH1 p.2 p.1
  have hF : AnalyticOnNhd ℂ F D := by
    intro p hp
    exact ((analyticAt_singularDirichletResolventToH1_joint (p.2,p.1) hp).comp
      (f := fun x : ℂ × FourierLebesgueSpace (2:ℝ) (-1) 2 => (x.2,x.1))
      (analyticAt_snd.prod analyticAt_fst)).neg
  have hi := NLS.ComplexAnalysis.analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF
    c r hr hV (fun q hq z hz => hc q hq hz)
  intro q hq
  change AnalyticAt ℂ (fun a => (2*Real.pi*I:ℂ)⁻¹ •
    ∮ z in C(c,r), F (z,a)) q
  have hs : AnalyticAt ℂ
      (fun _ : FourierLebesgueSpace (2:ℝ) (-1) 2 => (2*Real.pi*I:ℂ)⁻¹) q := analyticAt_const
  exact hs.smul (hi q hq)

theorem analyticOnNhd_singularDirichletContinuousRieszProjection
    (V : Set (FourierLebesgueSpace (2:ℝ) (-1) 2)) (hV : IsOpen V)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : ∀ q ∈ V, sphere c r ⊆ singularDirichletResolventSet q) :
    AnalyticOnNhd ℂ (fun q => singularDirichletContinuousRieszProjection q c r) V := by
  intro q hq
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM
      (analyticOnNhd_singularDirichletRieszToH1 V hV c r hr hc q hq) analyticAt_const)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_singularDirichletRieszToH1_comp
    (L : E →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2)
    (V : Set E) (hV : IsOpen V) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : ∀ q ∈ V, sphere c r ⊆ singularDirichletResolventSet (L q)) :
    AnalyticOnNhd ℂ (fun q => singularDirichletRieszToH1 (L q) c r) V := by
  let J : ℂ × E → FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ := fun p => (L p.2,p.1)
  let D := {p : ℂ × E | p.1 ∈ singularDirichletResolventSet (L p.2)}
  have hJ : ∀ p, AnalyticAt ℂ J p := fun _ =>
    ((L.analyticAt _).comp analyticAt_snd).prod analyticAt_fst
  have hD : IsOpen D := isOpen_singularDirichletJointResolvent.preimage
    (L.continuous.comp continuous_snd |>.prodMk continuous_fst)
  let F := fun p : ℂ × E => -singularDirichletResolventToH1 (L p.2) p.1
  have hF : AnalyticOnNhd ℂ F D := by
    intro p hp
    exact ((analyticAt_singularDirichletResolventToH1_joint (J p) hp).comp
      (f := J) (hJ p)).neg
  have hi := NLS.ComplexAnalysis.analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF
    c r hr hV (fun q hq z hz => hc q hq hz)
  intro q hq
  change AnalyticAt ℂ (fun a => (2*Real.pi*I:ℂ)⁻¹ • ∮ z in C(c,r), F (z,a)) q
  have hs : AnalyticAt ℂ (fun _ : E => (2*Real.pi*I:ℂ)⁻¹) q := analyticAt_const
  exact hs.smul (hi q hq)

theorem analyticOnNhd_singularDirichletContinuousRieszProjection_comp
    (L : E →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2)
    (V : Set E) (hV : IsOpen V) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : ∀ q ∈ V, sphere c r ⊆ singularDirichletResolventSet (L q)) :
    AnalyticOnNhd ℂ (fun q => singularDirichletContinuousRieszProjection (L q) c r) V := by
  intro q hq
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM
      (analyticOnNhd_singularDirichletRieszToH1_comp L V hV c r hr hc q hq) analyticAt_const)

end NLS.KdV
