import NLS.KdV.HillHminusOneCanonicalActions
import NLS.KdV.HillMiuraActionCotangentIntegrand
import NLS.ZakharovShabat.SourceIndexedHigherActionGradient

/-! The ACTUAL canonical Hill action has a genuine full H-minus-one
source-dual contour gradient at every real potential, including closed
gaps. The coefficient -2/pi comes from twice the original level-two
action and its verified polynomial integration by parts. -/
noncomputable section
open Set Metric Filter Topology Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem HillHminusMiuraActionBall.exists_action_gradient_circle
    (B : HillHminusMiuraActionBall) (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
      sphere a R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal (B.lift q)) ∧
      ∀ h : PeriodOneHminusOne,
        (fderiv ℂ (hillHminusCanonicalAction n) q) h=
          -(2*(Real.pi : ℂ)⁻¹)*(∮ z in C(a,R), z *
            hillHminusDiscriminantCotangent (z^2-(B.shift : ℂ)) q h /
              sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal (B.lift q)) z) := by
  let v : PeriodOneHminusOne → CoeffPair 2 := fun p => hillMiuraDiagonal (B.lift p)
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hq hreal⟩
  have hφ : IsRealType (CoeffPair.toMax 2 (v q)) := (hillMiuraRealSource u).property
  obtain ⟨a,R,hR,hcircle,hlevels⟩ :=
    exists_sourceIndexedHigherAction_gradient_circle (by simp) (by norm_num) (n : ℤ) (v q) hφ
  have hv : AnalyticAt ℂ v q := (hillMiuraDiagonal.analyticAt _).comp (B.lift_analytic q hq)
  have hJ := (hlevels 1).1
  have hd : DifferentiableAt ℂ
      (fun p => sourceIndexedHigherAction (by simp) (by norm_num) (n : ℤ) 1 (v p)) q :=
    (hJ.comp hv).differentiableAt
  have hc := (hJ.differentiableAt.hasFDerivAt.comp q hv.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ (fun p => sourceIndexedHigherAction (by simp) (by norm_num) (n : ℤ) 1 (v p)) q=_ at hc
  have he : hillHminusCanonicalAction n =ᶠ[𝓝 q]
      (fun p => 2*sourceIndexedHigherAction (by simp) (by norm_num) (n : ℤ) 1 (v p)) := by
    filter_upwards [B.source_open.mem_nhds hq] with p hp
    exact B.canonical_action_eq n p hp
  refine ⟨a,R,hR,hcircle,?_⟩
  intro h
  have hp : (fderiv ℂ (hillHminusCanonicalAction n) q) h=
      2*((fderiv ℂ (sourceIndexedHigherAction (by simp) (by norm_num) (n : ℤ) 1) (v q))
        ((fderiv ℂ v q) h)) := by
    rw [he.fderiv_eq,fderiv_const_mul hd (2:ℂ),hc]
    simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply]
  rw [hp,(hlevels 1).2]
  simp only [pow_one]
  have hi : (∮ z in C(a,R), z *
      (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) z) (v q))
        ((fderiv ℂ v q) h) / sourceCanonicalRoot (by simp) (by norm_num) (v q) z)=
      ∮ z in C(a,R), z * hillHminusDiscriminantCotangent (z^2-(B.shift : ℂ)) q h /
        sourceCanonicalRoot (by simp) (by norm_num) (v q) z := by
    apply circleIntegral.integral_congr hR.le
    intro z _
    dsimp only
    rw [fderiv_liftedMiuraDiscriminant_eq_native B.source B.source_open B.lift B.lift_analytic
      (B.shift : ℂ) B.image q hq z h]
  rw [hi]
  ring

theorem exists_hillHminusCanonicalAction_cotangent_contour
    (q : PeriodOneHminusOne) (hreal : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ u : Coeff 2, ∃ c : ℂ,
      periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
        CircleIntegrable (hillMiuraActionCotangentIntegrand q u c) a R ∧
        fderiv ℂ (hillHminusCanonicalAction n) q=
          -(2*(Real.pi : ℂ)⁻¹) • (∮ z in C(a,R), hillMiuraActionCotangentIntegrand q u c z) := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraActionBall q hreal
  obtain ⟨a,R,hR,hcircle,hpoint⟩ := B.exists_action_gradient_circle n q hB hreal
  have hi := circleIntegrable_hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift : ℂ) a R hR.le hcircle
  refine ⟨B.lift q,B.shift,B.image q hB,a,R,hR,hi,?_⟩
  ext h
  rw [hpoint h]
  have heval := NLS.ComplexAnalysis.map_circleIntegral (ContinuousLinearMap.apply ℂ ℂ h) hi
  change (∮ z in C(a,R), hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift : ℂ) z) h=
    ∮ z in C(a,R), (hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift : ℂ) z) h at heval
  simp only [smul_apply,smul_eq_mul]
  rw [heval]
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro z _
  dsimp only [hillMiuraActionCotangentIntegrand]
  simp only [smul_apply,smul_eq_mul]
  ring

end NLS.KdV
