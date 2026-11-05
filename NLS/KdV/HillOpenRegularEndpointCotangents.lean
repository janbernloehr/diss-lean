import NLS.KdV.HillEndpointDirichletPrimitives
import NLS.KdV.HillEndpointAngleGerms
import NLS.KdV.HillPrimitiveCorrectionMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual regular correction at an open periodic terminal has a constructed
analytic physical germ with its cotangent in the genuine norming span. -/
theorem exists_hillRegularAbelianCorrection_open_endpoint_norming_cotangent
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ C : Coeff 2 → ℂ, ∃ c : ℂ,
      AnalyticAt ℂ C (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk) ∧
      ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
        SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
        (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
          c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk) := by
  obtain ⟨B,ε,e,b,_,hB,hε,_,hphysical,hBD⟩ :=
    exists_hillDirichletPrimitive_endpoint_norming_cotangent h0q h0r q n k hn hk hgap hlog
  have hsin := hphysical.mono (fun _ hp => hp.2.2.2.1)
  obtain ⟨a,_,hεD⟩ := hillDirichletAngleGerm_endpoint_norming_cotangent q k hk hgap hlog ε hε hsin
  let δ : ℂ := if k=n then 1 else 0
  let C : Coeff 2 → ℂ := fun p => B p-δ*(ε p-(Real.pi : ℂ))
  have hC : AnalyticAt ℂ C (SpectralWeight.one.toCoeff q.val) :=
    hB.sub (analyticAt_const.mul (hε.sub analyticAt_const))
  have hmatch := eventually_hillPrimitive_eq_regularCorrection_of_terminal q.val q.property.1 q.property.2
    n k hn hk hgap B ε (hphysical.mono (fun _ hp => ⟨hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩))
  refine ⟨C,b-δ*a,hC,?_,?_⟩
  · filter_upwards [hmatch] with p hp
    dsimp only [C,δ]
    rw [hp]
    ring
  · intro h heven
    have hd := hB.differentiableAt.hasFDerivAt.sub
      ((hε.differentiableAt.hasFDerivAt.sub_const (Real.pi : ℂ)).const_mul δ)
    change HasFDerivAt C _ (SpectralWeight.one.toCoeff q.val) at hd
    rw [hd.fderiv]
    simp only [sub_apply,smul_apply,smul_eq_mul]
    rw [hBD h heven,hεD h heven]
    ring

end NLS.KdV
