import NLS.KdV.HillInfiniteNormingSingle
import NLS.KdV.HillInfiniteEndpointCorrectionCotangent
import NLS.KdV.HillEndpointDirichletPrimitives
import NLS.KdV.HillEndpointAngleGerms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The full physical phase, including its own angle and its actual infinite
correction series, has a genuine convergent norming-span cotangent at an
all-periodic source. Only the target gap must be open. -/
theorem exists_hillFullPhysicalPhase_endpoint_cotangent
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ Θ ε : Coeff 2 → ℂ, ∃ c : ℕ → ℂ,
      AnalyticAt ℂ Θ (SpectralWeight.one.toCoeff q.val) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 n)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 n) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 n hn ∧
        Θ (SpectralWeight.one.toCoeff p.val)=hillSummedRegularAbelianCorrection
          p.val p.property.1 p.property.2 n hn+ε (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) ∧
      Summable (fun j : ℕ => ‖c j‖) ∧
      ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
        SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
        (fderiv ℂ Θ (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
          hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillInfiniteNormingGradient q c) := by
  obtain ⟨F,c,hF,hFphysical,hc,hFD⟩ :=
    exists_hillSummedRegularCorrection_endpoint_cotangent h0q h0r q n hn hterminal
  obtain ⟨B,ε,e,b,_,_,hε,_,hphysical,_⟩ :=
    exists_hillDirichletPrimitive_endpoint_norming_cotangent h0q h0r q n n hn hn hgap (hterminal n hn)
  obtain ⟨a,_,hεD⟩ := hillDirichletAngleGerm_endpoint_norming_cotangent q n hn hgap (hterminal n hn)
    ε hε (hphysical.mono (fun _ hp => hp.2.2.2.1))
  obtain ⟨d,hd,hdeq⟩ := exists_hillInfiniteNormingGradient_add_term h0q h0r q c hc (n-1) a
  have hni : n-1+1=n := by omega
  simp only [hni] at hdeq
  let Θ : Coeff 2 → ℂ := fun p => F p+ε p-(Real.pi : ℂ)
  have hΘ : AnalyticAt ℂ Θ (SpectralWeight.one.toCoeff q.val) := (hF.add hε).sub analyticAt_const
  refine ⟨Θ,ε,d,hΘ,hε,?_,hd,?_⟩
  · filter_upwards [hFphysical,hphysical] with p hpF hpε
    refine ⟨hpε.1,hpε.2.1,hpε.2.2.1,hpε.2.2.2.1,?_⟩
    dsimp only [Θ]
    rw [hpF]
  · intro h heven
    have hDΘ := (hF.differentiableAt.hasFDerivAt.add hε.differentiableAt.hasFDerivAt).sub_const (Real.pi : ℂ)
    change HasFDerivAt Θ _ (SpectralWeight.one.toCoeff q.val) at hDΘ
    rw [hDΘ.fderiv,add_apply,hFD h heven,hεD h heven,hdeq,map_add,map_smul,smul_eq_mul]

end NLS.KdV
