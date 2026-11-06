import NLS.KdV.HillIsospectralCosinePrimitives
import NLS.ComplexAnalysis.MovingSpectralParameter
import NLS.KdV.HillCharacteristicAngle

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillDirichletAbelianIntegral_characteristic_open_gap_extension
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ B d μ S ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ d (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ μ (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ S (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      d (SpectralWeight.one.toCoeff q)=(hillRealGapHalfLength q hq hr k : ℂ) ∧
      μ (SpectralWeight.one.toCoeff q)=(hillDirichletEnergy q hq hr k hk : ℂ) ∧
      S (SpectralWeight.one.toCoeff q)=hillDirichletGapSine q hq hr k hk ∧
      ε (SpectralWeight.one.toCoeff q) = e ∧ e ∈ segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e=
        (hillDirichletEnergy q hq hr k hk : ℂ) ∧
      Complex.sin e=hillDirichletGapSine q hq hr k hk ∧
      (∀ᶠ p : Coeff 2 in 𝓝 (SpectralWeight.one.toCoeff q),
        d p≠0 ∧ (d p)^2=hillLocalGapSquare q hq hr k p/4 ∧
        hillL2DirichletCharacteristic p (μ p)=0 ∧
        cosineGapPoint (hillLocalGapMidpoint q hq hr k p) (d p) (ε p)=μ p ∧
        Complex.sin (ε p)=S p ∧
        S p=I*hillDirichletSheetRoot p (μ p)/(d p*hillLocalDeflatedComplexRoot q hq hr k (μ p,p))) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 k ≠ 0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im = 0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val)) =
            (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val)) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk ∧
        B (SpectralWeight.one.toCoeff p.val) = hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k
          (ε (SpectralWeight.one.toCoeff p.val)) ∧ (B (SpectralWeight.one.toCoeff p.val)).im = 0) ∧
      ∀ h : Coeff 2,
        (∀ energy : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b energy) (SpectralWeight.one.toCoeff q)) h=0) →
        (fderiv ℂ B (SpectralWeight.one.toCoeff q)) h=
          hillAbelianCosineDifferential q hq hr n hn k e*((fderiv ℂ ε (SpectralWeight.one.toCoeff q)) h) := by
  obtain ⟨F,Ω,Z,W,hΩ,hconv,hangle,hZ,hqZ,hW,hqW,hF,_,hmatch,hD,hflat⟩ :=
    exists_hillAbelianCosinePrimitive_joint_isospectral_open_gap_chart q hq hr h0q h0r n k hn hk hgap
  obtain ⟨d,μ,S,ε,e,hd,hμ,hS,hε,hd0,hμ0,hS0,hε0,he,hpoint,hsin,hcomplex,hterminal⟩ :=
    exists_hillDirichlet_analytic_characteristic_angle q hq hr k hk hgap
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let B : Coeff 2 → ℂ := fun p => F (ε p,p)
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) :=
    (hF (ε (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ⟨by rw [hε0];exact hangle he,hqZ⟩).comp
      (f := fun p : Coeff 2 => (ε p,p)) (hε.prod analyticAt_id)
  have hεΩ : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0, ε (P p) ∈ Ω := by
    have hc : ContinuousAt (fun p : RealPeriodOneHillPotential => ε (P p)) p0 :=
      ContinuousAt.comp (f := P) hε.continuousAt hP.continuousAt
    have hbaseΩ : ε (P p0) ∈ Ω := by
      change ε (SpectralWeight.one.toCoeff q) ∈ Ω
      rw [hε0]
      exact hangle he
    exact hc.preimage_mem_nhds (hΩ.mem_nhds hbaseΩ)
  refine ⟨B,d,μ,S,ε,e,hB,hd,hμ,hS,hε,hd0,hμ0,hS0,hε0,he,hpoint,hsin,hcomplex,?_,?_⟩
  · filter_upwards [hterminal,hW.mem_nhds hqW,hεΩ] with p hp hpW hpΩ
    have hBp : B (P p) = hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k (ε (P p)) :=
      (hmatch p hpW).2 _ hpΩ
    refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hBp,?_⟩
    have hreal : ε (P p) = ((ε (P p)).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using (show (ε (P p)).im = 0 from hp.2.1)
    rw [hBp,hreal]
    exact hillAbelianCosinePrimitive_im_eq_zero p.val p.property.1 p.property.2 n hn k hk _

  · intro h hiso
    have heΩ : ε (SpectralWeight.one.toCoeff q)∈Ω := by
      rw [hε0]
      exact hangle he
    change (fderiv ℂ (fun p : Coeff 2 => F (ε p,p)) (SpectralWeight.one.toCoeff q)) h=_
    rw [fderiv_moving_spectral_parameter F ε (SpectralWeight.one.toCoeff q)
      (hF (ε (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ⟨heΩ,hqZ⟩).differentiableAt hε.differentiableAt]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [hflat h hiso _ heΩ,(hD _ heΩ).deriv,zero_add,hε0]

end NLS.KdV
