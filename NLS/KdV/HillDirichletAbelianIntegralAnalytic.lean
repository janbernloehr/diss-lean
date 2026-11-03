import NLS.KdV.HillAbelianOpenGapPrimitiveCharts
import NLS.KdV.HillDirichletAnalyticAngles

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillDirichletAbelianIntegral_analytic_open_gap_extension
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ B ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      ε (SpectralWeight.one.toCoeff q) = e ∧ e ∈ segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 k ≠ 0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im = 0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val)) =
            (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val)) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk ∧
        B (SpectralWeight.one.toCoeff p.val) = hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k
          (ε (SpectralWeight.one.toCoeff p.val)) ∧ (B (SpectralWeight.one.toCoeff p.val)).im = 0 := by
  obtain ⟨F,Ω,Z,W,hΩ,hconv,hangle,hZ,hqZ,hW,hqW,hF,_,hmatch⟩ :=
    exists_hillAbelianCosinePrimitive_joint_analytic_open_gap_chart q hq hr h0q h0r n k hn hk hgap
  obtain ⟨ε,e,hε,hε0,he,hterminal⟩ := exists_hillDirichlet_analytic_sheeted_angle q hq hr k hk hgap
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
  refine ⟨B,ε,e,hB,hε,hε0,he,?_⟩
  filter_upwards [hterminal,hW.mem_nhds hqW,hεΩ] with p hp hpW hpΩ
  have hBp : B (P p) = hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k (ε (P p)) :=
    (hmatch p hpW).2 _ hpΩ
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hBp,?_⟩
  have hreal : ε (P p) = ((ε (P p)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (show (ε (P p)).im = 0 from hp.2.1)
  rw [hBp,hreal]
  exact hillAbelianCosinePrimitive_im_eq_zero p.val p.property.1 p.property.2 n hn k hk _

end NLS.KdV
