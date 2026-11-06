import NLS.ComplexAnalysis.RealLineGermDerivative
import NLS.KdV.HillRealSourceDecomposition
import NLS.KdV.HillDirichletNormingData

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

private theorem real_direction_derivative
    (F G : WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q)
    (heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential), F p.val=G p.val)
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff h)) :
    (fderiv ℂ F q) h=(fderiv ℂ G q) h := by
  have hevenLine (t : ℝ) : SpectralWeight.one.toCoeff (q+(t : ℂ) • h)∈Coeff.paritySubspace 0 := by
    simpa only [map_add,map_smul] using (Coeff.paritySubspace (p := 2) 0).add_mem hq
      ((Coeff.paritySubspace 0).smul_mem (t : ℂ) heven)
  have hrealLine (t : ℝ) : IsRealHillPotential (SpectralWeight.one.toCoeff (q+(t : ℂ) • h)) := by
    intro k
    simp only [SpectralWeight.toCoeff_apply,WeightedCoeff.add_val,WeightedCoeff.smul_val]
    have hqr : q.val (-k)=conj (q.val k) := by simpa only [SpectralWeight.toCoeff_apply] using hr k
    have hhr : h.val (-k)=conj (h.val k) := by simpa only [SpectralWeight.toCoeff_apply] using hreal k
    rw [hqr,hhr,map_add,map_mul,conj_ofReal]
  let Q : ℝ → RealPeriodOneHillPotential := fun t => ⟨q+(t : ℂ) • h,hevenLine t,hrealLine t⟩
  have hQc : Continuous Q := by
    apply Continuous.subtype_mk
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hQ0 : Q 0=(⟨q,hq,hr⟩ : RealPeriodOneHillPotential) := by
    apply Subtype.ext
    simp only [Q,ofReal_zero,zero_smul,add_zero]
  have ht : Tendsto Q (𝓝 0) (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) := by
    rw [← hQ0]
    exact hQc.continuousAt
  apply fderiv_eq_of_eventuallyEq_real_affine_line F G q h hF hG
  exact ht.eventually heq

/-- A holomorphic germ agreeing on the actual real period-one Hill
space has intrinsic complex derivatives in every even direction. -/
theorem hillPhysicalGerm_fderiv_eq_of_eventuallyEq
    (F G : WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q)
    (heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential), F p.val=G p.val)
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0) :
    (fderiv ℂ F q) h=(fderiv ℂ G q) h := by
  obtain ⟨a,b,hae,har,hbe,hbr,hsplit⟩ := exists_hillRealPeriodOne_complex_decomposition h heven
  rw [hsplit,map_add,map_add,map_smul,map_smul,
    real_direction_derivative q hq hr F G hF hG heq a hae har,
    real_direction_derivative q hq hr F G hF hG heq b hbe hbr]

/-- Physical matching determines the source derivative independently
of the coefficient extension, on the actual period-one tangent space. -/
theorem hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq
    (F G : Coeff 2 → ℂ)
    (hF : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q))
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q))
    (heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      F (SpectralWeight.one.toCoeff p.val)=G (SpectralWeight.one.toCoeff p.val))
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0) :
    (fderiv ℂ F (SpectralWeight.one.toCoeff q)) (SpectralWeight.one.toCoeff h)=
      (fderiv ℂ G (SpectralWeight.one.toCoeff q)) (SpectralWeight.one.toCoeff h) := by
  have hf := hF.differentiableAt.hasFDerivAt.comp q (SpectralWeight.one.toCoeff.hasFDerivAt)
  have hg := hG.differentiableAt.hasFDerivAt.comp q (SpectralWeight.one.toCoeff.hasFDerivAt)
  have ht := hillPhysicalGerm_fderiv_eq_of_eventuallyEq q hq hr
    (fun p => F (SpectralWeight.one.toCoeff p)) (fun p => G (SpectralWeight.one.toCoeff p))
    (hF.comp (SpectralWeight.one.toCoeff.analyticAt q)) (hG.comp (SpectralWeight.one.toCoeff.analyticAt q)) heq h heven
  change (fderiv ℂ (F ∘ SpectralWeight.one.toCoeff) q) h=(fderiv ℂ (G ∘ SpectralWeight.one.toCoeff) q) h at ht
  rw [hf.fderiv,hg.fderiv] at ht
  exact ht

end NLS.KdV
