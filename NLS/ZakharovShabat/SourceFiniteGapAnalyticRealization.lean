import NLS.ZakharovShabat.SourceFiniteGapTranslationLift
import NLS.ZakharovShabat.NormalizedSobolevSourceEvaluation
import NLS.ZakharovShabat.SourceFiniteGapSmoothRealization

/-! # Spatial real analyticity of the original real finite-gap source

The translation orbit has an analytic weighted lift because its finite
Fourier target is analytic and its canonical gap tail is fixed. Bounded
Sobolev evaluation identifies this lift with the original physical Fourier
sum. Thus the already constructed coefficient-preserving representatives
are real analytic at every spatial point, at every finite source exponent
strictly above one.
-/

noncomputable section
open Filter Topology Set
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original real finite-gap source has real normalized one-derivative coordinates. -/
theorem exists_sourceFiniteGap_oneDerivative_coordinates (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ ψ : CoeffPair p, IsRealType (CoeffPair.toMax p ψ) ∧
      normalizedWeightedSource sourceOneDerivativeWeight ψ = φ.val := by
  obtain ⟨ha,hb⟩ := sourceFiniteGap_mem_all_sobolev hp hp1 φ hf 1 zero_le_one
  let ψ : CoeffPair p := WithLp.toLp p
    (⟨fun n => (Weight.sobolev 1 n : ℂ)*φ.val.fst n, ha⟩,
     ⟨fun n => (Weight.sobolev 1 n : ℂ)*φ.val.snd n, hb⟩)
  refine ⟨ψ, ?_, ?_⟩
  · intro n
    change (Weight.sobolev 1 n : ℂ)*φ.val.snd n =
      conj ((Weight.sobolev 1 (-n) : ℂ)*φ.val.fst (-n))
    rw [Weight.sobolev_neg, map_mul, Complex.conj_ofReal]
    exact congrArg (fun z : ℂ => (Weight.sobolev 1 n : ℂ)*z) (φ.property n)
  · apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext n
    · change (normalizedWeightedSource sourceOneDerivativeWeight ψ).fst n = φ.val.fst n
      rw [normalizedWeightedSource_fst, sourceOneDerivativeWeight_double]
      exact mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero n)
    · change (normalizedWeightedSource sourceOneDerivativeWeight ψ).snd n = φ.val.snd n
      rw [normalizedWeightedSource_snd, sourceOneDerivativeWeight_double]
      exact mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero n)

/-- The original physical finite-gap pair is analytic along spatial translation at zero. -/
theorem analyticAt_sourceFiniteGapPhysicalPair_translate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (x : ℝ) :
    AnalyticAt ℝ (fun t : ℝ =>
      ((sourceFiniteGapPhysicalPair hp hp1 φ hf).1 (x+t),
       (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 (x+t))) 0 := by
  obtain ⟨ψ,hreal,hψ⟩ := exists_sourceFiniteGap_oneDerivative_coordinates hp hp1 φ hf
  have hfinite : (⟨normalizedWeightedSource sourceOneDerivativeWeight ψ,
      normalizedWeightedSource_realType sourceOneDerivativeWeight ψ hreal⟩ :
      realTypeSourceLocus p) ∈ sourceFiniteGapLocus hp hp1 := by
    have hf0 : {n : ℤ | canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0}.Finite := hf
    change {n : ℤ | canonicalPeriodicGap hp hp1
      (periodOnePotential (normalizedWeightedSource sourceOneDerivativeWeight ψ))
      (periodOnePotential_mem _) n ≠ 0}.Finite
    simpa only [hψ] using hf0
  obtain ⟨ξ,hξ,_,hdecode⟩ := exists_analyticAt_sourceFiniteGap_translationLift
    hp hp1 sourceOneDerivativeWeight ψ hreal hfinite
  simp only [hψ] at hdecode
  let a : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one hp hp1 φ hf).1⟩
  let b : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one hp hp1 φ hf).2⟩
  have hA : AnalyticAt ℝ (fun t => normalizedSobolevSourceEvaluation hp x (ξ t)) 0 :=
    ((normalizedSobolevSourceEvaluation hp x).restrictScalars ℝ).analyticAt _ |>.comp hξ
  apply hA.congr
  filter_upwards [hdecode] with t ht
  have ha : (normalizedSobolevSourceL1 hp (ξ t)).fst =
      Coeff.spatialTranslation (2*Real.pi) t a := by
    ext n
    rw [normalizedSobolevSourceL1_fst, ht, sourceSpatialTranslation_fst]
    rfl
  have hb : (normalizedSobolevSourceL1 hp (ξ t)).snd =
      Coeff.spatialTranslation (2*Real.pi) t b := by
    ext n
    rw [normalizedSobolevSourceL1_snd, ht, sourceSpatialTranslation_snd]
    rfl
  rw [normalizedSobolevSourceEvaluation_apply, ha, hb,
    Fourier.periodOneSynthesis_spatialTranslation, Fourier.periodOneSynthesis_spatialTranslation]
  rfl

/-- Both original coefficient-preserving physical representatives are spatially real analytic. -/
theorem analyticOnNhd_sourceFiniteGapPhysicalPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    AnalyticOnNhd ℝ (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 univ ∧
      AnalyticOnNhd ℝ (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 univ := by
  have hpair (x : ℝ) : AnalyticAt ℝ (fun y =>
      ((sourceFiniteGapPhysicalPair hp hp1 φ hf).1 y,
       (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 y)) x := by
    have h := analyticAt_sourceFiniteGapPhysicalPair_translate hp hp1 φ hf x
    have hs : AnalyticAt ℝ (fun y : ℝ => y-x) x := analyticAt_id.sub analyticAt_const
    have h' : AnalyticAt ℝ (fun t : ℝ =>
        ((sourceFiniteGapPhysicalPair hp hp1 φ hf).1 (x+t),
         (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 (x+t))) (x-x) := by
      simpa only [sub_self] using h
    have hh := h'.comp (f := fun y : ℝ => y-x) hs
    simpa only [Function.comp_def, ← add_sub_assoc, add_sub_cancel_left] using hh
  exact ⟨fun x _ => analyticAt_fst.comp (hpair x),
    fun x _ => analyticAt_snd.comp (hpair x)⟩

/-- The qualified finite-gap regularity assertion: real analytic periodic
functions represent every original source coefficient at every finite p>1. -/
theorem sourceFiniteGap_exists_analytic_representative (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ u v : ℝ → ℂ, AnalyticOnNhd ℝ u univ ∧ AnalyticOnNhd ℝ v univ ∧
      Function.Periodic u 1 ∧ Function.Periodic v 1 ∧
      ∀ n : ℤ, Fourier.periodOneCoefficient u n = φ.val.fst n ∧
        Fourier.periodOneCoefficient v n = φ.val.snd n := by
  obtain ⟨ha,hb⟩ := analyticOnNhd_sourceFiniteGapPhysicalPair hp hp1 φ hf
  obtain ⟨hu,hv⟩ := periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf
  exact ⟨_,_,ha,hb,hu,hv,periodOneCoefficient_sourceFiniteGapPhysicalPair hp hp1 φ hf⟩

end NLS.ZakharovShabat
