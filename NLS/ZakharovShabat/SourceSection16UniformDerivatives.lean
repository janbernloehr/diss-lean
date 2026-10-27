import NLS.ZakharovShabat.SourceGapWeightedEtaOriginalSequence
import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace
import NLS.ZakharovShabat.SourceAuxiliaryUniformGradient

/-! # Uniform derivatives of the three factors used in Section 16

The source's Cauchy estimate uses one neighborhood before every spectral
index. These bounds concern the actual normalization, beta correction,
and gap-weighted eta coordinates in the original source norm.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

private theorem uniform_scalar_gradient_bound {ι : Type*}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (F : ι → CoeffPair p → ℂ)
    (V : Set (CoeffPair p)) (hV : IsOpen V) (φ : CoeffPair p) (hφ : φ ∈ V)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) V) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ ψ ∈ V, ∀ i, ‖F i ψ‖ ≤ M) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ U, ∀ i,
        ‖fderiv ℂ (F i) ψ‖ ≤ C ∧
        ‖CoeffPair.conjugateGradient hp hq (fderiv ℂ (F i) ψ)‖ ≤ 2*C := by
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp hV φ hφ
  have hh : 0 < r/2 := by positivity
  refine ⟨ball φ (r/2),isOpen_ball,mem_ball_self hh,
    fun ψ hψ => hrsub (ball_subset_ball (by linarith) hψ),
    2*M/(r/2),by positivity,?_⟩
  intro ψ hψ i
  have hd : ‖fderiv ℂ (F i) ψ‖ ≤ 2*M/(r/2) := by
    apply norm_fderiv_le_of_ball_bound _ φ ψ (r/2) (r/2) M hh
    · simpa only [show r/2+r/2=r by ring] using (hF i).differentiableOn.mono hrsub
    · intro χ hχ
      apply hbound χ (hrsub ?_) i
      simpa only [show r/2+r/2=r by ring] using hχ
    · exact hψ
  exact ⟨hd,(CoeffPair.norm_conjugateGradient_le hp hq _).trans
    (mul_le_mul_of_nonneg_left hd (by norm_num))⟩

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One complex source neighborhood bounds every actual beta derivative and
its physical conjugate gradient, uniformly in the signed spectral index. -/
theorem betaCorrection_gradient_local_bound
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (hq : q ≠ ⊤) (φ : CoeffPair p) (hφ : φ ∈ B) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ B ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        ‖fderiv ℂ (sourceAngularBetaCorrection hp hp1 n s) ψ‖ ≤ C ∧
        ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceAngularBetaCorrection hp hp1 n s) ψ)‖ ≤ 2*C := by
  obtain ⟨V,hV,hφV,hVB,G,A,_,hA,hb⟩ := D.exists_local_uniform_betaCorrection_bound φ hφ
  obtain ⟨U,hU,hφU,hUV,C,hC,hd⟩ := uniform_scalar_gradient_bound hp hq
    (fun n => sourceAngularBetaCorrection hp hp1 n s) V hV φ hφV
    (fun n => (D.beta_series.analytic_correction n).mono hVB) A hA
    (fun ψ hψ => (hb ψ hψ).2)
  exact ⟨U,hU,hφU,hUV.trans hVB,C,hC,hd⟩

end SourceAngularEtaLocalCommonDomainData

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The gap-weighted eta coordinate has uniformly bounded derivatives on
one original source neighborhood, for either signed coordinate. -/
theorem gapWeighted_gradient_local_bound
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ W) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        ‖fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s σ) ψ‖ ≤ C ∧
        ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s σ) ψ)‖ ≤ 2*C := by
  obtain ⟨V,hV,hφV,hVW,M,hM,_,hb⟩ := H.gapWeighted_original_local_sequence φ hφ
  have hscalar (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
      ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ M := by
    rw [← (hb ψ hψ σ hσ).2 n]
    exact (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans (hb ψ hψ σ hσ).1
  obtain ⟨U,hU,hφU,hUV,C,hC,hd⟩ := uniform_scalar_gradient_bound hp hq
    (fun n => sourceGapWeightedEtaCoordinate hp hp1 n s σ) V hV φ hφV
    (fun n => (H.gapWeightedEta_original_analytic n σ).mono hVW) M hM hscalar
  exact ⟨U,hU,hφU,hUV.trans hVW,C,hC,hd⟩

end SourceLemma12_12Data

/-- Near every real source, one complex neighborhood bounds all normalized
action-root derivatives in source operator norm and physical gradient norm. -/
theorem sourceNormalizedActionRoot_gradient_local_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        ‖fderiv ℂ (sourceNormalizedActionRoot hp hp1 n) ψ‖ ≤ C ∧
        ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceNormalizedActionRoot hp hp1 n) ψ)‖ ≤ 2*C := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨V,hV,hφV,M,F,he,hb,_,_⟩ :=
    exists_local_sourceNormalizedActionRootDeviation_continuousMap (q := p) hp hp1 hp1 hp hhalf φ hreal
  obtain ⟨A,hA,hφA,ha,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ hreal
  have hM : 0 ≤ M := (norm_nonneg (F φ)).trans (hb φ hφV)
  have hscalar (ψ : CoeffPair p) (hψ : ψ ∈ V ∩ A) (n : ℤ) :
      ‖sourceNormalizedActionRoot hp hp1 n ψ‖ ≤ M+1 := by
    have hn := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (F ψ) n).trans (hb ψ hψ.1)
    rw [he ψ hψ.1 n] at hn
    change ‖sourceNormalizedActionRoot hp hp1 n ψ-1‖ ≤ M at hn
    calc
      _ = ‖(sourceNormalizedActionRoot hp hp1 n ψ-1)+1‖ := by rw [sub_add_cancel]
      _ ≤ ‖sourceNormalizedActionRoot hp hp1 n ψ-1‖+‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ M+1 := by simpa using add_le_add_right hn 1
  obtain ⟨U,hU,hφU,_,C,hC,hd⟩ := uniform_scalar_gradient_bound hp hq
    (sourceNormalizedActionRoot hp hp1) (V ∩ A) (hV.inter hA) φ ⟨hφV,hφA⟩
    (fun n => (ha n).mono inter_subset_right) (M+1) (by positivity) hscalar
  exact ⟨U,hU,hφU,C,hC,hd⟩

end NLS.ZakharovShabat
