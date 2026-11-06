import NLS.ZakharovShabat.SourceWeightedEtaComplexAnalytic
import NLS.SequenceSpaces.AnalyticRootPhaseSymbol

/-! # Native bounded analytic normalization of the ACTUAL eta coordinate

The original principal root and original angular correction give bounded
analytic reciprocal symbols near EVERY real source. Both actual signs
share ONE complex neighborhood and uniform native bounds. No phase or
root branch is replaced by an amplitude or formal asymptotic value.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

def sourceEtaNormalizationSymbol (hp : p≠⊤) (hp1 : 1<p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (sign : ℂ) : CoeffPair p → Coeff ⊤ :=
  Coeff.rootPhaseSymbol (fun ψ n => sourceNormalizedActionRoot hp hp1 n ψ)
    (fun ψ n => sourceAngularBetaCorrection hp hp1 n s ψ) sign

def sourceEtaNormalizationInverseSymbol (hp : p≠⊤) (hp1 : 1<p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (sign : ℂ) : CoeffPair p → Coeff ⊤ :=
  Coeff.rootPhaseInverseSymbol (fun ψ n => sourceNormalizedActionRoot hp hp1 n ψ)
    (fun ψ n => sourceAngularBetaCorrection hp hp1 n s ψ) sign

namespace SourceBirkhoffMapComplexData
variable {hp : p≠⊤} {hp1 : 1<p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- EVERY actual real source has ONE native complex analytic bounded
normalization and reciprocal for BOTH eta signs and EVERY index. -/
theorem exists_local_sourceEtaNormalization_symbols
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val∈U ∧ U⊆W ∧
      ∃ C : ℝ, 0<C ∧ ∀ sign : ℂ, sign=1 ∨ sign=-1 →
        AnalyticOnNhd ℂ (sourceEtaNormalizationSymbol hp hp1 s sign) U ∧
        AnalyticOnNhd ℂ (sourceEtaNormalizationInverseSymbol hp hp1 s sign) U ∧ ∀ ψ∈U,
          ‖sourceEtaNormalizationSymbol hp hp1 s sign ψ‖≤C ∧
          ‖sourceEtaNormalizationInverseSymbol hp hp1 s sign ψ‖≤C ∧ ∀ n,
            sourceNormalizedActionRoot hp hp1 n ψ≠0 ∧
            sourceEtaNormalizationSymbol hp hp1 s sign ψ n=
              (sourceNormalizedActionRoot hp hp1 n ψ)⁻¹*exp (-sign*I*sourceAngularBetaCorrection hp hp1 n s ψ) ∧
            sourceEtaNormalizationInverseSymbol hp hp1 s sign ψ n=
              sourceNormalizedActionRoot hp hp1 n ψ*exp (sign*I*sourceAngularBetaCorrection hp hp1 n s ψ) ∧
            sourceEtaNormalizationSymbol hp hp1 s sign ψ n*sourceEtaNormalizationInverseSymbol hp hp1 s sign ψ n=1 := by
  have hhalf : ENNReal.ofReal (p.toReal/2)≤p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨Uf,hUf,hφf,M,F,hF,hFb,_hFc,_hFd⟩ :=
    exists_local_sourceNormalizedActionRootDeviation_continuousMap (q := p) hp hp1 hp1 hp hhalf φ.val φ.property
  have hM : 0≤M := (norm_nonneg (F φ.val)).trans (hFb φ.val hφf)
  obtain ⟨Ur,hUr,hφr,hlower⟩ := exists_local_sourceNormalizedActionRoot_uniform_lower hp hp1 φ
  obtain ⟨Ua,hUa,hφa,hra,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ.val φ.property
  obtain ⟨Ub,hUb,hφb,_hUb,G,A,_hG,hA,hβ⟩ := D.angular.exists_local_uniform_betaCorrection_bound
    φ.val (D.source_subset (D.real_subset φ.property))
  let U := ((Uf∩Ur)∩(Ua∩Ub))∩W
  have hU : IsOpen U := ((hUf.inter hUr).inter (hUa.inter hUb)).inter D.source_open
  have hφU : φ.val∈U := ⟨⟨⟨hφf,hφr⟩,hφa,hφb⟩,D.real_subset φ.property⟩
  have hbound (ψ : CoeffPair p) (hψ : ψ∈U) (n : ℤ) :
      sourceNormalizedActionRoot hp hp1 n ψ≠0 ∧ ‖sourceNormalizedActionRoot hp hp1 n ψ‖≤M+1 ∧
        ‖(sourceNormalizedActionRoot hp hp1 n ψ)⁻¹‖≤2 ∧ ‖sourceAngularBetaCorrection hp hp1 n s ψ‖≤A := by
    have hlow := hlower ψ hψ.1.1.2 n
    refine ⟨norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) hlow.1),?_,hlow.2,(hβ ψ hψ.1.2.2).2 n⟩
    have hn := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (F ψ) n).trans (hFb ψ hψ.1.1.1)
    rw [hF ψ hψ.1.1.1 n,sourceNormalizedActionRootDeviation] at hn
    calc
      _ ≤ ‖sourceNormalizedActionRoot hp hp1 n ψ-1‖+‖(1 : ℂ)‖ := norm_le_norm_sub_add _ _
      _ ≤ M+1 := by rw [norm_one]; linarith
  obtain ⟨C,hC,hsymbol⟩ := Coeff.analytic_rootPhase_symbols U hU
    (fun ψ n => sourceNormalizedActionRoot hp hp1 n ψ)
    (fun ψ n => sourceAngularBetaCorrection hp hp1 n s ψ)
    (fun n ψ hψ => hra n ψ hψ.1.2.1)
    (fun n ψ hψ => D.angular.beta_series.analytic_correction n ψ (D.source_subset hψ.2))
    (M+1) 2 A (by positivity) (by norm_num) hA hbound
  refine ⟨U,hU,hφU,inter_subset_right,C,hC,?_⟩
  intro sign hsign
  obtain ⟨hσ,hν,hd⟩ := hsymbol sign hsign
  refine ⟨hσ,hν,?_⟩
  intro ψ hψ
  exact ⟨(hd ψ hψ).1,(hd ψ hψ).2.1,fun n => ⟨(hbound ψ hψ n).1,(hd ψ hψ).2.2 n⟩⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
