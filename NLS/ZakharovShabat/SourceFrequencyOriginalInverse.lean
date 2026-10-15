import NLS.ZakharovShabat.SourceFrequencyOriginalAsymptotic
import NLS.ZakharovShabat.SourceFrequencyGenericLocalInverse
import NLS.ZakharovShabat.SourceFrequencyReality

/-!
# Corollary 18.2 for the same original action frequency

All four inverse and Fredholm assertions are derived from the very map
carrying Theorem 18.1's mixed asymptotic, on its unchanged connected domain.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {U : Set (Coeff q)} {F : Coeff q → Coeff q}
namespace SourceOriginalFrequencyData

/-- The action frequency has the exact first Taylor coefficient -2Id. -/
theorem derivative_zero (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p) :
    fderiv ℂ F 0 = (-2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q) := by
  obtain ⟨Wa,sa,A,P,hs,hrec⟩ := E.spectral
  exact sourceFrequency_fderiv_zero A hs D.complex hp2.le F
    (E.analytic 0 E.zero_mem).differentiableAt E.map_zero hrec

/-- The same mixed-asymptotic map has compact corrected derivative everywhere. -/
theorem compact_derivative (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p)
    (b : Coeff q) (hb : b ∈ U) :
    IsCompactOperator (fderiv ℂ F b+(2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q)) := by
  obtain ⟨r,hr,hr1,hrq,hpr⟩ := Coeff.exists_strict_refined_actionExponent (q := q) hp hp2
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨H,hH,_,he⟩ := E.refined r hr hr1 hpr
  exact Coeff.isCompactOperator_actionCorrection_fderiv (Coeff.doublingExponent_ne_top hp)
    hrq U E.isOpen F H E.analytic hH he b hb

/-- Fredholm index zero is expressed by equal finite kernel and cokernel dimensions. -/
theorem fredholm (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p)
    (b : Coeff q) (hb : b ∈ U) :
    (fderiv ℂ F b).IsFredholm ∧ Module.finrank ℂ (fderiv ℂ F b).ker =
      Module.finrank ℂ (Coeff q ⧸ (fderiv ℂ F b).range) := by
  apply CompactSpectrum.fredholm_index_zero_of_compact_sub_smul
    (fderiv ℂ F b) (c := -2) (by norm_num)
  rw [neg_smul,sub_neg_eq_add]
  convert E.compact_derivative hp2 b hb using 1
  · congr 1
  · ext x n
    rfl

/-- Both inverse identities hold at zero, with the exact inverse derivative. -/
theorem local_inverse (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p) :
    ∃ G : Coeff q → Coeff q, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      (∀ᶠ b in 𝓝 (0 : Coeff q), G (F b) = b) ∧
      (∀ᶠ c in 𝓝 (0 : Coeff q), F (G c) = c) ∧
      fderiv ℂ G 0 = (-2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Coeff q) :=
  NLS.ComplexAnalysis.exists_analytic_localInverse_of_scalar_derivative
    F (E.analytic 0 E.zero_mem) E.map_zero (-2) (by norm_num) (E.derivative_zero hp2)

/-- An open dense subset of the same domain has genuine analytic local inverses. -/
theorem generic_local_inverse (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p) :
    ∃ O : Set (Coeff q), IsOpen O ∧ O ⊆ U ∧ U ⊆ closure O ∧
      ∀ b ∈ O, IsUnit (fderiv ℂ F b) ∧
        ∃ G : Coeff q → Coeff q, AnalyticAt ℂ G (F b) ∧ G (F b) = b ∧
          (∀ᶠ c in 𝓝 b, G (F c) = c) ∧ (∀ᶠ z in 𝓝 (F b), F (G z) = z) ∧
          fderiv ℂ G (F b) = Ring.inverse (fderiv ℂ F b) := by
  have hu0 : IsUnit (fderiv ℂ F 0) := by
    rw [E.derivative_zero hp2,ContinuousLinearMap.isUnit_iff_bijective]
    exact (LinearEquiv.smulOfNeZero ℂ (Coeff q) (-2) (by norm_num)).bijective
  have hcompact : ∀ b ∈ U,
      IsCompactOperator (fderiv ℂ F b - (-2 : ℂ) • 1 : Coeff q →L[ℂ] Coeff q) := by
    intro b hb
    rw [neg_smul,sub_neg_eq_add]
    convert E.compact_derivative hp2 b hb using 1
    congr 1
  obtain ⟨hO,hDense⟩ := CompactSpectrum.open_dense_isUnit_of_analytic_compact_shift
    E.isOpen E.isPreconnected E.analytic.fderiv (by norm_num : (-2 : ℂ) ≠ 0)
    hcompact ⟨0,E.zero_mem,hu0⟩
  refine ⟨{b ∈ U | IsUnit (fderiv ℂ F b)},hO,fun _ hb => hb.1,hDense,?_⟩
  intro b hb
  exact ⟨hb.2,NLS.ComplexAnalysis.exists_localInverse_of_isUnit_fderiv (E.analytic b hb.1) hb.2⟩

/-- The same frequency has a real-valued analytic restriction on nonnegative actions. -/
theorem real_extension (E : SourceOriginalFrequencyData D U F) (h2p : 2 ≤ p) :
    ∃ R : RealCoeff q → RealCoeff q,
      AnalyticOnNhd ℝ R (RealCoeff.complexCLM q ⁻¹' U) ∧
      ∀ b : RealCoeff q, RealCoeff.complexCLM q b ∈ U → (∀ n, 0 ≤ b n) →
        RealCoeff.complexCLM q (R b) = F (RealCoeff.complexCLM q b) := by
  obtain ⟨Wa,sa,A,P,hs,hrec⟩ := E.spectral
  obtain ⟨T,_,hT,R,hR,he⟩ := A.exists_real_analytic_actionMap hs D.complex h2p F E.isOpen E.analytic hrec
  exact ⟨R,hT ▸ hR,fun b hb hpos => he b (hT.symm ▸ hb) hpos⟩

end SourceOriginalFrequencyData
end NLS.ZakharovShabat
