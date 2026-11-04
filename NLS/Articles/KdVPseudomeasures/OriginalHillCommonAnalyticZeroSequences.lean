import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodUniformFullInverse
import NLS.KdV.HminusOneCanonicalHillZeroSequences

/-! Original physical Hill zero displacements have full-l2 complex
analytic extensions on ONE open connected neighborhood containing the
ENTIRE real Hminus-one form, chosen BEFORE ALL numerator indices.
The finer squared-gap estimate and universal product scalar remain open. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_common_complex_analytic_zero_sequences :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ IsConnected U ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ U) ∧
      U ⊆ hillHminusCanonicalPsiDomain ∧
      ∃ s : ℕ+ → PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2,
        ∀ n : ℕ+, AnalyticOnNhd ℂ (s n) U ∧
          (∀ q : OriginalHminusOnePotential, s n (originalPeriodOneCoefficients q) = originalHillPsiZeroDisplacement n q) ∧
          ∀ m : ℕ+, m ≠ n → ∀ q ∈ U,
            hillHminusCanonicalPsi n (hillEnergySequenceZero m (s n q),q) = 0 := by
  refine ⟨hillHminusCanonicalZeroSequenceDomain,isOpen_hillHminusCanonicalZeroSequenceDomain,
    isConnected_hillHminusCanonicalZeroSequenceDomain,
    (fun q => real_mem_hillHminusCanonicalZeroSequenceDomain _ (originalPeriodOneCoefficients_real q)),
    hillHminusCanonicalZeroSequenceDomain_subset_psiDomain,hillHminusCanonicalZeroSequence,?_⟩
  intro n
  exact ⟨analyticOnNhd_hillHminusCanonicalZeroSequence n,
    (fun q => hillHminusCanonicalZeroSequence_real n _ (originalPeriodOneCoefficients_real q)),
    fun m hmn q hq => hillHminusCanonicalZeroSequence_retained_root n m hmn q hq⟩

theorem exists_original_common_Hill_zero_sequence_period_patch (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.source ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ s : ℕ+ → PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2,
          ∀ n : ℕ+, AnalyticOnNhd ℂ (s n) (ball (originalPeriodOneCoefficients q) ε) ∧
            (∀ y ∈ ball (originalPeriodOneCoefficients q) ε,
              (s n y,y) ∈ P.inputDomain ∧ P.equation n (s n y,y) = 0) ∧
            ∀ r : OriginalHminusOnePotential, originalPeriodOneCoefficients r ∈ ball (originalPeriodOneCoefficients q) ε →
              s n (originalPeriodOneCoefficients r) = originalHillPsiZeroDisplacement n r := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch _ (originalPeriodOneCoefficients_real q)
  obtain ⟨_,ε,_,hε,s,hs⟩ := P.exists_common_actual_analytic_zero_sequences _ hq (originalPeriodOneCoefficients_real q)
  refine ⟨P,hq,ε,hε,s,?_⟩
  intro n
  exact ⟨(hs n).1,(fun y hy => ⟨((hs n).2.2.1 y hy).1,((hs n).2.2.1 y hy).2.1⟩),
    fun r hr => (hs n).2.2.2.1 _ hr (originalPeriodOneCoefficients_real r)⟩

end NLS.Articles.KdVPseudomeasures
