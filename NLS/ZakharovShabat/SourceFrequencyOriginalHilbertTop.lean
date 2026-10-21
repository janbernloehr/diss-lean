import NLS.ZakharovShabat.SourceFrequencyOriginalHilbert
import NLS.SequenceSpaces.RealCoeffExponent

/-! # Every target exponent for the original common frequency

The infinity target preserves the same original family, action domain,
and literal frequency values, including the real analytic realization.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceOriginalHilbertFrequencyData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {U : Set (Coeff 1)} {ωstar : Coeff 1 → ℤ → ℂ}

/-- The common frequency has an infinity-norm realization on exactly its
existing action domain, retaining complex and real analyticity. -/
theorem realizations_top (Q : SourceOriginalHilbertFrequencyData D U ωstar) :
    ∃ F : Coeff 1 → Coeff ⊤, AnalyticOnNhd ℂ F U ∧ AnalyticOnNhd ℝ F U ∧
      (∀ b ∈ U, ∀ n, F b n = ωstar b n) ∧
      ∃ R : RealCoeff 1 → RealCoeff ⊤, AnalyticOnNhd ℝ R (RealCoeff.complexCLM 1 ⁻¹' U) ∧
        ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∀ n, (R b n : ℂ) = ωstar (RealCoeff.complexCLM 1 b) n := by
  obtain ⟨F,hF,hFR,hval,R,hR,hRval⟩ := Q.realizations 2 (by simp) (by norm_num)
  let L := Coeff.exponentInclusion (show (2:ℝ≥0∞) ≤ ⊤ from le_top)
  let LR := RealCoeff.exponentInclusion (show (2:ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨fun b => L (F b),?_,?_,?_,fun b => LR (R b),?_,?_⟩
  · intro b hb
    exact (L.analyticAt _).comp (hF b hb)
  · intro b hb
    exact ((L.restrictScalars ℝ).analyticAt _).comp (hFR b hb)
  · intro b hb n
    exact hval b hb n
  · intro b hb
    exact (LR.analyticAt _).comp (hR b hb)
  · intro b hb n
    exact hRval b hb n

/-- All target exponents above one, including infinity, use the same
original frequency and the same action neighborhood. -/
theorem realizations_all (Q : SourceOriginalHilbertFrequencyData D U ωstar)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 1 < r) :
    ∃ F : Coeff 1 → Coeff r, AnalyticOnNhd ℂ F U ∧ AnalyticOnNhd ℝ F U ∧
      (∀ b ∈ U, ∀ n, F b n = ωstar b n) ∧
      ∃ R : RealCoeff 1 → RealCoeff r, AnalyticOnNhd ℝ R (RealCoeff.complexCLM 1 ⁻¹' U) ∧
        ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∀ n, (R b n : ℂ) = ωstar (RealCoeff.complexCLM 1 b) n := by
  by_cases htop : r = ⊤
  · subst r
    exact Q.realizations_top
  · exact Q.realizations r htop hr

/-- The literal common frequency sequence belongs to every target
exponent above one throughout its original complex action domain. -/
theorem memℓp_all (Q : SourceOriginalHilbertFrequencyData D U ωstar)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : 1 < r) (b : Coeff 1) (hb : b ∈ U) :
    Memℓp (ωstar b) r := by
  obtain ⟨F,_,_,hval,_⟩ := Q.realizations_all r hr
  have he : ωstar b = ⇑(F b) := funext (fun n => (hval b hb n).symm)
  rw [he]
  exact lp.memℓp _

end NLS.ZakharovShabat.SourceOriginalHilbertFrequencyData
