import NLS.ZakharovShabat.SourceHilbertActionTrace
import NLS.ZakharovShabat.SourceActionExponentDifferential

/-! # The ordinary NLS mass correction for exponents at most two

The physical Hilbert mass pulled back through the exponent inclusion is
entire. Its real restriction equals the absolutely convergent sum of the
original spectral actions, so action preservation also preserves the
ordinary NLS frequency correction.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Physical mass on the source exponent p ≤ 2, with its entire complex extension. -/
def sourceOrdinaryComplexMass (hp2 : p ≤ 2) (φ : CoeffPair p) : ℂ :=
  sourceHilbertMass (CoeffPair.exponentInclusion hp2 φ)

/-- Real physical mass of a real source. -/
def sourceOrdinaryMass (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) : ℝ :=
  (sourceOrdinaryComplexMass hp2 φ.val).re

theorem analytic_sourceOrdinaryComplexMass (hp2 : p ≤ 2) :
    AnalyticOnNhd ℂ (sourceOrdinaryComplexMass hp2) univ := by
  intro φ _
  exact (analyticOnNhd_sourceHilbertMass _ (mem_univ _)).comp
    ((CoeffPair.exponentInclusion hp2).analyticAt φ)

theorem analytic_sourceOrdinaryMass (hp2 : p ≤ 2) :
    AnalyticOnNhd ℝ (sourceOrdinaryMass hp2) univ := by
  intro φ _
  exact (Complex.reCLM.analyticAt _).comp
    (((analytic_sourceOrdinaryComplexMass hp2 φ.val (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp
      ((realTypeSourceSubmodule p).subtypeL.analyticAt φ))

/-- The complex mass restricts to the real physical mass. -/
theorem sourceOrdinaryMass_complex (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    (sourceOrdinaryMass hp2 φ : ℂ) = sourceOrdinaryComplexMass hp2 φ.val := by
  have hreal : IsRealType (CoeffPair.toMax 2 (CoeffPair.exponentInclusion hp2 φ.val)) :=
    (realTypeSourceExponentInclusion hp2 ⟨φ.val,φ.property⟩).property
  change ((sourceHilbertMass (CoeffPair.exponentInclusion hp2 φ.val)).re : ℂ) =
    sourceHilbertMass (CoeffPair.exponentInclusion hp2 φ.val)
  rw [sourceHilbertMass_eq_half_norm_sq_of_realType _ hreal,Complex.ofReal_re]

/-- Physical mass equals the literal sum of the original spectral actions. -/
theorem sourceOrdinaryMass_eq_tsum (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) :
    sourceOrdinaryMass hp2 φ = ∑' n : ℤ, (sourceComplexAction hp hp1 n φ.val).re := by
  let ψ : realTypeSourceSubmodule 2 := realTypeSourceExponentInclusion hp2 ⟨φ.val,φ.property⟩
  have he := sourceHilbert_sum_actions_eq_half_norm_sq ψ
  calc
    sourceOrdinaryMass hp2 φ = ‖ψ.val‖^2/2 := by
      change (sourceHilbertMass ψ.val).re = _
      have hm := congrArg Complex.re (sourceHilbertMass_eq_half_norm_sq_of_realType ψ.val ψ.property)
      exact hm
    _ = ∑' n : ℤ, (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re := he.symm
    _ = ∑' n : ℤ, (sourceComplexAction hp hp1 n φ.val).re := by
      apply tsum_congr
      intro n
      exact congrArg Complex.re ((sourceComplexAction_eq_sourceRealAction
        (by simp) (by norm_num) n ψ.val ψ.property).symm.trans
        (sourceComplexAction_real_exponent hp (by simp) hp1
          (by norm_num) hp2 n ⟨φ.val,φ.property⟩).symm)

/-- The action series is absolutely convergent throughout the real source space for p ≤ 2. -/
theorem summable_sourceOrdinaryActions (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) : Summable (fun n : ℤ => ‖sourceComplexAction hp hp1 n φ.val‖) := by
  obtain ⟨_,_,_,_,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  let ψ : realTypeSourceSubmodule 2 := realTypeSourceExponentInclusion hp2 ⟨φ.val,φ.property⟩
  have h := D.summable_norm_hilbert_actions ψ.val (D.real_subset ψ.property)
  exact h.congr (fun n => congrArg norm (sourceComplexAction_real_exponent hp (by simp) hp1
    (by norm_num) hp2 n ⟨φ.val,φ.property⟩).symm)

/-- Preserving the original actions preserves the mass correction. -/
theorem sourceOrdinaryMass_eq_of_actions (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ ψ : realTypeSourceSubmodule p)
    (h : ∀ n, sourceComplexAction hp hp1 n φ.val = sourceComplexAction hp hp1 n ψ.val) :
    sourceOrdinaryMass hp2 φ = sourceOrdinaryMass hp2 ψ := by
  rw [sourceOrdinaryMass_eq_tsum hp hp1,sourceOrdinaryMass_eq_tsum hp hp1]
  exact tsum_congr (fun n => congrArg Complex.re (h n))

end NLS.ZakharovShabat
