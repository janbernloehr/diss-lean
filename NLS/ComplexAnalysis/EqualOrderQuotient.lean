import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Liouville

/-!
# Entire quotients of functions with equal finite orders

Meromorphic normal form fills the quotient at common zeros. Equal finite
orders make every filled germ analytic and nonvanishing. The resulting entire
quotient multiplies the denominator to the numerator everywhere.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- The quotient with all removable values filled by meromorphic normal form. -/
def analyticQuotient (f g : ℂ → ℂ) : ℂ → ℂ := toMeromorphicNFOn (f/g) Set.univ

/-- Equal finite analytic orders give meromorphic quotient order zero. -/
theorem meromorphicOrderAt_div_eq_zero_of_equal_order {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (ho : analyticOrderAt f z = analyticOrderAt g z) (hfin : analyticOrderAt g z ≠ ⊤) :
    meromorphicOrderAt (f/g) z = 0 := by
  rw [meromorphicOrderAt_div hf.meromorphicAt hg.meromorphicAt,
    hf.meromorphicOrderAt_eq,hg.meromorphicOrderAt_eq,ho]
  lift analyticOrderAt g z to ℕ using hfin with n hn
  simp

/-- The filled quotient has order zero at each point when the entire functions have equal finite orders. -/
theorem meromorphicOrderAt_analyticQuotient {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ho : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfin : ∀ z, analyticOrderAt g z ≠ ⊤) (z : ℂ) :
    meromorphicOrderAt (analyticQuotient f g) z = 0 := by
  rw [analyticQuotient,meromorphicOrderAt_toMeromorphicNFOn (hf.meromorphicOn.div hg.meromorphicOn) (Set.mem_univ z)]
  exact meromorphicOrderAt_div_eq_zero_of_equal_order (hf z (Set.mem_univ _)) (hg z (Set.mem_univ _)) (ho z) (hfin z)

/-- Equal finite orders remove every quotient singularity on the complex plane. -/
theorem analyticOnNhd_analyticQuotient {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ho : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfin : ∀ z, analyticOrderAt g z ≠ ⊤) : AnalyticOnNhd ℂ (analyticQuotient f g) Set.univ := by
  intro z hz
  apply (meromorphicNFOn_toMeromorphicNFOn (f/g) Set.univ hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [← analyticQuotient,meromorphicOrderAt_analyticQuotient hf hg ho hfin]

/-- The filled quotient does not vanish, including at common zeros of the original functions. -/
theorem analyticQuotient_ne_zero {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ho : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfin : ∀ z, analyticOrderAt g z ≠ ⊤) (z : ℂ) : analyticQuotient f g z ≠ 0 := by
  apply (meromorphicNFOn_toMeromorphicNFOn (f/g) Set.univ (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp
  exact meromorphicOrderAt_analyticQuotient hf hg ho hfin z

/-- At a nonzero denominator the filled quotient is ordinary division. -/
theorem analyticQuotient_eq_div {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (z : ℂ) (hgz : g z ≠ 0) : analyticQuotient f g z = f z/g z := by
  rw [analyticQuotient,toMeromorphicNFOn_eq_toMeromorphicNFAt
    (hf.meromorphicOn.div hg.meromorphicOn) (Set.mem_univ z)]
  have ha := (hf z (Set.mem_univ _)).div (hg z (Set.mem_univ _)) hgz
  exact congrFun (toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt) z

/-- The filled quotient gives exact factorization at every point, including the common zeros. -/
theorem analyticQuotient_mul {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ho : ∀ z, analyticOrderAt f z = analyticOrderAt g z) (z : ℂ) :
    analyticQuotient f g z*g z = f z := by
  by_cases hz : g z = 0
  · have hfz : f z = 0 := by
      by_contra h
      have horder := (hf z (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr h
      have hgz := (hg z (Set.mem_univ _)).analyticOrderAt_eq_zero.mp ((ho z).symm.trans horder)
      exact hgz hz
    simp [hz,hfz]
  · rw [analyticQuotient_eq_div hf hg z hz,div_mul_cancel₀ _ hz]

/-- A bounded filled quotient of functions with equal finite orders is a nonzero constant factor. -/
theorem exists_const_factor_of_bounded_analyticQuotient {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ho : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfin : ∀ z, analyticOrderAt g z ≠ ⊤)
    (hb : Bornology.IsBounded (Set.range (analyticQuotient f g))) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, f z = c*g z := by
  have ha := analyticOnNhd_analyticQuotient hf hg ho hfin
  have hd : Differentiable ℂ (analyticQuotient f g) := fun z => (ha z (Set.mem_univ _)).differentiableAt
  obtain ⟨c,hc⟩ := hd.exists_const_forall_eq_of_bounded hb
  refine ⟨c,?_,fun z => ?_⟩
  · rw [← hc 0]
    exact analyticQuotient_ne_zero hf hg ho hfin 0
  · rw [← hc z]
    exact (analyticQuotient_mul hf hg ho z).symm

/-- A prescribed finite limit at infinity determines the exact entire normalization. -/
theorem eq_const_mul_of_tendsto_analyticQuotient {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ho : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfin : ∀ z, analyticOrderAt g z ≠ ⊤) {c : ℂ}
    (hc : Tendsto (analyticQuotient f g) (cocompact ℂ) (𝓝 c)) : ∀ z, f z = c*g z := by
  have ha := analyticOnNhd_analyticQuotient hf hg ho hfin
  have hd : Differentiable ℂ (analyticQuotient f g) := fun z => (ha z (Set.mem_univ _)).differentiableAt
  intro z
  rw [← hd.apply_eq_of_tendsto_cocompact z hc]
  exact (analyticQuotient_mul hf hg ho z).symm

end NLS.ComplexAnalysis
