import NLS.ZakharovShabat.SourceH1ActualGapCriterion
import NLS.ZakharovShabat.SourceFiniteGapDensity

/-! # Finite-gap reduction of the sharp cubic bound

Continuity of actual moments and density of finite-gap sources reduce the
sharp cubic estimate to the finite-gap case, for every finite p>1. Finite
spectral support supplies action summability. The H1 endpoint therefore
follows from only the finite-gap zero-profile identities; those identities
are an explicit hypothesis here and are proved in `SourceFiniteGapProfileIdentity`.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- The actual moment family is continuous on the entire real source space. -/
theorem continuous_real_moment (n : ℤ) (k : ℕ) :
    Continuous (fun φ : realTypeSourceSubmodule p => A.moment n k φ.val) := by
  apply continuous_iff_continuousAt.mpr
  intro φ
  exact ((A.analytic_moment n k) φ.val (A.realType_subset_domain φ.property)).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- Density reduces the sharp cubic bound to actual finite-gap sources at every finite p>1. -/
theorem real_action_sq_le_cubic_iff_finiteGap (n : ℤ) :
    (∀ φ : realTypeSourceSubmodule p,
      (3/4:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖^2 ≤ (A.moment n 3 φ.val).re) ↔
    (∀ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 →
      (3/4:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖^2 ≤ (A.moment n 3 φ.val).re) := by
  constructor
  · exact fun h φ _ => h φ
  · intro hfinite φ
    have hc : IsClosed {ψ : realTypeSourceSubmodule p |
        (3/4:ℝ)*‖A.moment n 1 ψ.val‖^2 ≤ (A.moment n 3 ψ.val).re} :=
      isClosed_le (continuous_const.mul ((A.continuous_real_moment n 1).norm.pow 2))
        (Complex.continuous_re.comp (A.continuous_real_moment n 3))
    have hsub : sourceFiniteGapLocus hp hp1 ⊆ {ψ : realTypeSourceSubmodule p |
        (3/4:ℝ)*‖A.moment n 1 ψ.val‖^2 ≤ (A.moment n 3 ψ.val).re} := by
      intro ψ hψ
      change (3/4:ℝ)*‖A.moment n 1 ψ.val‖^2 ≤ (A.moment n 3 ψ.val).re
      rw [A.moment_one n (A.realType_subset_domain ψ.property)]
      exact hfinite ψ hψ
    have h := closure_minimal hsub hc (dense_sourceFiniteGapLocus hp hp1 φ)
    change (3/4:ℝ)*‖A.moment n 1 φ.val‖^2 ≤ (A.moment n 3 φ.val).re at h
    rwa [A.moment_one n (A.realType_subset_domain φ.property)] at h

include A in
/-- Finite gap support supplies absolute action summability at every finite source exponent. -/
theorem summable_actions_of_finiteGap (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    Summable (fun n : ℤ => ‖sourceComplexAction hp hp1 n φ.val‖) := by
  apply summable_of_ne_finset_zero (s := hf.toFinset)
  intro n hn
  have hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    by_contra hg
    apply hn
    exact hf.mem_toFinset.mpr hg
  rw [← A.moment_one n (A.realType_subset_domain φ.property),
    A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n hg 1,norm_zero]

/-- Actual finite-gap profile identities suffice for the sharp cubic estimate on all real sources. -/
theorem real_action_sq_le_cubic_of_finiteGap_profile_identity (n : ℤ)
    (hrep : ∀ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 →
      ∀ x ∈ Icc (0:ℝ) Real.pi, sourceRealGapCosineProfile hp hp1 φ.val n x =
        sourceGapHalfWidthReal hp hp1 φ n*Real.sin x*(1+sourceExteriorGapCorrection hp hp1 φ n x))
    (φ : realTypeSourceSubmodule p) :
    (3/4:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖^2 ≤ (A.moment n 3 φ.val).re := by
  apply (A.real_action_sq_le_cubic_iff_finiteGap n).mpr _ φ
  intro ψ hψ
  exact A.real_action_sq_le_cubic_of_actual_gap_identity ψ n (A.summable_actions_of_finiteGap ψ hψ)
    (hrep ψ hψ)

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas

namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- Only finite-gap zero-profile identities are needed for the unrestricted H1 endpoint. -/
theorem sourceH1_energy_le_lemma272_of_finiteGap_zero_profile_identity
    (hrep : ∀ φ : realTypeSourceSubmodule 4, φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) →
      ∀ x ∈ Icc (0:ℝ) Real.pi,
        sourceRealGapCosineProfile (by simp) (by norm_num) φ.val 0 x =
          sourceGapHalfWidthReal (by simp) (by norm_num) φ 0*Real.sin x*
            (1+sourceExteriorGapCorrection (by simp) (by norm_num) φ 0 x))
    (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  let φ : realTypeSourceSubmodule 4 := ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have h := A.real_action_sq_le_cubic_of_finiteGap_profile_identity 0 hrep φ
  rw [← sourceH1_actionTerm_zero_eq_FL4 a 0] at h
  exact A.sourceH1_energy_le_lemma272_of_zero_moment a h

end NLS.ZakharovShabat
