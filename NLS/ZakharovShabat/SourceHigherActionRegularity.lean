import NLS.ZakharovShabat.SourceHigherActionAtlas
import NLS.ZakharovShabat.SourceFiniteGapHigherActionTrace
import Mathlib.Analysis.Analytic.Constructions

/-! # Regularity and trace calibration of the glued higher actions -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical complex higher actions have simultaneous defining contours. -/
theorem sourceComplexHigherAction_circle_representation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hψ : ψ ∈ sourceComplexHigherActionDomain hp hp1) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ n k, sourceComplexHigherAction hp hp1 n k ψ = sourceHigherActionCircle hp hp1 ψ (c n) (R n) k :=
  (sourceHigherActionAtlas hp hp1).circle_representation ψ hψ

/-- At a real source every real-centered isolating circle computes the gap
integral, independently of the constructed atlas. -/
theorem sourceHigherActionCircle_eq_real_of_realCentered_enclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ)
    (c : ℂ) (R : ℝ) (hc : c.im = 0) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 φ.val n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val n) :
    sourceHigherActionCircle hp hp1 φ.val c R k = (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
  obtain ⟨d,S,hfamily,he⟩ := sourceComplexHigherAction_circle_representation hp hp1 φ.val
    (realType_subset_sourceComplexHigherActionDomain hp hp1 φ.property)
  rw [← sourceComplexHigherAction_eq_real hp hp1 φ n k,he n k]
  exact sourceHigherActionCircle_eq_of_realCentered_enclosingCircles hp hp1 n k φ.val φ.property
    c (d n) R (S n) hc (hfamily.1 n) hR (hfamily.2 n).1 hseg (hfamily.2 n).2.1 hother (hfamily.2 n).2.2.1

/-- Each real higher action is real analytic in the original source norm,
including at collapsed gaps. -/
theorem analyticOnNhd_sourceRealHigherAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule p => sourceRealHigherAction hp hp1 φ n k) univ := by
  intro φ _
  have ha := (analyticOnNhd_sourceComplexHigherAction hp hp1 n k φ.val
    (realType_subset_sourceComplexHigherActionDomain hp hp1 φ.property)).restrictScalars (𝕜 := ℝ)
  have hi := ha.comp ((realTypeSourceSubmodule p).subtypeL.analyticAt φ)
  have hr := (Complex.reCLM.analyticAt _).comp hi
  simpa only [Function.comp_def,sourceComplexHigherAction_eq_real,reCLM_apply,ofReal_re] using hr

theorem continuous_sourceRealHigherAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (k : ℕ) :
    Continuous (fun φ : realTypeSourceSubmodule p => sourceRealHigherAction hp hp1 φ n k) :=
  continuous_iff_continuousAt.mpr fun φ =>
    (analyticOnNhd_sourceRealHigherAction hp hp1 n k φ (mem_univ _)).continuousAt

/-- The glued complex functions inherit the physical all-order trace formula
at every real finite-gap source. -/
theorem sourceFiniteGap_tsum_complexHigherActions_eq_hamiltonian
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) :
    (∑' n : ℤ, sourceComplexHigherAction hp hp1 n k φ.val) =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/2^k := by
  simp only [sourceComplexHigherAction_eq_real]
  exact sourceFiniteGap_tsum_higherActions_eq_hamiltonian hp hp1 φ hf k

end NLS.ZakharovShabat
