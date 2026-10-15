import NLS.ZakharovShabat.SourceSection20Domain
import NLS.ZakharovShabat.SourceMomentReality

/-!
# Original Section 20 contour moments and their physical frequency sum

The same Section 19 primitive appears in the literal contour formula,
with the original psi roots and raw 2π normalization. Every positive
moment vanishes at a collapsed gap, including the diagonal case.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The original moment integrals use the very primitive of the retained
Section 19 package, simultaneously for all indices and orders. -/
theorem moment_contours (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ (n k : ℤ) (m : ℕ), A.moment n k m ψ =
        ∮ z in C(c k,R k), (sourceFullAbelianPrimitive hp hp1 B k (z,ψ))^m*
          (sourcePsiCandidate n (z,(s n ψ : Coeff p))/sourceCanonicalRoot hp hp1 ψ z) := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (Q.moment_subset hψ)
  obtain ⟨E⟩ := (A.localChart φ).charts ψ hφ
  obtain ⟨E'⟩ := Q.charts ψ hψ
  obtain ⟨c,R,hC,he⟩ := A.circle_representation ψ (Q.moment_subset hψ)
  refine ⟨c,R,hC,?_⟩
  intro n k m
  exact (he n k m).trans (sourceAbelianMomentCircle_independent_neighborhood hp hp1 Wa B n k m
    (s n ψ : Coeff p) ψ E E' (c k) (R k) (hC.2 k).1.le (hC.2 k).2.2.2)

/-- All four clauses of Lemma 20.1, on the common original domain. -/
theorem lemma20_1 :
    (∀ n k m, AnalyticOnNhd ℂ (A.moment n k m) U) ∧
    (∀ ψ ∈ U, ∀ n k, A.moment n k 0 ψ = (2*Real.pi : ℂ)*(if k = n then 1 else 0)) ∧
    (∀ ψ ∈ U, ∀ n k l, A.moment n k (2*l+1) ψ = 0) ∧
    ∀ ψ ∈ U, ∀ n k,
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0 →
      ∀ m : ℕ, 1 ≤ m → A.moment n k m ψ = 0 := by
  refine ⟨fun n k m => (A.analytic_moment n k m).mono Q.moment_subset,
    fun ψ hψ => A.moment_zero_order ψ (Q.moment_subset hψ),
    fun ψ hψ => A.moment_odd ψ (Q.moment_subset hψ),?_⟩
  intro ψ hψ n k hk m hm
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact A.moment_succ_of_collapsed ψ (Q.moment_subset hψ) n k hk l

/-- Theorem 20.4's actual convergent series, with its exact coefficient four. -/
theorem frequency_hasSum (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) :
    HasSum (fun k => -(4/(2*Real.pi):ℂ)*A.moment n k 2 ψ) (A.renormalizedFrequency n ψ) :=
  (Q.summable ψ hψ n).of_norm.hasSum.mul_left _

/-- Lemma 20.2: the independently constructed physical frequency and mass
equal the original moment sum, also when the selected gap is collapsed. -/
theorem physical_frequency
    {W₂ B₂ V₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₂ B₂ V₂ s₂)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    D₂.complex.finiteGapFrequencyAtExponent hp hp1 φ hf n-
      4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1-(2*(n:ℂ)*Real.pi)^2 =
      -(4/(2*Real.pi):ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val) :=
  (A.renormalizedFrequency_eq_physical_finiteGap_all_exponents D₂.complex
    Q.roots.toSourcePsiIsolatingComplexExtension φ hf n).symm

/-- The physical finite-gap values determine each analytic frequency uniquely. -/
theorem unique_frequency
    {W₂ B₂ V₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₂ B₂ V₂ s₂)
    (n : ℤ) (F : CoeffPair p → ℂ) (hF : AnalyticOnNhd ℂ F U)
    (he : ∀ (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1),
      F φ.val = D₂.complex.finiteGapFrequencyAtExponent hp hp1 φ hf n-
        4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1-(2*(n:ℂ)*Real.pi)^2) :
    EqOn F (A.renormalizedFrequency n) U := by
  apply eqOn_of_analytic_of_sourceFiniteGap hp hp1 Q.source_open Q.connected Q.real_subset hF (Q.frequency_analytic n)
  intro φ hf
  exact (he φ hf).trans (Q.physical_frequency D₂ φ hf n)

/-- Frequencies are real-valued on the entire original real source locus. -/
theorem frequency_real (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (A.renormalizedFrequency n φ.val).im = 0 :=
  A.renormalizedFrequency_im_eq_zero Q.roots.toSourcePsiIsolatingComplexExtension φ n

end NLS.ZakharovShabat.SourceSection20Data
