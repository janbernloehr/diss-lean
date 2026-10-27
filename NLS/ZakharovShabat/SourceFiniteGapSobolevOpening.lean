import NLS.ZakharovShabat.SourceSobolevGapOpening
import NLS.ZakharovShabat.SourceHilbertGapOpening
import NLS.ZakharovShabat.SourceFiniteGapSobolev

/-! # Finite-gap opening converges in every nonnegative Sobolev norm

Every real spectral finite-gap source has the required native weighted
representative. Its Sobolev opening curve is the original Hilbert curve
on raw coefficients, and in particular converges in H1 at zero amplitude.
The preserved quantities are the other actions and gap support; equality
of all other numerical gap lengths is not asserted.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The analytic Sobolev lift is exactly the original Hilbert opening curve. -/
theorem originalWeightedRealSource_sobolevGapOpening_hilbert
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (n : ℤ) (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ)
      (D.sobolevGapOpening (by rfl) σ hσ a n t) =
      D.hilbertGapOpening (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a) n t := by
  apply D.hilbertRealHomeomorph.injective
  rw [D.hilbertRealHomeomorph_gapOpening]
  change (D.realHomeomorph (by rfl)) _ = _
  rw [D.originalWeightedRealSource_sobolevGapOpening]
  exact (D.realHomeomorph (by rfl)).apply_symm_apply _

/-- At every real spectral finite-gap source, the same amplitude line has
an analytic representative in every native Sobolev space and converges
there to its initial value. In particular the order-one choice is H1. -/
theorem exists_finiteGap_sobolevGapOpening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (σ : ℝ) (hσ : 0 ≤ σ) (n : ℤ) :
    ∃ a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
      ∃ F : ℝ → weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
        originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a = φ ∧
        F 0 = a ∧ AnalyticOnNhd ℝ F univ ∧ Tendsto F (𝓝 0) (𝓝 a) ∧
        ∀ t : ℝ,
          originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (F t) =
            D.hilbertGapOpening φ n t ∧
          originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (F t) ∈
            sourceFiniteGapLocus (by simp) (by norm_num) := by
  have hm := sourceFiniteGap_mem_all_sobolev (by simp) (by norm_num) φ hf σ hσ
  obtain ⟨a,ha⟩ := (exists_originalWeightedRealSource_iff (sourceSobolevSpectralWeight σ hσ) φ).mpr
    (by simpa only [sourceSobolevSpectralWeight_even] using hm)
  refine ⟨a,D.sobolevGapOpening (by rfl) σ hσ a n,ha,
    D.sobolevGapOpening_zero (by rfl) σ hσ a n,
    D.analyticOnNhd_sobolevGapOpening (by rfl) σ hσ a n,
    D.tendsto_sobolevGapOpening_zero (by rfl) σ hσ a n,?_⟩
  intro t
  have he := D.originalWeightedRealSource_sobolevGapOpening_hilbert σ hσ a n t
  rw [ha] at he
  exact ⟨he,he ▸ D.hilbertGapOpening_mem_finiteGap φ hf n t⟩

/-- A concrete sequence of finite-gap approximants opens the selected
collapsed gap, preserves every other gap's zero status, and converges
in the chosen Sobolev norm. No numerical gap-length equality is assumed. -/
theorem exists_finiteGap_sobolev_open_approximants
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
      ∃ G : ℕ → weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
        originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a = φ ∧
        Tendsto G atTop (𝓝 a) ∧ ∀ l : ℕ,
          let ψ := originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (G l)
          ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧
          canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val)
            (periodOnePotential_mem ψ.val) n ≠ 0 ∧
          ∀ k : ℤ, k ≠ n →
            (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val)
              (periodOnePotential_mem ψ.val) k = 0 ↔
             canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
              (periodOnePotential_mem φ.val) k = 0) := by
  obtain ⟨a,F,ha,_,_,hlim,hF⟩ := D.exists_finiteGap_sobolevGapOpening φ hf σ hσ n
  refine ⟨a,fun l => F (1 / ((l : ℝ) + 1)),ha,
    hlim.comp tendsto_one_div_add_atTop_nhds_zero_nat,?_⟩
  intro l
  change originalWeightedRealSource _ (F _) ∈ _ ∧ _
  rw [(hF (1 / ((l : ℝ) + 1))).1]
  exact ⟨D.hilbertGapOpening_mem_finiteGap φ hf n _,
    D.hilbertGapOpening_gap_ne_zero φ n hn _ (by positivity),
    fun k hk => D.hilbertGapOpening_gap_zero_iff_of_ne φ n k hk _⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
