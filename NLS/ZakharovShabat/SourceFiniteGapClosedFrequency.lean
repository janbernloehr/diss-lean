import NLS.ComplexAnalysis.AmplitudeDerivativeLimit
import NLS.ZakharovShabat.SourceFiniteGapOpeningHamiltonian

/-! # The physical frequency at a closed finite-gap action

The selected action on the opening line is `t^2/2`. The closed frequency
is therefore the second amplitude derivative of physical `H3`. A nonzero
opening sequence, fixed finite gap support, and the first-derivative identity
identify it with the limit of actual open-action frequencies and prove the
closed-gap case of the moment formula.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V X : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical second amplitude derivative at a collapsed selected gap,
normalized by the exact action `t^2/2` on the opening line. -/
def finiteGapClosedFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (_hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) : ℂ :=
  deriv (deriv (D.physicalGapOpeningHamiltonian φ hf n 3)) 0

/-- The explicit inverse-natural amplitude sequence converges in the
original Hilbert source norm. -/
theorem tendsto_hilbertGapOpening_sequence
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    Tendsto (fun k : ℕ => (D.hilbertGapOpening φ n (1/((k : ℝ)+1))).val) atTop (𝓝 φ.val) := by
  have he := ((realTypeSourceSubmodule 2).subtypeL.continuous.comp
    (D.continuous_hilbertGapOpening φ n)).continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun k : ℕ => (D.hilbertGapOpening φ n (1/((k : ℝ)+1))).val) atTop
    (𝓝 (D.hilbertGapOpening φ n 0).val) at he
  simpa only [D.hilbertGapOpening_zero] using he

/-- The physical second derivative is the frequency limit. The same argument
also proves that the first physical amplitude derivative vanishes at zero. -/
theorem finiteGapClosedFrequency_eq_limit_and_moments
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) :
    deriv (D.physicalGapOpeningHamiltonian φ hf n 3) 0 = 0 ∧
    D.finiteGapClosedFrequency φ hf n hn -
      4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n : ℂ)*Real.pi)^2 =
        -(4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val) ∧
    Tendsto (fun k : ℕ => D.finiteGapOpenFrequency (D.hilbertGapOpening φ n (1/((k : ℝ)+1)))
      (D.hilbertGapOpening_mem_finiteGap φ hf n _) n
      (D.hilbertGapOpening_gap_ne_zero φ n hn _ (by positivity))) atTop
        (𝓝 (D.finiteGapClosedFrequency φ hf n hn)) := by
  classical
  let a := fun k : ℕ => 1/((k : ℝ)+1)
  have ha : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hane (k : ℕ) : a k ≠ 0 := by dsimp [a]; positivity
  let γ := fun k : ℕ => D.hilbertGapOpening φ n (a k)
  let hγ := fun k : ℕ => D.hilbertGapOpening_mem_finiteGap φ hf n (a k)
  let hg := fun k : ℕ => D.hilbertGapOpening_gap_ne_zero φ n hn (a k) (hane k)
  let ω := fun k : ℕ => D.finiteGapOpenFrequency (γ k) (hγ k) n (hg k)
  let L : ℂ := 4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 +
    (2*(n : ℂ)*Real.pi)^2 - (4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val)
  have hlim : Tendsto (fun k => (γ k).val) atTop (𝓝 φ.val) := D.tendsto_hilbertGapOpening_sequence φ n
  have hmass : Tendsto (fun k => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (γ k) (hγ k) 1)
      atTop (𝓝 (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1)) := by
    simp only [sourceFiniteGapNLSHamiltonian_one_eq_mass]
    exact (analyticOnNhd_sourceHilbertMass φ.val (mem_univ _)).continuousAt.tendsto.comp hlim
  have hmom : Tendsto (fun l => ∑' k : ℤ, A.moment n k 2 (γ l).val) atTop
      (𝓝 (∑' k : ℤ, A.moment n k 2 φ.val)) := by
    apply A.positive_moment_sum_tendsto_of_eventually_fixed_gap_support
      (fun k => (γ k).val) φ.val (A.realType_subset_domain φ.property) hlim (insert n hf.toFinset)
    exact Eventually.of_forall fun k => ⟨A.realType_subset_domain (γ k).property,
      D.hilbertGapOpening_gap_support φ hf n (a k)⟩
  have hω : Tendsto ω atTop (𝓝 L) := by
    have h := ((hmass.const_mul 4).add_const ((2*(n : ℂ)*Real.pi)^2)).sub
      (hmom.const_mul (4/(2*Real.pi) : ℂ))
    apply h.congr
    intro k
    have he := D.finiteGapOpenFrequency_renormalized_eq_moments A hs (γ k) (hγ k) n (hg k)
    dsimp only [ω]
    linear_combination -he
  have hder (k : ℕ) : deriv (D.physicalGapOpeningHamiltonian φ hf n 3) (a k) = (a k : ℂ)*ω k :=
    D.deriv_physicalGapOpeningHamiltonian_three φ hf n hn (a k) (hane k)
  obtain ⟨hzero,hsecond⟩ := second_deriv_eq_of_amplitude_frequency_limit
    (D.physicalGapOpeningHamiltonian φ hf n 3)
    (D.analyticOnNhd_physicalGapOpeningHamiltonian_three φ hf n 0 (mem_univ _)) a ω L ha hane hω hder
  change D.finiteGapClosedFrequency φ hf n hn = L at hsecond
  refine ⟨hzero,?_,?_⟩
  · rw [hsecond]
    dsimp [L]
    ring
  · rw [hsecond]
    exact hω

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
