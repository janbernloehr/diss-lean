import NLS.ZakharovShabat.SourceFiniteGapFourthOpening
import NLS.ZakharovShabat.SourceFiniteGapClosedFrequency

/-! # The physical H₄ frequency at a closed finite-gap action

The closed frequency is the second amplitude derivative of physical H₄.
A fixed finite support and analytic opening line identify it with the
open-frequency limit and the same weighted second-moment formula.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V X : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The action t²/2 gives the physical second amplitude derivative at a closed action. -/
def finiteGapFourthClosedFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (_hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) : ℂ :=
  deriv (deriv (D.physicalGapOpeningHamiltonian φ hf n 4)) 0

/-- The independently defined second derivative is the open-frequency limit
and satisfies Lemma 5.2 at the collapsed selected action. -/
theorem finiteGapFourthClosedFrequency_eq_limit_and_moments
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) :
    deriv (D.physicalGapOpeningHamiltonian φ hf n 4) 0 = 0 ∧
    D.finiteGapFourthClosedFrequency φ hf n hn-
      6*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2-
      (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1-
      (2*(n:ℂ)*Real.pi)^3 = -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val) ∧
    Tendsto (fun k : ℕ => D.finiteGapFourthOpenFrequency (D.hilbertGapOpening φ n (1/((k:ℝ)+1)))
      (D.hilbertGapOpening_mem_finiteGap φ hf n _) n
      (D.hilbertGapOpening_gap_ne_zero φ n hn _ (by positivity))) atTop
        (nhds (D.finiteGapFourthClosedFrequency φ hf n hn)) := by
  classical
  let a := fun k : ℕ => 1/((k:ℝ)+1)
  have ha : Tendsto a atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hane (k : ℕ) : a k ≠ 0 := by dsimp [a]; positivity
  let γ := fun k : ℕ => D.hilbertGapOpening φ n (a k)
  let hγ := fun k : ℕ => D.hilbertGapOpening_mem_finiteGap φ hf n (a k)
  let hg := fun k : ℕ => D.hilbertGapOpening_gap_ne_zero φ n hn (a k) (hane k)
  let ω := fun k : ℕ => D.finiteGapFourthOpenFrequency (γ k) (hγ k) n (hg k)
  let L : ℂ := 6*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2+
    (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1+
    (2*(n:ℂ)*Real.pi)^3-12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val)
  have hlim : Tendsto (fun k => (γ k).val) atTop (nhds φ.val) := D.tendsto_hilbertGapOpening_sequence φ n
  have hmass : Tendsto (fun k => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (γ k) (hγ k) 1)
      atTop (nhds (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1)) := by
    simp only [sourceFiniteGapNLSHamiltonian_one_eq_mass]
    exact (analyticOnNhd_sourceHilbertMass φ.val (mem_univ _)).continuousAt.tendsto.comp hlim
  have hmomentum : Tendsto (fun k => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (γ k) (hγ k) 2)
      atTop (nhds (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2)) := by
    have he := (analyticAt_sourceFiniteGapHamiltonian_two_on_curve (D.hilbertGapOpening φ n)
      (D.hilbertGapOpening_mem_finiteGap φ hf n) (insert n hf.toFinset)
      (D.hilbertGapOpening_gap_support φ hf n) 0
      (D.analyticOnNhd_hilbertGapOpening φ n 0 (mem_univ _))).continuousAt.tendsto.comp ha
    simpa only [Function.comp_def,γ,D.hilbertGapOpening_zero] using he
  have hmom : Tendsto (fun l => ∑' k : ℤ, (k:ℂ)*A.moment n k 2 (γ l).val) atTop
      (nhds (∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val)) := by
    apply A.weighted_positive_moment_sum_tendsto_of_eventually_fixed_gap_support
      (fun k => (γ k).val) φ.val (A.realType_subset_domain φ.property) hlim (insert n hf.toFinset)
    exact Eventually.of_forall fun k => ⟨A.realType_subset_domain (γ k).property,
      D.hilbertGapOpening_gap_support φ hf n (a k)⟩
  have hω : Tendsto ω atTop (nhds L) := by
    have h := (((hmomentum.const_mul 6).add (hmass.const_mul ((12*Real.pi:ℂ)*n))).add_const
      ((2*(n:ℂ)*Real.pi)^3)).sub (hmom.const_mul (12:ℂ))
    apply h.congr
    intro k
    have he := D.finiteGapFourthOpenFrequency_renormalized_eq_moments A hs (γ k) (hγ k) n (hg k)
    dsimp only [ω]
    linear_combination -he
  have hder (k : ℕ) : deriv (D.physicalGapOpeningHamiltonian φ hf n 4) (a k) = (a k:ℂ)*ω k :=
    D.deriv_physicalGapOpeningHamiltonian_four φ hf n hn (a k) (hane k)
  obtain ⟨hzero,hsecond⟩ := second_deriv_eq_of_amplitude_frequency_limit
    (D.physicalGapOpeningHamiltonian φ hf n 4)
    (D.analyticOnNhd_physicalGapOpeningHamiltonian_four φ hf n 0 (mem_univ _)) a ω L ha hane hω hder
  change D.finiteGapFourthClosedFrequency φ hf n hn = L at hsecond
  refine ⟨hzero,?_,?_⟩
  · rw [hsecond]
    dsimp [L]
    ring
  · rw [hsecond]
    exact hω

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
