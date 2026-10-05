import NLS.ZakharovShabat.SourcePrimitivePowerCubicSequence
import NLS.ZakharovShabat.SourceFiniteGapRenormalizedHamiltonian
import NLS.ZakharovShabat.SourceClosedGapsZero
import NLS.SequenceSpaces.LocallyUniformSummation

/-! # The analytic renormalized Hamiltonian on FL⁴

The literal cubic-moment sum defines the extension in Proposition 21.3.
Its analyticity comes from the ℓ¹-valued sequence; its locally uniform
convergence follows from continuous decreasing truncation tails.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {W : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- The renormalized Hamiltonian as the actual cubic-moment series. -/
def renormalizedHamiltonian (ψ : CoeffPair 4) : ℂ :=
  -(4/3:ℂ)*(∑' n : ℤ, A.moment n 3 ψ)

/-- The extension agrees with the physical finite-gap correction. -/
theorem renormalizedHamiltonian_eq_finiteGap (φ : realTypeSourceLocus 4)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    A.renormalizedHamiltonian φ.val = sourceFiniteGapRenormalizedHamiltonian (by simp) (by norm_num) φ hf :=
  (A.finiteGap_hamiltonian_identity φ hf).symm

/-- The complex sum is real on the entire real source locus. -/
theorem real_renormalizedHamiltonian_eq_real_tsum (φ : realTypeSourceSubmodule 4) :
    A.renormalizedHamiltonian φ.val =
      ((-(4/3:ℝ)*(∑' n : ℤ, (A.moment n 3 φ.val).re) : ℝ) : ℂ) := by
  unfold renormalizedHamiltonian
  push_cast
  congr 1
  apply tsum_congr
  intro n
  apply Complex.ext
  · rfl
  · simpa only [ofReal_im] using A.real_odd_moment_im φ n 1

/-- The real cubic moments have an absolutely convergent sum. -/
theorem summable_real_cubic_moments (φ : realTypeSourceSubmodule 4) :
    Summable (fun n => (A.moment n 3 φ.val).re) := by
  obtain ⟨U,_,_,hreal,_,_,_,hs⟩ := A.exists_cubicSequence_analytic
  exact Complex.reCLM.summable (hs φ.val (hreal φ.property)).of_norm

/-- The extension is real and nonpositive at every real FL⁴ source. -/
theorem real_renormalizedHamiltonian_nonpos (φ : realTypeSourceSubmodule 4) :
    (A.renormalizedHamiltonian φ.val).re ≤ 0 ∧ (A.renormalizedHamiltonian φ.val).im = 0 := by
  rw [A.real_renormalizedHamiltonian_eq_real_tsum φ]
  simp only [ofReal_re,ofReal_im,and_true]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (tsum_nonneg (fun n => (A.real_moment_nonneg φ n 3).1))

/-- Any open gap makes the extension strictly negative. -/
theorem real_renormalizedHamiltonian_neg_of_open_gap (φ : realTypeSourceSubmodule 4) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) : (A.renormalizedHamiltonian φ.val).re < 0 := by
  rw [A.real_renormalizedHamiltonian_eq_real_tsum φ,ofReal_re]
  exact mul_neg_of_neg_of_pos (by norm_num)
    ((A.summable_real_cubic_moments φ).tsum_pos (fun k => (A.real_moment_nonneg φ k 3).1) n
      (A.real_odd_moment_pos φ n 1 hn))

/-- The only real zero of the extension is the zero potential. -/
theorem real_renormalizedHamiltonian_eq_zero_iff (φ : realTypeSourceSubmodule 4) :
    A.renormalizedHamiltonian φ.val = 0 ↔ φ = 0 := by
  rw [← real_source_all_gaps_closed_iff_zero (by simp) (by norm_num) φ]
  constructor
  · intro hz n
    by_contra hn
    have hneg := A.real_renormalizedHamiltonian_neg_of_open_gap φ n hn
    simp only [hz,zero_re,lt_self_iff_false] at hneg
  · intro hg
    have hz (n : ℤ) : A.moment n 3 φ.val = 0 :=
      A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n (hg n) 3
    simp only [renormalizedHamiltonian,hz,tsum_zero,mul_zero]

/-- Analyticity, absolute convergence, and locally uniform convergence
hold on one connected neighborhood of the full real source locus. -/
theorem exists_renormalizedHamiltonian_analytic :
    ∃ U : Set (CoeffPair 4), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 4 ⊆ U ∧ U ⊆ A.domain ∧
      AnalyticOnNhd ℂ A.renormalizedHamiltonian U ∧
      (∀ ψ ∈ U, Summable (fun n => ‖A.moment n 3 ψ‖)) ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) ψ => -(4/3:ℂ)*(∑ n ∈ Finset.Icc (-(N:ℤ)) N, A.moment n 3 ψ))
        A.renormalizedHamiltonian atTop U := by
  obtain ⟨U,hU,hconn,hreal,hsub,hcoeff,ha,hs⟩ := A.exists_cubicSequence_analytic
  have heq (ψ : CoeffPair 4) (hψ : ψ ∈ U) :
      -(4/3:ℂ)*(lp.tsumCLM ℂ ℤ ℂ) (A.cubicSequence ψ) = A.renormalizedHamiltonian ψ := by
    change -(4/3:ℂ)*(∑' n, A.cubicSequence ψ n) = _
    simp only [hcoeff ψ hψ,renormalizedHamiltonian]
  have hsum := Coeff.tendstoLocallyUniformlyOn_sums_of_continuousOn A.cubicSequence U ha.continuousOn
  have hscale : UniformContinuous (fun z : ℂ => -(4/3:ℂ)*z) :=
    ((-(4/3:ℂ)) • ContinuousLinearMap.id ℂ ℂ).uniformContinuous
  have hconv := hscale.comp_tendstoLocallyUniformlyOn hsum
  refine ⟨U,hU,hconn,hreal,hsub,?_,hs,?_⟩
  · intro ψ hψ
    have han : AnalyticAt ℂ (fun χ => -(4/3:ℂ)*(lp.tsumCLM ℂ ℤ ℂ) (A.cubicSequence χ)) ψ :=
      analyticAt_const.mul (((lp.tsumCLM ℂ ℤ ℂ).analyticAt (A.cubicSequence ψ)).comp (ha ψ hψ))
    exact han.congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hψ) (fun χ hχ => heq χ hχ))
  · rw [Metric.tendstoLocallyUniformlyOn_iff] at hconv ⊢
    intro ε hε ψ hψ
    obtain ⟨V,hV,hb⟩ := hconv ε hε ψ hψ
    refine ⟨V ∩ U,inter_mem hV self_mem_nhdsWithin,hb.mono ?_⟩
    intro N hN χ hχ
    simpa only [Function.comp_def,hcoeff χ hχ.2,renormalizedHamiltonian] using hN χ hχ.1

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
