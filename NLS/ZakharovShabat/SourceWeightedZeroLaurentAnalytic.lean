import NLS.ZakharovShabat.SourceWeightedZeroLaurentBound
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Actual analytic weighted l1 Laurent-level-zero sequences

The common locally uniform weighted norm bound upgrades coordinate
analyticity to Banach analyticity. Every noncentral signed coordinate
is the actual Laurent action, with only the singular central index set
to zero. No finite-gap or open-action hypothesis is imposed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def sourceWeightedZeroLaurentSequence (q : ℤ → ℝ) (L : E →L[ℂ] CoeffPair 2) (b : E) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun n => if n = 0 then 0 else
    (q n : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (L b))

theorem exists_local_sourceWeightedZeroLaurentSequence_analytic
    (w : SpectralWeight) (q : ℤ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hqw : ∀ n : ℤ, q n/(1+|(n : ℝ)|) ≤ (w (2*n))^2)
    (L : E →L[ℂ] CoeffPair 2) (S : E →L[ℂ] WeightedCoeffPair w.toWeight 2)
    (hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b))
    (a : E) (ha : L a ∈ realDiagonalSourceLocus 2) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧
      (∀ b ∈ U, ∀ n : ℤ, sourceWeightedZeroLaurentSequence q L b n =
        if n = 0 then 0 else (q n : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (L b)) ∧
      AnalyticOnNhd ℂ (sourceWeightedZeroLaurentSequence q L) U := by
  obtain ⟨U,hU,haU,hUD,C,hbound⟩ := exists_local_sourceWeightedZeroLaurent_bound w q hq hqw L S hSL a ha
  have he (b : E) (hb : b ∈ U) (n : ℤ) : sourceWeightedZeroLaurentSequence q L b n =
      if n = 0 then 0 else (q n : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (L b) := by
    obtain ⟨g,hg,_⟩ := hbound b hb
    rw [sourceWeightedZeroLaurentSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]
    exact hg n
  refine ⟨U,hU,haU,he,Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU ?_ C ?_⟩
  · intro n b hb
    have hf : AnalyticAt ℂ (fun c : E => if n = 0 then 0 else
        (q n : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (L c)) b := by
      by_cases hn : n = 0
      · simp only [if_pos hn]
        exact analyticAt_const
      · simp only [if_neg hn]
        exact analyticAt_const.mul ((analyticOnNhd_sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 hn
          (L b) (hUD hb)).comp (L.analyticAt b))
    apply hf.congr
    filter_upwards [hU.mem_nhds hb] with c hc
    exact (he c hc n).symm
  · intro b hb
    obtain ⟨g,hg,hgn⟩ := hbound b hb
    rwa [sourceWeightedZeroLaurentSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]

end NLS.ZakharovShabat
