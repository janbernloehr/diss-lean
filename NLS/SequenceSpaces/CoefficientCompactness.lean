import NLS.SequenceSpaces.Truncation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Sequences

/-! # Bounded coefficient limits and Hilbert norm convergence

Bounded sequences have coefficientwise convergent subsequences. At exponent
two, convergence of the norms upgrades coefficient convergence to norm convergence.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- A bounded sequence has a coefficientwise convergent subsequence whose
limit still belongs to the same sequence space. No uniform tail hypothesis is needed. -/
theorem exists_coefficientwise_tendsto_subseq_of_bounded
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : ℕ → Coeff p)
    (hb : Bornology.IsBounded (range a)) :
    ∃ b : Coeff p, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n : ℤ, Tendsto (fun k => a (σ k) n) atTop (𝓝 (b n)) := by
  obtain ⟨B, hB⟩ := hb.exists_norm_le
  let K : Set (ℤ → ℂ) := Set.pi univ (fun _ => closedBall 0 B)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_closedBall 0 B)
  have ha (k : ℕ) : (fun n => a k n) ∈ K := by
    intro n _
    rw [mem_closedBall, dist_zero_right]
    exact (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) (a k) n).trans (hB _ ⟨k, rfl⟩)
  obtain ⟨b, _, σ, hσ, ht⟩ := hK.tendsto_subseq ha
  have hbσ : Bornology.IsBounded (range (a ∘ σ)) := hb.subset (range_comp_subset_range _ _)
  have hm : Memℓp b p := lp.memℓp_of_tendsto hbσ ht
  exact ⟨⟨b, hm⟩, σ, hσ, tendsto_pi_nhds.mp ht⟩

/-- Every finite Fourier projection preserves coefficientwise limits. -/
theorem tendsto_truncate_of_coefficientwise
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {α : Type*} {l : Filter α}
    (a : α → Coeff p) (b : Coeff p)
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n))) (s : Finset ℤ) :
    Tendsto (fun k => truncate s (a k)) l (𝓝 (truncate s b)) := by
  classical
  unfold truncate
  apply tendsto_finsetSum
  intro n _
  exact (lp.isometry_single n).continuous.continuousAt.tendsto.comp (ht n)

/-- Orthogonal Fourier truncation splits the Hilbert energy exactly. -/
theorem norm_sub_truncate_sq (s : Finset ℤ) (a : Coeff 2) :
    ‖a - truncate s a‖^2 = ‖a‖^2 - ‖truncate s a‖^2 := by
  classical
  have he : inner ℂ a (truncate s a) = inner ℂ (truncate s a) (truncate s a) := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    by_cases hn : n ∈ s <;> simp [truncate_apply, hn]
  rw [norm_sub_sq (𝕜 := ℂ), he, inner_self_eq_norm_sq]
  ring

/-- Coefficientwise convergence and convergence of squared norms imply strong
Hilbert convergence. This is the Fourier form of the Radon–Riesz argument. -/
theorem tendsto_of_coefficientwise_of_norm_sq
    {α : Type*} {l : Filter α} (a : α → Coeff 2) (b : Coeff 2)
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n)))
    (hnorm : Tendsto (fun k => ‖a k‖^2) l (𝓝 (‖b‖^2))) :
    Tendsto a l (𝓝 b) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have htr := ((tendsto_const_nhds (x := b)).sub (tendsto_truncate (by simp) b)).norm
  have hsmall : ∀ᶠ s : Finset ℤ in atTop, ‖b - truncate s b‖ < ε/3 := by
    apply htr.eventually (gt_mem_nhds (show ‖b-b‖ < ε/3 by simpa using (by linarith : (0:ℝ) < ε/3)))
  obtain ⟨s, hs⟩ := hsmall.exists
  have hhead := tendsto_truncate_of_coefficientwise a b ht s
  have htail : Tendsto (fun k => ‖a k - truncate s (a k)‖^2) l
      (𝓝 (‖b - truncate s b‖^2)) := by
    simp_rw [norm_sub_truncate_sq]
    exact hnorm.sub (hhead.norm.pow 2)
  have htailSmall : ∀ᶠ k in l, ‖a k - truncate s (a k)‖^2 < (ε/3)^2 :=
    htail.eventually (gt_mem_nhds (by nlinarith [norm_nonneg (b - truncate s b)]))
  have hheadSmall : ∀ᶠ k in l, dist (truncate s (a k)) (truncate s b) < ε/3 :=
    (Metric.tendsto_nhds.mp hhead) (ε/3) (by linarith)
  filter_upwards [htailSmall, hheadSmall] with k htk hhk
  have htk' : dist (a k) (truncate s (a k)) < ε/3 := by
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (a k - truncate s (a k))]
  have hbk : dist (truncate s b) b < ε/3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hs
  have htri := dist_triangle (a k) (truncate s (a k)) b
  have htri' := dist_triangle (truncate s (a k)) (truncate s b) b
  linarith

end NLS.Coeff
