import NLS.SequenceSpaces.Truncation
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Locally uniform summation of continuous ℓ¹-valued maps

The norms of symmetric truncation tails decrease continuously to zero.
Dini's local theorem gives local uniform convergence, hence uniform
convergence on every compact subset of the parameter domain.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- Summing a truncation is the literal finite coefficient sum. -/
theorem tsum_truncate_one (s : Finset ℤ) (a : Coeff 1) :
    (∑' n : ℤ, truncate s a n) = ∑ n ∈ s, a n := by
  rw [tsum_eq_sum (s := s) (fun n hn => by simp [truncate_apply,hn])]
  exact Finset.sum_congr rfl (fun n hn => by simp only [truncate_apply,if_pos hn])

/-- Continuous ℓ¹-valued families have locally uniformly convergent symmetric sums. -/
theorem tendstoLocallyUniformlyOn_sums_of_continuousOn {X : Type*} [TopologicalSpace X]
    (f : X → Coeff 1) (S : Set X) (hf : ContinuousOn f S) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) x => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, f x n)
      (fun x => ∑' n : ℤ, f x n) atTop S := by
  let t (N : ℕ) (x : X) := ‖f x-truncate (Finset.Icc (-(N:ℤ)) N) (f x)‖
  have hcont (N : ℕ) : ContinuousOn (t N) S :=
    (hf.sub ((truncateCLM (Finset.Icc (-(N:ℤ)) N)).continuous.comp_continuousOn hf)).norm
  have hanti (x : X) : Antitone (fun N => t N x) := by
    intro i j hij
    apply lp.norm_mono (by norm_num : (1:ℝ≥0∞) ≠ 0)
    intro n
    have hsub : Finset.Icc (-(i:ℤ)) i ⊆ Finset.Icc (-(j:ℤ)) j := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      constructor <;> omega
    by_cases hi : n ∈ Finset.Icc (-(i:ℤ)) i
    · simp only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_pos hi,if_pos (hsub hi),sub_self,le_refl]
    · by_cases hj : n ∈ Finset.Icc (-(j:ℤ)) j
      · simp only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_pos hj,if_neg hi,sub_self,norm_zero,sub_zero]
        exact norm_nonneg _
      · simp only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_neg hi,if_neg hj,le_refl]
  have ht (x : X) : Tendsto (fun N => t N x) atTop (𝓝 0) := by
    simpa only [t,Function.comp_def,sub_self,norm_zero] using!
      ((tendsto_const_nhds (x := f x)).sub ((tendsto_truncate (by simp) (f x)).comp Finset.tendsto_Icc_neg)).norm
  have hlocal := Antitone.tendstoLocallyUniformlyOn_of_forall_tendsto hcont
    (fun x _ => hanti x) continuousOn_const (fun x _ => ht x)
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hlocal ⊢
  intro ε hε x hx
  obtain ⟨V,hV,hbound⟩ := hlocal ε hε x hx
  refine ⟨V,hV,hbound.mono ?_⟩
  intro N hN y hy
  have hsum : (∑' n : ℤ, f y n) - (∑ n ∈ Finset.Icc (-(N:ℤ)) N, f y n) =
      ∑' n : ℤ, (f y-truncate (Finset.Icc (-(N:ℤ)) N) (f y)) n := by
    rw [← tsum_truncate_one]
    exact ((lp.tsumCLM ℂ ℤ ℂ).map_sub _ _).symm
  rw [dist_eq_norm,hsum]
  exact (lp.norm_tsum_le _).trans_lt (by simpa only [dist_zero_left,Real.norm_eq_abs,t,abs_norm] using hN y hy)

/-- The same sums converge uniformly on each compact parameter set. -/
theorem tendstoUniformlyOn_sums_of_isCompact {X : Type*} [TopologicalSpace X]
    (f : X → Coeff 1) (K : Set X) (hK : IsCompact K) (hf : ContinuousOn f K) :
    TendstoUniformlyOn
      (fun (N : ℕ) x => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, f x n)
      (fun x => ∑' n : ℤ, f x n) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (tendstoLocallyUniformlyOn_sums_of_continuousOn f K hf)

end NLS.Coeff
