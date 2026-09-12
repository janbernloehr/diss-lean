import NLS.Fourier.SchwartzMultiplierConvergence

/-!
# Absolutely convergent series of Schwartz functions

A series summable in every Schwartz seminorm has a genuine Schwartz sum and
converges to it in the Schwartz topology. This constructs the needed limit
directly, without assuming a completeness instance for Schwartz space.
-/

noncomputable section
open scoped SchwartzMap ContDiff
namespace NLS.Fourier

variable {ι : Type*} (u : ι → 𝓢(ℝ, ℂ))
  (hs : ∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i)))

private theorem series_fderiv_bound (n : ℕ) (i : ι) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (u i) x‖ ≤ SchwartzMap.seminorm ℂ 0 n (u i) := by
  simpa using (u i).le_seminorm ℂ 0 n x

include hs

private theorem series_contDiff : ContDiff ℝ ∞ (fun x : ℝ => ∑' i, u i x) :=
  contDiff_tsum (fun i => (u i).smooth ⊤) (fun n _ => hs 0 n)
    (fun n i x _ => series_fderiv_bound u n i x)

private theorem series_iteratedFDeriv (n : ℕ) (x : ℝ) :
    iteratedFDeriv ℝ n (fun y : ℝ => ∑' i, u i y) x = ∑' i, iteratedFDeriv ℝ n (u i) x :=
  iteratedFDeriv_tsum_apply (fun i => (u i).smooth ⊤) (fun n _ => hs 0 n)
    (fun n i x _ => series_fderiv_bound u n i x) (by simp) x

private theorem series_hasSum_fderiv (n : ℕ) (x : ℝ) :
    HasSum (fun i => iteratedFDeriv ℝ n (u i) x)
      (iteratedFDeriv ℝ n (fun y : ℝ => ∑' i, u i y) x) := by
  rw [series_iteratedFDeriv u hs]
  exact (Summable.of_norm_bounded (hs 0 n) (fun i => series_fderiv_bound u n i x)).hasSum

private theorem series_decay_bound (k n : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ => ∑' i, u i y) x‖ ≤
      ∑' i, SchwartzMap.seminorm ℂ k n (u i) := by
  have h := ((series_hasSum_fderiv u hs n x).const_smul (‖x‖ ^ k)).norm_le_of_bounded
    (hs k n).hasSum (fun i => ?_)
  · simpa only [norm_smul, norm_pow, norm_norm] using h
  · simpa only [norm_smul, norm_pow, norm_norm] using
      (u i).le_seminorm ℂ k n x

/-- The pointwise sum is a Schwartz function when every seminorm is summable. -/
def schwartzSum : 𝓢(ℝ, ℂ) where
  toFun x := ∑' i, u i x
  smooth' := series_contDiff u hs
  decay' k n := ⟨∑' i, SchwartzMap.seminorm ℂ k n (u i), series_decay_bound u hs k n⟩

@[simp] theorem schwartzSum_apply (x : ℝ) : schwartzSum u hs x = ∑' i, u i x := rfl

/-- Every weighted seminorm of the sum is bounded by the sum of the corresponding seminorms. -/
theorem seminorm_schwartzSum_le (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (schwartzSum u hs) ≤
      ∑' i, SchwartzMap.seminorm ℂ k n (u i) :=
  SchwartzMap.seminorm_le_bound ℂ k n _ (tsum_nonneg (fun _ => apply_nonneg _ _))
    (series_decay_bound u hs k n)

/-- The error after any finite truncation is bounded by the scalar seminorm tail. -/
theorem seminorm_sum_sub_schwartzSum_le (s : Finset ι) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n ((∑ i ∈ s, u i) - schwartzSum u hs) ≤
      (∑' i, SchwartzMap.seminorm ℂ k n (u i)) - ∑ i ∈ s, SchwartzMap.seminorm ℂ k n (u i) := by
  classical
  have hnonneg := (hs k n).sum_le_tsum s (fun i _ => apply_nonneg _ _)
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (sub_nonneg.mpr hnonneg)
  intro x
  have hd := (s.hasSum_iff_compl.mp (series_hasSum_fderiv u hs n x)).const_smul (‖x‖ ^ k)
  have hb := s.hasSum_iff_compl.mp (hs k n).hasSum
  have he := hd.norm_le_of_bounded hb (fun i => ?_)
  · have hsum : (fun x : ℝ => (∑ i ∈ s, u i) x) = fun x => ∑ i ∈ s, u i x := by
      funext x
      exact sum_apply s u x
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n
      ((fun x : ℝ => (∑ i ∈ s, u i) x) - (schwartzSum u hs : ℝ → ℂ)) x‖ ≤ _
    rw [hsum, iteratedFDeriv_sub (ContDiff.sum (fun i _ => (u i).smooth n))
      ((schwartzSum u hs).smooth n)]
    simp only [Pi.sub_apply, iteratedFDeriv_fun_sum_apply (fun i _ => (u i).contDiffAt n)]
    simpa only [norm_smul, norm_pow, norm_norm,
      norm_sub_rev] using! he
  · simpa only [norm_smul, norm_pow, norm_norm] using
      (u i).le_seminorm ℂ k n x

/-- Absolute summability in every seminorm gives convergence in the genuine Schwartz topology. -/
theorem hasSum_schwartzSum : HasSum u (schwartzSum u hs) := by
  apply (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds _ _ |>.mpr
  rintro ⟨k, n⟩ ε hε
  have ht : Filter.Tendsto
      (fun s : Finset ι => (∑' i, SchwartzMap.seminorm ℂ k n (u i)) -
        ∑ i ∈ s, SchwartzMap.seminorm ℂ k n (u i)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := ∑' i, SchwartzMap.seminorm ℂ k n (u i))).sub (hs k n).hasSum
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with s hsε
  exact (seminorm_sum_sub_schwartzSum_le u hs s k n).trans_lt hsε

/-- A seminorm-absolutely-convergent series is summable in Schwartz space. -/
theorem summable_schwartz_of_summable_seminorms : Summable u :=
  ⟨schwartzSum u hs, hasSum_schwartzSum u hs⟩

end NLS.Fourier
