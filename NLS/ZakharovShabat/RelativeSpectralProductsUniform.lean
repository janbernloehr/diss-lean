import NLS.ZakharovShabat.RelativeSpectralProducts
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Algebra

/-!
# Locally uniform relative spectral products

A ball of half the free spectral gap admits a common summable majorant.
The relative products converge locally uniformly in the spectral parameter,
including at perturbed roots, and their limits are holomorphic off the free lattice.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Free denominators at the center are controlled throughout a half-gap ball. -/
theorem free_denominator_norm_le_twice (z₀ z : ℂ)
    (hz : z ∈ Metric.closedBall z₀ (freeGap z₀ / 2)) (n : ℤ) :
    ‖z₀-(Real.pi : ℂ)*n‖ ≤ 2*‖z-(Real.pi : ℂ)*n‖ := by
  have hd : ‖z-z₀‖ ≤ freeGap z₀/2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have ht := norm_sub_le (z₀-z) ((Real.pi : ℂ)*n-z)
  have hg := freeGap_le z₀ n
  rw [sub_sub_sub_cancel_right, norm_sub_rev z₀ z, norm_sub_rev ((Real.pi : ℂ)*n) z] at ht
  linarith

/-- The entire closed half-gap ball avoids the free lattice. -/
theorem closedBall_half_freeGap_subset (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice) :
    Metric.closedBall z₀ (freeGap z₀/2) ⊆ freeLatticeᶜ := by
  intro z hz
  rintro ⟨n,hn⟩
  have h := free_denominator_norm_le_twice z₀ z hz n
  change (Real.pi : ℂ)*n = z at hn
  rw [← hn, sub_self, norm_zero, mul_zero] at h
  exact (norm_pos_iff.mpr (free_denominator_ne_zero hz₀ n)).not_ge h

/-- A relative displacement has a common summable majorant on the half-gap ball. -/
theorem norm_relativeDisplacement_le_twice (ξ : ℤ → ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice)
    (z : ℂ) (hz : z ∈ Metric.closedBall z₀ (freeGap z₀/2)) (n : ℤ) :
    ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖ ≤
      2*‖(ξ n-(Real.pi : ℂ)*n)/(z₀-(Real.pi : ℂ)*n)‖ := by
  have hd₀ := norm_pos_iff.mpr (free_denominator_ne_zero hz₀ n)
  have hd := norm_pos_iff.mpr (free_denominator_ne_zero (closedBall_half_freeGap_subset z₀ hz₀ hz) n)
  rw [norm_div, norm_div]
  apply (div_le_iff₀ hd).mpr
  have hb := free_denominator_norm_le_twice z₀ z hz n
  have hm := mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg (ξ n-(Real.pi : ℂ)*n)) hd₀.le)
  field_simp at hm ⊢
  nlinarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unordered single-sequence products converge locally uniformly off the free lattice. -/
theorem hasProdLocallyUniformlyOn_spectralRelativeFactor (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    HasProdLocallyUniformlyOn (fun n z => spectralRelativeFactor ξ z n)
      (fun z => ∏' n, spectralRelativeFactor ξ z n) freeLatticeᶜ := by
  apply hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z₀ hz₀
  let K := Metric.closedBall z₀ (freeGap z₀/2)
  have hK := closedBall_half_freeGap_subset z₀ hz₀
  have hsum := (summable_norm_spectralRelativeDisplacement hp ξ hξ z₀ hz₀).mul_left 2
  have hprod := hsum.hasProdUniformlyOn_one_add (f := fun n z =>
    -((ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n))) (isCompact_closedBall z₀ (freeGap z₀/2))
    (Filter.Eventually.of_forall (fun n z hz => by
      simpa only [norm_neg] using norm_relativeDisplacement_le_twice ξ z₀ hz₀ z hz n))
    (fun n => (continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz => free_denominator_ne_zero (hK hz) n)).neg)
  refine ⟨K,nhdsWithin_le_nhds (Metric.closedBall_mem_nhds _ (half_pos (freeGap_pos hz₀))),?_⟩
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hprod ⊢
  apply (hprod.congr ?_).congr_right ?_
  · filter_upwards with s z hz
    apply Finset.prod_congr rfl
    intro n _
    exact (spectralRelativeFactor_eq ξ z (hK hz) n).symm
  · intro z hz
    apply tprod_congr
    intro n
    exact (spectralRelativeFactor_eq ξ z (hK hz) n).symm

/-- Each relative factor is holomorphic throughout the off-lattice domain. -/
theorem differentiableOn_spectralRelativeFactor (ξ : ℤ → ℂ) (n : ℤ) :
    DifferentiableOn ℂ (fun z => spectralRelativeFactor ξ z n) freeLatticeᶜ := by
  apply ((differentiableOn_const (ξ n)).sub differentiableOn_id).div
    ((differentiableOn_const ((Real.pi : ℂ)*n)).sub differentiableOn_id)
  intro z hz
  exact sub_ne_zero.mpr (sub_ne_zero.mp (free_denominator_ne_zero hz n)).symm

/-- The single relative product is holomorphic, including at its perturbed zeros. -/
theorem differentiableOn_spectralRelativeProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    DifferentiableOn ℂ (fun z => ∏' n, spectralRelativeFactor ξ z n) freeLatticeᶜ := by
  apply (hasProdLocallyUniformlyOn_spectralRelativeFactor hp ξ hξ).differentiableOn
    (Filter.Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd
      (fun n _ => differentiableOn_spectralRelativeFactor ξ n))) isClosed_freeLattice.isOpen_compl

/-- Unordered paired products converge locally uniformly, with no nonvanishing condition. -/
theorem hasProdLocallyUniformlyOn_spectralRelativePair (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    HasProdLocallyUniformlyOn (fun n z => spectralRelativeFactor ξ z n * spectralRelativeFactor η z n)
      (spectralRelativePairProduct ξ η) freeLatticeᶜ := by
  have h := (hasProdLocallyUniformlyOn_spectralRelativeFactor hp ξ hξ).mul₀
    (hasProdLocallyUniformlyOn_spectralRelativeFactor hp η hη)
    (differentiableOn_spectralRelativeProduct hp ξ hξ).continuousOn
    (differentiableOn_spectralRelativeProduct hp η hη).continuousOn
  apply (h.congr (fun s z _ => (Finset.prod_mul_distrib).symm)).congr_right
  intro z hz
  exact ((multipliable_spectralRelativeFactor hp ξ hξ z hz).tprod_mul
    (multipliable_spectralRelativeFactor hp η hη z hz)).symm

/-- The literal symmetric relative cutoffs inherit locally uniform convergence. -/
theorem tendstoLocallyUniformlyOn_spectralRelativePairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N : ℕ => fun z => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      spectralRelativeFactor ξ z n * spectralRelativeFactor η z n)
      (spectralRelativePairProduct ξ η) atTop freeLatticeᶜ := by
  intro v hv z hz
  obtain ⟨t,ht,he⟩ := hasProdLocallyUniformlyOn_spectralRelativePair hp ξ η hξ hη v hv z hz
  exact ⟨t,ht,Finset.tendsto_Icc_neg.eventually he⟩

/-- The paired relative product is holomorphic throughout the off-lattice domain. -/
theorem differentiableOn_spectralRelativePairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    DifferentiableOn ℂ (spectralRelativePairProduct ξ η) freeLatticeᶜ := by
  apply (hasProdLocallyUniformlyOn_spectralRelativePair hp ξ η hξ hη).differentiableOn
    (Filter.Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd
      (fun n _ => (differentiableOn_spectralRelativeFactor ξ n).mul
        (differentiableOn_spectralRelativeFactor η n)))) isClosed_freeLattice.isOpen_compl

end NLS.ZakharovShabat
