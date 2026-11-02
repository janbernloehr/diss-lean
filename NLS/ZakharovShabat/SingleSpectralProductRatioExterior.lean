import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles

/-!
# Exterior bounds for ratios of single-root products

Two `ℓᵖ` root products have the same free sine normalization.
Their relative errors below one half give a nonzero denominator and
a common bound of four for their quotient on the separated exterior.
Both deleted and full product interpolation arguments use this bound.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Ratios of two displaced single-root products are uniformly bounded
on the large separated exterior, where the denominator is nonzero. -/
theorem exists_threshold_entireSingleSpectralProduct_ratio_le_four
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξlp : Memℓp (fun m => ξ m-(Real.pi:ℂ)*m) p)
    (hηlp : Memℓp (fun m => η m-(Real.pi:ℂ)*m) p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z-(Real.pi:ℂ)*m‖) →
      entireSingleSpectralProduct η z ≠ 0 ∧
      ‖entireSingleSpectralProduct ξ z / entireSingleSpectralProduct η z‖ ≤ 4 := by
  obtain ⟨Rξ,hRξ⟩ := exists_threshold_entireSingleSpectralProduct_div_free_close
    hp ξ hξlp hr hrπ (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨Rη,hRη⟩ := exists_threshold_entireSingleSpectralProduct_div_free_close
    hp η hηlp hr hrπ (by norm_num : (0:ℝ) < 1/2)
  refine ⟨max Rξ Rη,?_⟩
  intro z hz hsep
  let d : ℂ := -2*sin z
  let J : ℂ := entireSingleSpectralProduct ξ z
  let G : ℂ := entireSingleSpectralProduct η z
  have hd : d ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hsep))
  have hdNorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hA : ‖J/d-1‖ ≤ (1:ℝ)/2 := hRξ z ((le_max_left _ _).trans hz) hsep
  have hB : ‖G/d-1‖ ≤ (1:ℝ)/2 := hRη z ((le_max_right _ _).trans hz) hsep
  have hAnorm : ‖J/d‖ ≤ 2 := by
    calc
      ‖J/d‖ = ‖(J/d-1)+1‖ := by congr 1; ring
      _ ≤ ‖J/d-1‖+‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hBnorm : (1:ℝ)/2 ≤ ‖G/d‖ := by
    have htri := norm_add_le (G/d) (1-G/d)
    have heq : (1:ℂ) = G/d+(1-G/d) := by ring
    rw [← heq] at htri
    rw [norm_one,norm_sub_rev] at htri
    linarith
  have hG : G ≠ 0 := by
    intro he
    rw [he,zero_div,norm_zero] at hBnorm
    norm_num at hBnorm
  have hGnorm : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hJle : ‖J‖ ≤ 2*‖d‖ := by
    rw [norm_div] at hAnorm
    exact (div_le_iff₀ hdNorm).mp hAnorm
  have hdle : ‖d‖ ≤ 2*‖G‖ := by
    rw [norm_div] at hBnorm
    have h := (le_div_iff₀ hdNorm).mp hBnorm
    linarith
  refine ⟨hG,?_⟩
  change ‖J/G‖ ≤ 4
  rw [norm_div]
  apply (div_le_iff₀ hGnorm).mpr
  linarith

/-- Ratios of two free-normalized l^p root products tend to one along
every separated path escaping to infinity. -/
theorem tendsto_entireSingleSpectralProduct_ratio_of_separated
    {p : ENNReal} [Fact (1 ≤ p)] {T : Type*} {l : Filter T}
    (hp : p ≠ ⊤) (xi eta : ℤ → ℂ)
    (hxi : Memℓp (fun j => xi j-(Real.pi : ℂ)*j) p)
    (heta : Memℓp (fun j => eta j-(Real.pi : ℂ)*j) p)
    (z : T → ℂ) (hz : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (hsep : ∀ i (j : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*j‖) :
    Tendsto (fun i => entireSingleSpectralProduct xi (z i)/entireSingleSpectralProduct eta (z i)) l (𝓝 1) := by
  have hx := tendsto_entireSingleSpectralProduct_div_free_of_separated hp xi hxi z hz hr hrpi hsep
  have he := tendsto_entireSingleSpectralProduct_div_free_of_separated hp eta heta z hz hr hrpi hsep
  have hh := hx.div he (by norm_num : (1 : ℂ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [] with i
  have hf : -2*sin (z i) ≠ 0 := mul_ne_zero (by norm_num)
    (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr (hsep i)))
  exact div_div_div_cancel_right₀ hf _ _

end NLS.ZakharovShabat
