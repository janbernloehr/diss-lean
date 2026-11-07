import NLS.ZakharovShabat.SourcePsiOriginalIndexRatio

/-! Original index ratios tend to one along any separated moving row.
The root input and evaluation point may vary throughout the placed domain. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.tendsto_indexRatio_of_spacing
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (a : ℕ → Coeff p) (ha : ∀ j, a j ∈ sourcePsiOriginalRootPlacement (p := p) D)
    (k m : ℕ → ℤ) (z : ℕ → ℂ) (hz : ∀ j, z j ∈ D (m j))
    (hspacing : Tendsto (fun j => ‖((k j-m j:ℤ):ℂ)‖) atTop atTop) :
    Tendsto (fun j => sourcePsiOriginalIndexRatio (k j) (m j) (a j) (z j)) atTop (𝓝 1) := by
  obtain ⟨K,_,hbound⟩ := hD.original_indexRatio_uniform_bound
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ (hspacing.const_div_atTop K)
  filter_upwards [hspacing.eventually (eventually_ge_atTop (1:ℝ))] with j hj
  have hmk : m j ≠ k j := by
    intro he
    simp only [he,sub_self,Int.cast_zero,norm_zero] at hj
    norm_num at hj
  exact hbound (a j) (ha j) (k j) (m j) hmk (z j) (hz j)

theorem tendsto_norm_fixed_sub_positive_index (k : ℤ) :
    Tendsto (fun j : ℕ => ‖((k-((j:ℤ)+1):ℤ):ℂ)‖) atTop atTop := by
  have h : Tendsto (fun j : ℕ => (j:ℝ)+1-(k:ℝ)) atTop atTop :=
    by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(k:ℝ))
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply tendsto_atTop_mono (f := fun j : ℕ => (j:ℝ)+1-(k:ℝ)) ?_ h
  intro j
  rw [Complex.norm_intCast,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one]
  have hb := neg_le_abs ((k:ℝ)-((j:ℝ)+1))
  linarith

theorem tendsto_norm_negative_positive_index_spacing :
    Tendsto (fun j : ℕ => ‖((-((j:ℤ)+1)-((j:ℤ)+1):ℤ):ℂ)‖) atTop atTop := by
  apply tendsto_atTop_mono (f := fun j : ℕ => (j:ℝ)) ?_ tendsto_natCast_atTop_atTop
  intro j
  rw [Complex.norm_intCast,Int.cast_sub,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one]
  have h := neg_le_abs (-((j:ℝ)+1)-((j:ℝ)+1))
  linarith

end NLS.ZakharovShabat
