import NLS.SequenceSpaces.FourierRealZeroCoordinates

/-! Dense derivative range from actual raw single-mode preimages in
the unchanged weighted complex zero-mode target. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem zeroModeProjection_surjective (w : Weight) : Function.Surjective (zeroModeProjection (p := p) w) := by
  intro b
  exact ⟨b.val,Subtype.ext (zeroModeProjection_coe w b.val b.property)⟩

theorem denseRange_zeroModeProjection_ofFinsupp (w : Weight) (hp : p ≠ ⊤) :
    DenseRange (fun a : ℤ →₀ ℂ => zeroModeProjection (p := p) w (ofFinsupp w p a)) :=
  (zeroModeProjection_surjective (p := p) w).denseRange.comp (denseRange_ofFinsupp w p hp)
    (zeroModeProjection (p := p) w).continuous

theorem ofFinsupp_eq_sum_weighted_single (w : Weight) (a : ℤ →₀ ℂ) :
    ofFinsupp w p a=∑ k ∈ a.support, a k • single w k 1 := by
  apply Subtype.ext
  funext j
  change a j=(evalCLM w p j) (∑ k ∈ a.support, a k • single w k 1)
  rw [map_sum]
  simp only [map_smul,evalCLM_apply,single_val,Pi.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]
  by_cases hj : j ∈ a.support
  · simp only [Finset.sum_ite_eq,hj,ite_true]
  · simp only [Finset.sum_ite_eq,hj,ite_false,Finsupp.notMem_support_iff.mp hj]

theorem denseRange_of_zeroModeSingle_mem_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : Weight) (hp : p ≠ ⊤) (T : E →L[ℂ] zeroModeSubmodule w p)
    (hT : ∀ k : ℤ, ∀ hk : k ≠ 0, zeroModeSingle w k hk 1 ∈ T.range) : DenseRange T := by
  let R := T.range
  have hsingle (k : ℤ) : zeroModeProjection (p := p) w (single w k 1) ∈ R := by
    by_cases hk : k=0
    · subst k
      have he : zeroModeProjection (p := p) w (single w 0 1)=0 := by
        apply Subtype.ext
        apply Subtype.ext
        funext j
        change (eraseZeroModeCLM w (single w 0 1)).val j=0
        rw [eraseZeroModeCLM_apply,single_val,Pi.single_apply]
        by_cases hj : j=0 <;> simp only [hj,ite_true,ite_false]
      rw [he]
      exact R.zero_mem
    · have he : zeroModeProjection (p := p) w (single w k 1)=zeroModeSingle w k hk 1 := by
        apply Subtype.ext
        exact zeroModeProjection_coe w (single w k 1) (by simp only [single_val,Pi.single_apply,if_neg (Ne.symm hk)])
      rw [he]
      exact hT k hk
  have hfinite (a : ℤ →₀ ℂ) : zeroModeProjection (p := p) w (ofFinsupp w p a) ∈ R := by
    rw [ofFinsupp_eq_sum_weighted_single,map_sum]
    exact R.sum_mem (fun k _ => by simpa only [map_smul] using R.smul_mem (a k) (hsingle k))
  intro z
  apply closure_mono (t := Set.range T) ?_ (denseRange_zeroModeProjection_ofFinsupp w hp z)
  rintro _ ⟨a,rfl⟩
  exact hfinite a

end NLS.WeightedCoeff
