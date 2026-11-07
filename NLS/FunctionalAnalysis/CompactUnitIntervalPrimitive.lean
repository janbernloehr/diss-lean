import NLS.FunctionalAnalysis.CompactSmoothPrimitive

/-! # Zero-integral test primitives stay strictly inside the original interval -/
noncomputable section
open Set MeasureTheory Function
open scoped ContDiff
namespace NLS.FunctionalAnalysis

theorem exists_compact_unitInterval_primitive
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0:ℝ) 1) (hi : (∫ x : ℝ, f x)=0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ Ioo (0:ℝ) 1 ∧ ∀ x, HasDerivAt F (f x) x := by
  let K := tsupport f ∪ {(1/2:ℝ)}
  have hK : IsCompact K := hc.union isCompact_singleton
  have hne : K.Nonempty := ⟨1/2,Or.inr (mem_singleton _)⟩
  obtain ⟨lo,hloK,hlo⟩ := hK.exists_isLeast hne
  obtain ⟨hi',hhiK,hhi⟩ := hK.exists_isGreatest hne
  have hKI : K ⊆ Ioo (0:ℝ) 1 := by
    intro x hx
    rcases hx with hx | hx
    · exact hs hx
    · simpa only [mem_singleton_iff.mp hx] using (show (1/2:ℝ) ∈ Ioo 0 1 by norm_num)
  let a := lo/2
  let b := (hi'+1)/2
  have ha : 0 < a ∧ a < lo := by dsimp [a]; have := (hKI hloK).1; constructor <;> linarith
  have hb : hi' < b ∧ b < 1 := by dsimp [b]; have := (hKI hhiK).2; constructor <;> linarith
  have hsupp : support f ⊆ Ioo a b := by
    intro x hx
    exact ⟨ha.2.trans_le (hlo (Or.inl (subset_tsupport f hx))),
      (hhi (Or.inl (subset_tsupport f hx))).trans_lt hb.1⟩
  let F := fun x => ∫ t in a..x, f t
  have hd (x : ℝ) : HasDerivAt F (f x) x := (hf.continuous.integral_hasStrictDerivAt a x).hasDerivAt
  have hFc : ContDiff ℝ ∞ F := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hd x).differentiableAt,?_⟩
    rw [show deriv F=f from funext fun x => (hd x).deriv]
    exact hf
  have hFS : support F ⊆ Icc a b := by
    intro x hx
    by_contra hn
    have he : x < a ∨ b < x := by simpa only [mem_Icc,not_and_or,not_le] using hn
    apply hx
    rcases he with he | he
    · change (∫ t in a..x, f t)=0
      calc
        _ = ∫ _ in a..x, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ≤ a := (show t ∈ Icc x a from by simpa only [uIcc_of_ge he.le] using ht).2
          by_contra hft
          have := (hsupp hft).1
          linarith
        _ = 0 := intervalIntegral.integral_zero
    · change (∫ t in a..x, f t)=0
      rw [intervalIntegral.integral_eq_integral_of_support_subset,hi]
      intro t ht
      exact ⟨(hsupp ht).1,(hsupp ht).2.le.trans he.le⟩
  refine ⟨F,hFc,HasCompactSupport.of_support_subset_isCompact isCompact_Icc hFS,?_,hd⟩
  intro x hx
  have ht : x ∈ Icc a b := closure_minimal hFS isClosed_Icc hx
  exact ⟨ha.1.trans_le ht.1,ht.2.trans_lt hb.2⟩

end NLS.FunctionalAnalysis
