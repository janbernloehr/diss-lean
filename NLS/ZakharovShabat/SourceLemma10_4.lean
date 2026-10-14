import NLS.ZakharovShabat.SourceStandardRootGapSideEndpoint

/-!
# Corrected Lemma 10.4: one sharp maximum bound for both gap sides

The denominator is the side trace of w_n on G_n. One attained maximum
controls every stopping point on both sides, including the branch points.
The supremum is a literal real supremum of these integral norms.
-/

noncomputable section
open Set Complex Filter MeasureTheory
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All normalized endpoint integral norms on the two closed sides of the actual gap. -/
def sourceStandardRootSideIntegralNorms (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (f : ℂ → ℂ) : Set ℝ :=
  {r | ∃ t ∈ Icc (-1 : ℝ) 1, ∃ upper : Bool,
    r = ‖sourceStandardRootSideIntegral hp hp1 ψ n f (-1) t upper/(Real.pi:ℂ)‖}

/-- Corrected Lemma 10.4, with one attained maximum chosen before all endpoints and both sides. -/
theorem sourceLemma10_4 (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sourcePeriodicSegment hp hp1 ψ n)) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ n,
      (∀ w ∈ sourcePeriodicSegment hp hp1 ψ n, ‖f w‖ ≤ ‖f z‖) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, ∀ upper : Bool,
        ‖sourceStandardRootSideIntegral hp hp1 ψ n f (-1) t upper/(Real.pi:ℂ)‖ ≤ ‖f z‖) ∧
      sSup (sourceStandardRootSideIntegralNorms hp hp1 ψ n f) ≤ ‖f z‖ := by
  have hseg := sourceStandardRoot_gapSegment_eq_periodicSegment hp hp1 ψ n
  obtain ⟨z,hz,hm,hb⟩ := sourceStandardRoot_gapSidePathIntegral_uniform_max_bound hp hp1 ψ n hg f
    (hseg ▸ hf)
  refine ⟨z,hseg ▸ hz,fun w hw => hm w (hseg.symm ▸ hw),fun t ht upper => hb t ht.1 ht.2 upper,?_⟩
  apply csSup_le
  · exact ⟨_,(-1),⟨le_rfl,by norm_num⟩,true,rfl⟩
  · rintro r ⟨t,ht,upper,rfl⟩
    exact hb t ht.1 ht.2 upper

/-- The same estimate written entirely with real suprema on the actual sets of values. -/
theorem sourceLemma10_4_sup (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sourcePeriodicSegment hp hp1 ψ n)) :
    sSup (sourceStandardRootSideIntegralNorms hp hp1 ψ n f) ≤
      sSup ((fun z => ‖f z‖) '' sourcePeriodicSegment hp hp1 ψ n) := by
  obtain ⟨z,hz,hm,_,hs⟩ := sourceLemma10_4 hp hp1 ψ n hg f hf
  refine hs.trans (le_csSup ?_ ⟨z,hz,rfl⟩)
  refine ⟨‖f z‖,?_⟩
  rintro r ⟨w,hw,rfl⟩
  exact hm w hw

/-- Stopping at the left endpoint gives zero on either side, for arbitrary data. -/
theorem sourceStandardRootSideIntegral_left (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (f : ℂ → ℂ) (upper : Bool) :
    sourceStandardRootSideIntegral hp hp1 ψ n f (-1) (-1) upper = 0 := by
  exact intervalIntegral.integral_same

/-- Opposite side traces give opposite endpoint integrals. -/
theorem sourceStandardRootSideIntegral_lower_eq_neg_upper (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (a b : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) :
    sourceStandardRootSideIntegral hp hp1 ψ n f a b false =
      -sourceStandardRootSideIntegral hp hp1 ψ n f a b true := by
  rw [sourceStandardRootSideIntegral_eq_weighted hp hp1 ψ n hg f a b ha hb false,
    sourceStandardRootSideIntegral_eq_weighted hp hp1 ψ n hg f a b ha hb true]
  simp

/-- Constant data have the exact full-side value, with the upper/lower sign fixed. -/
theorem sourceStandardRootSideIntegral_const_full (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (c : ℂ) (upper : Bool) :
    sourceStandardRootSideIntegral hp hp1 ψ n (fun _ => c) (-1) 1 upper/(Real.pi:ℂ) =
      (if upper then Complex.I else -Complex.I)*c := by
  rw [sourceStandardRootSideIntegral_eq_boundary hp hp1 ψ n hg (fun _ => c) 1 (by norm_num) upper,
    gapSideBoundaryIntegral_eq_primitive _ _ (fun _ => c) 1 (div_ne_zero hg (by norm_num)) upper]
  simp only [gapSidePrimitive,Real.arccos_one,intervalIntegral.integral_const,sub_zero,
    Complex.real_smul]
  field_simp

/-- Each full side attains the unit bound for constant data. -/
theorem sourceStandardRootSideIntegral_const_full_norm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (c : ℂ) (upper : Bool) :
    ‖sourceStandardRootSideIntegral hp hp1 ψ n (fun _ => c) (-1) 1 upper/(Real.pi:ℂ)‖ = ‖c‖ := by
  rw [sourceStandardRootSideIntegral_const_full hp hp1 ψ n hg c upper]
  cases upper <;> simp

/-- The full supremum equals the data norm for constants, so the factor one is sharp. -/
theorem sourceLemma10_4_const_sharp (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (c : ℂ) :
    sSup (sourceStandardRootSideIntegralNorms hp hp1 ψ n (fun _ => c)) = ‖c‖ := by
  obtain ⟨z,_,_,hb,hs⟩ := sourceLemma10_4 hp hp1 ψ n hg (fun _ => c) continuousOn_const
  apply le_antisymm hs
  apply le_csSup
  · refine ⟨‖c‖,?_⟩
    rintro r ⟨t,ht,upper,rfl⟩
    exact hb t ht upper
  · exact ⟨1,⟨by norm_num,le_rfl⟩,true,
      (sourceStandardRootSideIntegral_const_full_norm hp hp1 ψ n hg c true).symm⟩

end NLS.ZakharovShabat
