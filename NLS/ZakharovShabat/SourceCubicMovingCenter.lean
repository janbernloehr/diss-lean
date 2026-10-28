import NLS.ZakharovShabat.SourceCubicSmallDiagonal
import NLS.ZakharovShabat.WeightedResonantDiagonalCenter
import NLS.ZakharovShabat.SourceLemma6_7

/-! # The actual real moving diagonal center

Supporting estimates for the unresolved final weighted gap sum on p.44.
The actual counted-root gap still needs comparison with the coefficient sum.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicMovingCenterFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The existing actual diagonal center applied to the original three-mode family. -/
def sourceCubicDiagonalCenter (n : ℤ) (s : ℝ) : ℂ :=
  weightedResonantDiagonalCenter (by simp) SpectralWeight.one (weightedCubicTailFamily n s) n

/-- The quadratic-amplitude majorant tends to zero. -/
theorem sourceCubicDiagonalBound_tendsto (n : ℤ) :
    Tendsto (fun s : ℝ => sourceCubicDiagonalBound n*s^2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous (fun s : ℝ => sourceCubicDiagonalBound n*s^2) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Under explicit smallness, the center solves the original diagonal equation and has quadratic displacement. -/
theorem sourceCubicDiagonalCenter_properties (n : ℤ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hsmall : SourceCubicSmall n s) (hb : sourceCubicDiagonalBound n*s^2 ≤ Real.pi/32) :
    sourceCubicDiagonalCenter n s ∈ refinedResonantDisk n ∧
    sourceCubicDiagonalCenter n s = (Real.pi : ℂ)*n+sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicDiagonalCenter n s) ∧
    ‖sourceCubicDiagonalCenter n s-(Real.pi : ℂ)*n‖ ≤ sourceCubicDiagonalBound n*s^2 := by
  have ha := sourceCubicDiagonal_analytic n n s hsmall
  rw [sourceCubicDiagonal_eq] at ha
  have hd (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖weightedResonantAExtension (by simp) SpectralWeight.one (weightedCubicTailFamily n s) n z‖ ≤ Real.pi/32 := by
    rw [← sourceCubicDiagonal_eq]
    exact (sourceCubicDiagonal_norm_le n n s hs hs1 hsmall z hz).trans hb
  have h := weightedResonantDiagonalCenter_spec (by simp) SpectralWeight.one (weightedCubicTailFamily n s) n ha hd
  change sourceCubicDiagonalCenter n s ∈ _ ∧ _ ∧ _ ∧ _ at h
  have he : sourceCubicDiagonalCenter n s = (Real.pi : ℂ)*n+sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicDiagonalCenter n s) := by
    simpa only [sourceCubicDiagonal_eq,sourceCubicDiagonalCenter] using h.2.2.1
  refine ⟨h.1,he,?_⟩
  calc
    _ = ‖sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicDiagonalCenter n s)‖ := by
      conv_lhs => rw [he,add_sub_cancel_left]
    _ ≤ _ := sourceCubicDiagonal_norm_le n n s hs hs1 hsmall _ (refinedResonantDisk_subset_strip n h.1)

/-- Small positive amplitudes give the actual center equation and quadratic displacement bound. -/
theorem sourceCubicDiagonalCenter_eventually (n : ℤ) : ∀ᶠ s in 𝓝[>] (0 : ℝ),
    sourceCubicDiagonalCenter n s ∈ refinedResonantDisk n ∧
    sourceCubicDiagonalCenter n s = (Real.pi : ℂ)*n+sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicDiagonalCenter n s) ∧
    ‖sourceCubicDiagonalCenter n s-(Real.pi : ℂ)*n‖ ≤ sourceCubicDiagonalBound n*s^2 := by
  have hb := (sourceCubicDiagonalBound_tendsto n).eventually_lt_const (by positivity : (0 : ℝ) < Real.pi/32)
  have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [weightedCubicTailFamily_eventually_controlled n,hs1,self_mem_nhdsWithin,hb]
    with s hsmall hs1 hs hb
  exact sourceCubicDiagonalCenter_properties n s hs.le hs1.le hsmall.1 hb.le

/-- The actual moving center tends to the free center. -/
theorem sourceCubicDiagonalCenter_tendsto (n : ℤ) :
    Tendsto (sourceCubicDiagonalCenter n) (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ)*n)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((sourceCubicDiagonalCenter_eventually n).mono (fun _ h => h.2.2)) (sourceCubicDiagonalBound_tendsto n)

/-- The three-mode family has the physical real-type sign in unit-weight coordinates. -/
theorem weightedCubicTailFamily_realSign (n : ℤ) (hn : 0 < n) (s : ℝ) :
    HasRealitySign SpectralWeight.one 1 (weightedCubicTailFamily n s) := by
  have h := (sourceHasRealitySign_iff 1 (sourceCubicTailFamily n s)).mp
    ((sourceHasRealitySign_one_iff (sourceCubicTailFamily n s)).mpr (sourceCubicTailFamily_realType n hn s))
  simpa only [unitWeightedPairEquiv_sourceCubicTailFamily] using h

/-- The actual diagonal respects complex conjugation under the family smallness condition. -/
theorem sourceCubicDiagonal_conj (n m : ℤ) (hn : 0 < n) (s : ℝ) (hsmall : SourceCubicSmall n s)
    (z : ℂ) (hz : z ∈ resonantStrip m) :
    sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) m ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) m z) := by
  have hh (z : ℂ) (hz : z ∈ resonantStrip m) :
      ‖weightedPotentialSquareInShift (by simp) SpectralWeight.one (weightedCubicTailFamily n s) m z hz‖ < 1 :=
    ((resonantCubic_square_bound (by simp) SpectralWeight.one _ m z hz).trans hsmall).trans_lt (by norm_num)
  rw [sourceCubicDiagonal_eq,weightedResonantAExtension_eq (by simp) SpectralWeight.one _ m _ (conj_mem_resonantStrip hz) (hh _ _),
    weightedResonantAExtension_eq (by simp) SpectralWeight.one _ m z hz (hh z hz)]
  exact weightedResonantA_conj (by simp) SpectralWeight.one 1 (by simp) _ (weightedCubicTailFamily_realSign n hn s) m z hz (hh z hz) (hh _ _)

/-- For a positive target index, the actual center is real at all sufficiently small positive amplitudes. -/
theorem sourceCubicDiagonalCenter_real_eventually (n : ℤ) (hn : 0 < n) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (sourceCubicDiagonalCenter n s).im = 0 := by
  have hb := (sourceCubicDiagonalBound_tendsto n).eventually_lt_const (by positivity : (0 : ℝ) < Real.pi/32)
  have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [weightedCubicTailFamily_eventually_controlled n,hs1,self_mem_nhdsWithin,hb,sourceCubicDiagonalCenter_eventually n]
    with s hsmall hs1 hs hb hc
  exact resonantDiagonalCenter_im_eq_zero n _ (sourceCubicDiagonal_analytic n n s hsmall.1)
    (fun z hz => (sourceCubicDiagonal_norm_le n n s hs.le hs1.le hsmall.1 z hz).trans hb.le)
    (sourceCubicDiagonal_conj n n hn s hsmall.1) (sourceCubicDiagonalCenter n s) (refinedResonantDisk_subset_strip n hc.1) hc.2.1

end NLS.ZakharovShabat
