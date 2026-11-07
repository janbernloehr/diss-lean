import NLS.Articles.DNLSEstimates.Primitive
import NLS.ZakharovShabat.SourceCanonicalRootCommonDomain

/-!
# The printed closed isolating discs and filled spectral root domain

The original local isolating families use open discs. Their positive
pointwise separation extends to the closures, giving the paper's disjoint
closed discs with exactly the same free tail. At a fixed complex source,
only noncollapsed cuts obstruct spectral analyticity of the canonical root.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.DNLSEstimates
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform distance inequalities extend to the closures of both sets. -/
theorem distance_bounds_closure {A B : Set ℂ} {l u : ℝ}
    (h : ∀ z ∈ A, ∀ w ∈ B, l ≤ dist z w ∧ dist z w ≤ u)
    {z w : ℂ} (hz : z ∈ closure A) (hw : w ∈ closure B) :
    l ≤ dist z w ∧ dist z w ≤ u := by
  have hfirst (w : ℂ) (hw : w ∈ B) : l ≤ dist z w ∧ dist z w ≤ u := by
    apply closure_minimal (fun x hx => h x hx w hw) _ hz
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  apply closure_minimal (fun y hy => hfirst y hy) _ hw
  exact (isClosed_le continuous_const (continuous_const.dist continuous_id)).inter
    (isClosed_le (continuous_const.dist continuous_id) continuous_const)

/-- The closures of the unchanged isolating discs are still disjoint. -/
theorem isolating_closed_discs {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (h : SourceIsolatingNeighborhoods hp hp1 V D c) :
    (∀ n : ℤ, ∃ a r : ℝ, 0 < r ∧ closure (D n) = closedBall (a : ℂ) r) ∧
    (∀ i j : ℤ, i ≠ j → Disjoint (closure (D i)) (closure (D j))) ∧
    (∀ i j : ℤ, i ≠ j → ∀ z ∈ closure (D i), ∀ w ∈ closure (D j),
      c⁻¹*|((i-j : ℤ) : ℝ)| ≤ dist z w ∧ dist z w ≤ c*|((i-j : ℤ) : ℝ)|) ∧
    (∃ N : ℕ, ∀ n : ℤ, N < n.natAbs →
      closure (D n) = closedBall ((n : ℂ)*Real.pi) (Real.pi/4)) := by
  have hb (i j : ℤ) (hij : i ≠ j) (z : ℂ) (hz : z ∈ closure (D i))
      (w : ℂ) (hw : w ∈ closure (D j)) := distance_bounds_closure (h.pointwise_distance i j hij) hz hw
  refine ⟨?_,?_,hb,?_⟩
  · intro n
    obtain ⟨a,r,hr,he⟩ := h.discs n
    exact ⟨a,r,hr,by rw [he,closure_ball _ (ne_of_gt hr)]⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hw
    have hc : 0 < c := zero_lt_one.trans_le h.one_le
    have hd : 0 < |((i-j : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hij)
    have hh := (hb i j hij z hz z hw).1
    have hp := mul_pos (inv_pos.mpr hc) hd
    simp only [dist_self,not_le.mpr hp] at hh
  · obtain ⟨N,hN⟩ := h.tail
    refine ⟨N,?_⟩
    intro n hn
    rw [hN n hn]
    simpa only [refinedResonantDisk,mul_comm (Real.pi : ℂ) (n : ℂ)] using
      (closure_ball ((n : ℂ)*Real.pi) (by positivity : (Real.pi/4 : ℝ) ≠ 0))

/-- Each fixed complex source on the unchanged common domain has an
analytic canonical root on the full complement of its noncollapsed cuts. -/
theorem canonicalRoot_filled_complex {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W : Set (CoeffPair p)} (h : SourceLemma10_5Data hp hp1 W)
    (a : CoeffPair p) (ha : a ∈ W) :
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 a) (sourceOpenGapComplement hp hp1 a) := by
  obtain ⟨V,_,_,haV,_,D,c,hD⟩ := h.neighborhoods a ha
  intro z hz
  rcases mem_sourceOpenGapComplement_cases hp hp1 a z hz with hz | ⟨n,hgap,hzn⟩
  · exact sourceCanonicalRoot_analyticOnNhd hp hp1 a z hz
  · apply sourceCanonicalRoot_analyticOnNhd_of_zeroGap hp hp1 W n (h.joint n).2 a ha hgap z
    intro m hmn hzm
    exact Set.disjoint_left.mp (hD.disjoint n m hmn.symm)
      (hD.gap a haV n hzn) (hD.gap a haV m hzm)

/-- A common open connected almost-real source domain supports both the
filled spectral statement and the literal joint closed-disc complement.
There is no joint analyticity assertion across moving open gaps. -/
theorem exists_filled_canonicalRoot_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      ∃ _h : SourceLemma10_5Data hp hp1 W,
        (∀ a ∈ W, AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 a) (sourceOpenGapComplement hp hp1 a)) ∧
        ∀ a ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ a ∈ V ∧ V ⊆ W ∧
          ∃ D c, SourceIsolatingNeighborhoods hp hp1 V D c ∧
            AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
              ((⋃ n : ℤ, closure (D n))ᶜ ×ˢ V) := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_5 hp hp1
  refine ⟨W,ho,hc,hr,h,canonicalRoot_filled_complex h,?_⟩
  intro a ha
  obtain ⟨V,hVo,_,haV,hVW,D,c,hD⟩ := h.neighborhoods a ha
  exact ⟨V,hVo,haV,hVW,D,c,hD.toSourceIsolatingNeighborhoods,
    h.canonicalClosedFixed hVW hD.toSourceIsolatingNeighborhoods⟩

/-- The printed infimum-distance comparison holds for the actual closed
discs, with the original constant and no change in the local family. -/
theorem isolating_closed_discs_set_distance {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (i j : ℤ) (hij : i ≠ j) :
    c⁻¹*|((i-j : ℤ) : ℝ)| ≤ spectralSetDistance (closure (D i)) (closure (D j)) ∧
      spectralSetDistance (closure (D i)) (closure (D j)) ≤ c*|((i-j : ℤ) : ℝ)| := by
  have hne (n : ℤ) : (closure (D n)).Nonempty := by
    obtain ⟨a,r,hr,he⟩ := h.discs n
    rw [he]
    exact ⟨a,subset_closure (Metric.mem_ball_self hr)⟩
  exact spectralSetDistance_comparison_of_pointwise (fun n => closure (D n)) hne c
    (isolating_closed_discs h).2.2.1 i j hij
end NLS.Articles.DNLSEstimates
