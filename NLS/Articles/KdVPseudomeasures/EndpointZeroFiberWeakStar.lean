import NLS.Articles.KdVPseudomeasures.ArticleEndpointWeakStarContinuity
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeZeroFiber
import NLS.Articles.KdVPseudomeasures.SourceWeakStarCompactSets
import NLS.SequenceSpaces.PhysicalSobolevWienerSeparation
import NLS.Topology.CompactSingletonFiber

/-! Inverse weak-star stability at the actual zero fiber on every specified
original endpoint norm ball. Global injectivity is not used or claimed. -/
noncomputable section
open Set Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The original zero distribution with its physical endpoint weak-star topology. -/
def endpointWeakStarZero (r : ℝ) (hr : AdmissiblePredualOrder r) : WeakStarPotential r :=
  ⟨originalEndpointPotential r hr 0⟩

theorem endpointWeakStarZero_val (r : ℝ) (hr : AdmissiblePredualOrder r) :
    (endpointWeakStarZero r hr).toPotential.val=0 := by
  change periodOneEndpointOriginal r hr.1 0=0
  exact map_zero _

/-- Zero output is equivalent to equality of the ENTIRE original input distribution to zero. -/
theorem articleEndpointCoordinates_eq_zero_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) : articleEndpointCoordinates r hr q=0 ↔ q.val=0 := by
  constructor
  · intro hz
    have he : originalEndpointRealSignedCoordinates r hr q=0 :=
      (articleEndpointTargetEquiv r hr).injective (hz.trans (map_zero _).symm)
    have hn := congrArg (endpointPhysicalNativeTargetInclusion r hr) he
    rw [endpointPhysicalNativeTargetInclusion_originalMap,map_zero] at hn
    have hq := original_Hill_native_zero_implies_zero (sourceOriginalPotential r hr q) hn
    apply Subtype.ext
    have hd := congrArg (fun a : FourierLebesgueSpace (2:ℝ) (-1) 2 => a.val) hq
    change q.val.val=(0 : SmoothPeriodicTest.Distribution (2:ℝ))
    change (sourceOriginalPotential r hr q).val.val=(0 : SmoothPeriodicTest.Distribution (2:ℝ)) at hd
    exact (sourceOriginalPotential_val r hr q).symm.trans hd
  · intro hq
    have hs : originalEndpointRealSource r hr q=0 := by
      apply Subtype.ext
      apply Subtype.ext
      change periodOneEndpointExtract r hr.1 q.val=0
      rw [hq,map_zero]
    change articleEndpointTargetEquiv r hr (hillEndpointRealSignedMap r hr
      (originalEndpointRealSource r hr q))=0
    rw [hs,hillEndpointRealSignedMap_zero,map_zero]

/-- The exact singleton zero fiber in the original physical weak-star source. -/
theorem articleEndpointCoordinates_zero_fiber (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) :
    articleEndpointCoordinates r hr q.toPotential=0 ↔ q=endpointWeakStarZero r hr := by
  rw [articleEndpointCoordinates_eq_zero_iff]
  constructor
  · intro hq
    cases q with
    | mk p =>
      congr 1
      exact Subtype.ext (hq.trans (endpointWeakStarZero_val r hr).symm)
  · rintro rfl
    exact endpointWeakStarZero_val r hr

/-- The actual map into the literal physical real Wiener weak dual has exactly
one zero-output fiber point, with no global inverse premise. -/
theorem articleEndpointWeakStarCoordinates_zero_fiber (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) :
    articleEndpointWeakStarCoordinates r hr q=
      articleEndpointWeakStarCoordinates r hr (endpointWeakStarZero r hr) ↔
      q=endpointWeakStarZero r hr := by
  constructor
  · intro h
    have he := WeightedCoeff.physicalSobolevWeakStar_injective (1/2-r) h
    have hz : articleEndpointCoordinates r hr (endpointWeakStarZero r hr).toPotential=0 :=
      (articleEndpointCoordinates_eq_zero_iff r hr _).mpr (endpointWeakStarZero_val r hr)
    exact (articleEndpointCoordinates_zero_fiber r hr q).mp (he.trans hz)
  · rintro rfl
    rfl

/-- On EVERY original endpoint norm ball, every original weak-star neighborhood
of zero contains all inputs whose ACTUAL outputs lie in a sufficiently small
literal physical real Wiener weak-star neighborhood of zero. -/
theorem exists_output_nhds_control_source_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (U : Set (WeakStarPotential r)) (hU : U ∈ 𝓝 (endpointWeakStarZero r hr)) :
    ∃ V ∈ 𝓝 (articleEndpointWeakStarCoordinates r hr (endpointWeakStarZero r hr)),
      ∀ q : WeakStarPotential r, ‖q.toPotential.val‖ ≤ R →
        articleEndpointWeakStarCoordinates r hr q ∈ V → q ∈ U := by
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}
  have hf : ContinuousOn (articleEndpointWeakStarCoordinates r hr) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_articleEndpointWeakStarCoordinates_on_bounded r hr K ⟨R,fun _ hq => hq⟩
  exact NLS.Topology.exists_nhds_of_compact_singleton_fiber K (isCompact_sourceNormBall r R)
    (articleEndpointWeakStarCoordinates r hr) hf (endpointWeakStarZero r hr)
    (fun q _ hq => (articleEndpointWeakStarCoordinates_zero_fiber r hr q).mp hq) U hU

/-- Inverse convergence at zero holds for EVERY eventually endpoint-bounded
net in the ORIGINAL physical weak-star topology. -/
theorem tendsto_source_zero_of_output_weakStar (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) {X : Type*} {l : Filter X} (x : X → WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hz : Tendsto (fun k => articleEndpointWeakStarCoordinates r hr (x k)) l
      (𝓝 (articleEndpointWeakStarCoordinates r hr (endpointWeakStarZero r hr)))) :
    Tendsto x l (𝓝 (endpointWeakStarZero r hr)) := by
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨V,hV,hVU⟩ := exists_output_nhds_control_source_zero r hr R U hU
  filter_upwards [hb,hz hV] with k hk hzk
  exact hVU (x k) hk hzk

/-- Every admissible original lower finite-p norm converges for the SAME net;
no new subsequence or endpoint norm convergence is asserted. -/
theorem tendsto_sourceLower_zero_of_output_weakStar (r : ℝ) (hr : AdmissiblePredualOrder r)
    (t R : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ht : 1 < (-r-t)*p.toReal)
    {X : Type*} {l : Filter X} (x : X → WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hz : Tendsto (fun k => articleEndpointWeakStarCoordinates r hr (x k)) l
      (𝓝 (articleEndpointWeakStarCoordinates r hr (endpointWeakStarZero r hr)))) :
    Tendsto (fun k => sourceLowerDistribution r t hp ht (x k)) l
      (𝓝 (sourceLowerDistribution r t hp ht (endpointWeakStarZero r hr))) :=
  (tendsto_source_iff_lowerDistribution_of_eventually_normBound r t R hp ht x
    (endpointWeakStarZero r hr) hb).mp (tendsto_source_zero_of_output_weakStar r hr R x hb hz)

/-- Forward convergence also needs only an EVENTUAL specified endpoint
bound; this makes no boundedness claim for arbitrary convergent nets. -/
theorem tendsto_articleEndpointWeakStarCoordinates_of_eventually_normBound
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    {X : Type*} {l : Filter X} (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R) (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun k => articleEndpointWeakStarCoordinates r hr (x k)) l
      (𝓝 (articleEndpointWeakStarCoordinates r hr a)) := by
  let y : X → WeakStarPotential r := fun k => if ‖(x k).toPotential.val‖ ≤ R then x k else a
  have he : x =ᶠ[l] y := hb.mono fun k hk => by simp only [y,if_pos hk]
  have hy : PotentialNormBounded r (range y) := by
    refine ⟨max R ‖a.toPotential.val‖,?_⟩
    rintro _ ⟨k,rfl⟩
    dsimp [y]
    split_ifs with hk
    · exact hk.trans (le_max_left _ _)
    · exact le_max_right _ _
  have hyt : Tendsto y l (𝓝 a) := (tendsto_congr' he).mp hx
  exact (tendsto_congr' (he.mono fun k hk => congrArg (articleEndpointWeakStarCoordinates r hr) hk)).mpr
    (tendsto_articleEndpointWeakStarCoordinates_of_bounded r hr y a hy hyt)

/-- Actual forward and inverse weak-star convergence agree at zero on EVERY
original endpoint norm ball, for arbitrary filters and eventual bounds. -/
theorem tendsto_output_zero_iff_source_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) {X : Type*} {l : Filter X} (x : X → WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R) :
    Tendsto (fun k => articleEndpointWeakStarCoordinates r hr (x k)) l
      (𝓝 (articleEndpointWeakStarCoordinates r hr (endpointWeakStarZero r hr))) ↔
      Tendsto x l (𝓝 (endpointWeakStarZero r hr)) :=
  ⟨tendsto_source_zero_of_output_weakStar r hr R x hb,
    tendsto_articleEndpointWeakStarCoordinates_of_eventually_normBound r hr R x _ hb⟩

/-- The identical original Hminus-one distributions converge to the literal
zero distribution for the SAME eventually endpoint-bounded net. -/
theorem tendsto_originalHminusOne_zero_of_output_weakStar (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) {X : Type*} {l : Filter X} (x : X → WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hz : Tendsto (fun k => articleEndpointWeakStarCoordinates r hr (x k)) l
      (𝓝 (articleEndpointWeakStarCoordinates r hr (endpointWeakStarZero r hr)))) :
    Tendsto (fun k => potentialHminusOne r hr (x k).toPotential) l (𝓝 0) := by
  have h := tendsto_sourceLower_zero_of_output_weakStar r hr (-1) R (p := 2)
    (by norm_num) (admissible_hminusOne_threshold r hr) x hb hz
  have hz0 : potentialHminusOne r hr (endpointWeakStarZero r hr).toPotential=0 := by
    unfold potentialHminusOne
    rw [endpointWeakStarZero_val,map_zero]
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr,hz0] using h

/-- On every specified original endpoint norm ball, FINITELY MANY actual
output coefficients control every admissible original lower norm near zero.
The finite set and its one positive tolerance are chosen before the input. -/
theorem exists_finite_output_control_sourceLower_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (t R : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ht : 1 < (-r-t)*p.toReal)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset ℤ, ∃ δ > 0, ∀ q : WeakStarPotential r, ‖q.toPotential.val‖ ≤ R →
      (∀ n ∈ J, ‖(articleEndpointCoordinates r hr q.toPotential).val.val.val n‖ < δ) →
      dist (sourceLowerDistribution r t hp ht q)
        (sourceLowerDistribution r t hp ht (endpointWeakStarZero r hr)) < ε := by
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ max R 0}
  have hbK : PotentialNormBounded r K := ⟨max R 0,fun _ hq => hq⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sourceNormBall r (max R 0))
  let a : K := ⟨endpointWeakStarZero r hr,by
    change ‖(endpointWeakStarZero r hr).toPotential.val‖ ≤ max R 0
    rw [endpointWeakStarZero_val,norm_zero]
    exact le_max_right _ _⟩
  let c : K → ℤ → ℂ := fun q n => (articleEndpointCoordinates r hr q.val.toPotential).val.val.val n
  have hF := continuous_articleEndpointWeakStarCoordinates_on_bounded r hr K hbK
  have hc : ∀ n, Continuous (fun q : K => c q n) := by
    intro n
    apply continuous_iff_continuousAt.mpr
    intro q
    exact WeightedCoeff.tendsto_coefficients_of_physicalSobolevWeakStar (1/2-r)
      (fun b : K => articleEndpointCoordinates r hr b.val.toPotential)
      (articleEndpointCoordinates r hr q.val.toPotential) hF.continuousAt.tendsto n
  have ha : articleEndpointCoordinates r hr a.val.toPotential=0 :=
    (articleEndpointCoordinates_eq_zero_iff r hr _).mpr (endpointWeakStarZero_val r hr)
  have hu : ∀ q : K, c q=c a → q=a := by
    intro q hq
    have he : articleEndpointCoordinates r hr q.val.toPotential=
        articleEndpointCoordinates r hr a.val.toPotential := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hq
    apply Subtype.ext
    exact (articleEndpointCoordinates_zero_fiber r hr q.val).mp (he.trans ha)
  have hf := (isEmbedding_sourceLowerDistribution_on_bounded r t hp ht K hbK).continuous
  obtain ⟨J,δ,hδ,hJ⟩ := NLS.Topology.exists_finite_coordinate_control_at_singleton c hc a hu
    (fun q : K => sourceLowerDistribution r t hp ht q.val) hf ε hε
  refine ⟨J,δ,hδ,fun q hq hcoords => hJ ⟨q,hq.trans (le_max_left _ _)⟩ (fun n hn => ?_)⟩
  change dist _ ((articleEndpointCoordinates r hr a.val.toPotential).val.val.val n) < δ
  rw [ha]
  change dist _ (0:ℂ) < δ
  rw [dist_zero_right]
  exact hcoords n hn

/-- Uniform convergence of actual output coefficients to zero implies
uniform lower-norm convergence of the SAME input families on arbitrary
parameter sets. Only an eventual common original endpoint bound is needed. -/
theorem tendstoUniformly_sourceLower_zero_of_output_coefficients
    (r : ℝ) (hr : AdmissiblePredualOrder r) (t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ht : 1 < (-r-t)*p.toReal)
    {A B : Type*} (F : A → B → WeakStarPotential r) (l : Filter A)
    (hb : ∀ᶠ a in l, ∀ b, ‖(F a b).toPotential.val‖ ≤ R)
    (hz : ∀ n : ℤ, TendstoUniformly
      (fun a b => (articleEndpointCoordinates r hr (F a b).toPotential).val.val.val n)
      (fun _ : B => (0:ℂ)) l) :
    TendstoUniformly (fun a b => sourceLowerDistribution r t hp ht (F a b))
      (fun _ : B => sourceLowerDistribution r t hp ht (endpointWeakStarZero r hr)) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨J,δ,hδ,hJ⟩ := exists_finite_output_control_sourceLower_zero r hr t R hp ht ε hε
  have he : ∀ᶠ a in l, ∀ n ∈ J, ∀ b : B,
      dist 0 ((articleEndpointCoordinates r hr (F a b).toPotential).val.val.val n) < δ :=
    (eventually_all_finset J).mpr fun n _ => (Metric.tendstoUniformly_iff.mp (hz n)) δ hδ
  filter_upwards [hb,he] with a ha hcoords b
  exact (dist_comm _ _).trans_lt (hJ (F a b) (ha b) (fun n hn => by
    simpa only [dist_zero_left] using hcoords n hn b))

end NLS.Articles.KdVPseudomeasures
