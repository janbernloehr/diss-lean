import NLS.ZakharovShabat.SourceFullAbelianCauchySquare
import NLS.ZakharovShabat.SourceAbelianSquare

/-! # Canonical square continuation across the selected complex gap

Relative limits from the dense canonical root domain give a square
independent of the Cauchy disc. Its spectral domain omits only the other
noncollapsed gaps; the selected gap and all collapsed gaps are filled.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceFullAbelianSquare (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n : ℤ) (t : ℂ × CoeffPair p) : ℂ :=
  denseLimitExtension (fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,t.2))^2)
    (sourceCanonicalRootDomain hp hp1 t.2) t.1

/-- Only the other noncollapsed cuts remain after squaring `F_n`. -/
def sourceFullAbelianSquareDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) : Set ℂ :=
  {z | ∀ j : ℤ, j ≠ n → canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j ≠ 0 →
    z ∉ sourcePeriodicSegment hp hp1 ψ j}

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} {ψ : CoeffPair p}

theorem sourceFullAbelianSquare_eq_sq (E : SourceAbelianSpectralChart hp hp1 W ψ) (n : ℤ) :
    EqOn (fun z => sourceFullAbelianSquare hp hp1 W n (z,ψ))
      (fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^2) (sourceOpenGapComplement hp hp1 ψ) := by
  let F : ℂ → ℂ := fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^2
  have hc : ContinuousOn F (sourceOpenGapComplement hp hp1 ψ) :=
    ((sourceFullAbelianPrimitive_spectral_analytic E n).pow 2).continuousOn
  have h := denseLimitExtension_eqOn_local F F (sourceCanonicalRootDomain hp hp1 ψ)
    (sourceOpenGapComplement hp hp1 ψ) (dense_sourceCanonicalRootDomain_complex hp hp1 ψ)
    (E.discs.isOpen_openGapComplement ψ E.source_mem) hc (fun _ _ => rfl)
  simpa only [sourceFullAbelianSquare,F] using! h

namespace SourceFullAbelianUniformCauchyFamily

theorem fullSquare_eq_square (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    EqOn (fun z => sourceFullAbelianSquare hp hp1 W n (z,ψ)) (fun z => C.square n (z,ψ))
      (ball (C.discs.center n) (C.discs.outer n)) := by
  unfold sourceFullAbelianSquare
  apply denseLimitExtension_eqOn_local (fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^2) _ _ _ (dense_sourceCanonicalRootDomain_complex hp hp1 ψ)
    isOpen_ball (C.square_analytic n ψ hψ).continuousOn
  intro z hz
  exact C.square_eq_fullPrimitive_sq n ψ hψ z ⟨hz.1,hz.2 n⟩

/-- The canonical square is analytic on the plane with only the other
noncollapsed gaps removed, including at both selected endpoints. -/
theorem fullSquare_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    AnalyticOnNhd ℂ (fun z => sourceFullAbelianSquare hp hp1 W n (z,ψ))
      (sourceFullAbelianSquareDomain hp hp1 ψ n) := by
  obtain ⟨E⟩ := C.charts ψ hψ
  intro z hz
  by_cases hn : z ∈ sourcePeriodicSegment hp hp1 ψ n
  · have hzB := C.segment_subset_outer n ψ hψ hn
    apply (C.square_analytic n ψ hψ z hzB).congr
    filter_upwards [isOpen_ball.mem_nhds hzB] with w hw
    exact (C.fullSquare_eq_square n ψ hψ hw).symm
  · have hzO : z ∈ sourceOpenGapComplement hp hp1 ψ := by
      intro j hj
      by_cases he : j = n
      · simpa only [he] using hn
      · exact hz j he hj
    apply ((sourceFullAbelianPrimitive_spectral_analytic E n z hzO).pow 2).congr
    filter_upwards [(C.discs.isOpen_openGapComplement ψ hψ).mem_nhds hzO] with w hw
    exact (sourceFullAbelianSquare_eq_sq E n hw).symm

theorem segment_subset_fullSquareDomain (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    sourcePeriodicSegment hp hp1 ψ n ⊆ sourceFullAbelianSquareDomain hp hp1 ψ n := by
  intro z hz j hj _
  exact C.discs.avoids_other ψ hψ n (ball_subset_closedBall (C.segment_subset_outer n ψ hψ hz)) j hj

theorem fullSquare_analyticAt_of_mem_segment (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ n) :
    AnalyticAt ℂ (fun w => sourceFullAbelianSquare hp hp1 W n (w,ψ)) z :=
  C.fullSquare_analytic n ψ hψ z (C.segment_subset_fullSquareDomain n ψ hψ hz)

theorem fullSquare_endpoint (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    sourceFullAbelianSquare hp hp1 W n (a,ψ) = 0 := by
  exact (C.fullSquare_eq_square n ψ hψ (C.endpoint_mem_ball n ψ hψ a ha)).trans (C.square_endpoint n ψ a ha)

theorem fullSquare_eq_gapBoundary_sq (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (θ : ℝ) (upper : Bool) :
    sourceFullAbelianSquare hp hp1 W n (sourceStandardRootMidpoint hp hp1 ψ n+
      sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ),ψ) = (C.gapBoundary n ψ θ upper)^2 := by
  have hz : sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ) ∈
      sourcePeriodicSegment hp hp1 ψ n := by
    rw [sourcePeriodicSegment_eq_midpoint_segment]
    simpa only [cosineGapPoint,← Complex.ofReal_cos] using
      cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ n) (sourceStandardRootHalfGap hp hp1 ψ n) θ
  exact (C.fullSquare_eq_square n ψ hψ (C.segment_subset_outer n ψ hψ hz)).trans (C.square_eq_gapBoundary_sq n ψ θ upper)

end SourceFullAbelianUniformCauchyFamily

/-- The full square preserves the previously constructed real-source square. -/
theorem sourceFullAbelianSquare_eq_real (φ : realTypeSourceSubmodule p)
    (E : SourceAbelianSpectralChart hp hp1 W φ.val) (n : ℤ) (z : ℂ) :
    sourceFullAbelianSquare hp hp1 W n (z,φ.val) = sourceAbelianSquare hp hp1 φ.val φ.property n z := by
  unfold sourceFullAbelianSquare sourceAbelianSquare denseLimitExtension Filter.limUnder
  congr 1
  apply Filter.map_congr
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [sourceFullAbelianPrimitive_eq_real φ E n w (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val hw)]

/-- Changing the ambient source neighborhood does not change the continued square. -/
theorem sourceFullAbelianSquare_independent_neighborhood {V : Set (CoeffPair p)}
    (D : SourceAbelianSpectralChart hp hp1 W ψ) (E : SourceAbelianSpectralChart hp hp1 V ψ)
    (n : ℤ) (z : ℂ) :
    sourceFullAbelianSquare hp hp1 W n (z,ψ) = sourceFullAbelianSquare hp hp1 V n (z,ψ) := by
  unfold sourceFullAbelianSquare denseLimitExtension Filter.limUnder
  congr 1
  apply Filter.map_congr
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [sourceFullAbelianPrimitive_independent_neighborhood D E n w
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hw)]

/-- The free continued square is the exact entire quadratic. -/
theorem sourceFullAbelianSquare_zero (E : SourceAbelianSpectralChart hp hp1 W 0) (n : ℤ) (z : ℂ) :
    sourceFullAbelianSquare hp hp1 W n (z,0) = -(z-(Real.pi : ℂ)*n)^2 := by
  exact (sourceFullAbelianSquare_eq_real (0 : realTypeSourceSubmodule p) E n z).trans (sourceAbelianSquare_zero hp hp1 n z)

end NLS.ZakharovShabat
