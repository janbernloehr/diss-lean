import NLS.SequenceSpaces.NonnegativeAnalyticAtlas
import NLS.SequenceSpaces.RealDerivativeEntries
import NLS.SequenceSpaces.RealOperatorInverse
import NLS.ComplexAnalysis.LocalInverseClosedSubspace
import NLS.SequenceSpaces.RealAnalyticInverseRestriction

/-! # Real local inverses from the original nonnegative cone map

Reality of both extension and inverse is derived from the values of the
original map on its cone domain, including at zero and other boundary points.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {f : nonnegativeLocus p → Coeff p} {U : Set (nonnegativeLocus p)}

/-- The extension atlas of a real-valued cone map preserves the full nearby
real locus. This is a consequence, not an additional atlas assumption. -/
theorem NonnegativeAnalyticAtlas.extension_eventually_real
    (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hreal : ∀ x ∈ U, f x ∈ realLocus p) {x : nonnegativeLocus p} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x.val, y ∈ realLocus p → a.extension x y ∈ realLocus p := by
  apply eventually_realLocus_of_nonnegative_analytic x.property (a.analyticAt x hx)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) (a.agreement x hx))
  filter_upwards [ball_mem_nhds x.val hr] with z hz hzpos
  have he := hball (show (⟨z,hzpos⟩ : nonnegativeLocus p) ∈ ball x r from hz)
  have heq : f ⟨z,hzpos⟩ = a.extension x z := he.2
  rw [← heq]
  exact hreal _ he.1

/-- At every invertible derivative, the actual ambient local inverse is
real on nearby real targets and recovers the original cone map. -/
theorem exists_real_localInverse_of_nonnegative_atlas
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hreal : ∀ x ∈ U, f x ∈ realLocus p) {x : nonnegativeLocus p} (hx : x ∈ U)
    (hu : IsUnit (a.derivative x)) : ∃ G : Coeff p → Coeff p,
      AnalyticAt ℂ G (f x) ∧ G (f x) = x.val ∧
      (∀ᶠ y in 𝓝 x, G (f y) = y.val) ∧
      (∀ᶠ y in 𝓝 x.val, G (a.extension x y) = y) ∧
      (∀ᶠ z in 𝓝 (f x), a.extension x (G z) = z) ∧
      fderiv ℂ G (f x) = Ring.inverse (a.derivative x) ∧
      (∀ᶠ z in 𝓝 (f x), z ∈ realLocus p → G z ∈ realLocus p) := by
  have hF := a.analyticAt x hx
  have hrF := a.extension_eventually_real hU hreal hx
  have hxr : x.val ∈ realLocus p := fun n => (x.property n).1
  have hentries := fderiv_entries_real_of_eventually_real hxr hF hrF
  obtain ⟨G,hG,hGx,hl,hr,hDG⟩ := ComplexAnalysis.exists_localInverse_of_isUnit_fderiv hF hu
  have hRG := ComplexAnalysis.eventually_mem_closedSubmodule_of_localInverse hF hu
    (realSubmodule p) isClosed_realSubmodule hxr hrF
    (inverse_mapsTo_realLocus_of_real_entries hp _ hu hentries) hG.continuousAt hGx hr
  have hfx : f x = a.extension x x.val := (a.agreement x hx).eq_of_nhds
  refine ⟨G,by rwa [hfx],by rwa [hfx],?_,hl,by rwa [hfx],by rwa [hfx],by rwa [hfx]⟩
  filter_upwards [a.agreement x hx,continuous_subtype_val.continuousAt hl] with y hy hyG
  rw [hy]
  exact hyG

/-- The inverse is an actual map between real sequence spaces, with both
real analytic inverse identities and recovery of the original cone map. -/
theorem exists_realRestriction_localInverse_of_nonnegative_atlas
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hreal : ∀ x ∈ U, f x ∈ realLocus p) {x : nonnegativeLocus p} (hx : x ∈ U)
    (hu : IsUnit (a.derivative x)) : ∃ G : RealCoeff p → RealCoeff p,
      AnalyticAt ℝ (realRestriction (a.extension x)) (reCLM p x.val) ∧
      AnalyticAt ℝ G (reCLM p (f x)) ∧ G (reCLM p (f x)) = reCLM p x.val ∧
      (∀ᶠ y in 𝓝 (reCLM p x.val), G (realRestriction (a.extension x) y) = y) ∧
      (∀ᶠ z in 𝓝 (reCLM p (f x)), realRestriction (a.extension x) (G z) = z) ∧
      (∀ᶠ y in 𝓝 x, G (reCLM p (f y)) = reCLM p y.val) := by
  obtain ⟨G,hG,hGx,hcone,hl,hr,_,hRG⟩ :=
    exists_real_localInverse_of_nonnegative_atlas hp a hU hreal hx hu
  have hcx : RealCoeff.complexCLM p (reCLM p x.val) = x.val :=
    RealCoeff.complexCLM_reCLM p _ (fun n => (x.property n).1)
  have hfx : f x = a.extension x x.val := (a.agreement x hx).eq_of_nhds
  have hFr : ∀ᶠ y in 𝓝 x.val, y ∈ realLocus p → a.extension x y ∈ realLocus p :=
    a.extension_eventually_real hU hreal hx
  have hs := realRestriction_localInverse (x := reCLM p x.val)
    (F := a.extension x) (G := G)
    (by rw [hcx]; exact a.analyticAt x hx)
    (by rw [hcx,← hfx]; exact hG)
    (by rw [hcx,← hfx]; exact hreal x hx)
    (by rw [hcx,← hfx]; exact hGx)
    (by rwa [hcx]) (by rwa [hcx,← hfx])
    (by rwa [hcx]) (by rwa [hcx,← hfx])
  have hbase : realRestriction (a.extension x) (reCLM p x.val) = reCLM p (f x) := by
    change reCLM p (a.extension x (RealCoeff.complexCLM p (reCLM p x.val))) = _
    rw [hcx,← hfx]
  rw [hbase] at hs
  refine ⟨realRestriction G,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,?_⟩
  filter_upwards [hU.mem_nhds hx,hcone] with y hy hyG
  change reCLM p (G (RealCoeff.complexCLM p (reCLM p (f y)))) = reCLM p y.val
  rw [RealCoeff.complexCLM_reCLM p _ (hreal y hy),hyG]

/-- The open dense complex local-inverse locus also admits genuine real
analytic local inverses when the original cone map is real-valued. -/
theorem open_dense_real_localInverse_of_nonnegative_atlas
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hreal : ∀ x ∈ U, f x ∈ realLocus p)
    (hcompact : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : Coeff p →L[ℂ] Coeff p))
    (hstart : a.localInversePoints.Nonempty) :
    IsOpen a.localInversePoints ∧ U ⊆ closure a.localInversePoints ∧
    ∀ x ∈ a.localInversePoints, ∃ G : RealCoeff p → RealCoeff p,
      AnalyticAt ℝ (realRestriction (a.extension x)) (reCLM p x.val) ∧
      AnalyticAt ℝ G (reCLM p (f x)) ∧ G (reCLM p (f x)) = reCLM p x.val ∧
      (∀ᶠ y in 𝓝 (reCLM p x.val), G (realRestriction (a.extension x) y) = y) ∧
      (∀ᶠ z in 𝓝 (reCLM p (f x)), realRestriction (a.extension x) (G z) = z) ∧
      (∀ᶠ y in 𝓝 x, G (reCLM p (f y)) = reCLM p y.val) := by
  have hd := open_dense_localInversePoints_of_nonnegative_atlas hp a hU hconn hcompact hstart
  refine ⟨hd.1,hd.2,?_⟩
  intro x hx
  rw [a.localInversePoints_eq] at hx
  exact exists_realRestriction_localInverse_of_nonnegative_atlas hp a hU hreal hx.1 hx.2

end NLS.Coeff
