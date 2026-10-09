import NLS.ComplexAnalysis.LinearCoordinatesLocalInverse

/-! # Inverse germs depend only on the germ of the original map -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Changing the map outside a neighborhood does not change its analytic inverse germs. -/
theorem HasAnalyticInverse.congr {f f' : E → E} {x : E}
    (h : HasAnalyticInverse (𝕜 := 𝕜) f x) (he : f =ᶠ[𝓝 x] f') :
    HasAnalyticInverse (𝕜 := 𝕜) f' x := by
  obtain ⟨g,hg,hgx,hl,hr⟩ := h
  have hx := he.eq_of_nhds
  refine ⟨g,by rwa [← hx],by rwa [← hx],?_,?_⟩
  · filter_upwards [he,hl] with y hy hyl
    rwa [← hy]
  · have ht : Tendsto g (𝓝 (f x)) (𝓝 x) := by
      simpa only [hgx] using hg.continuousAt.tendsto
    rw [← hx]
    filter_upwards [he.comp_tendsto ht,hr] with y hy hyr
    change f (g y) = f' (g y) at hy
    rwa [← hy]

/-- Equality of germs gives equivalent existence of two-sided analytic inverse germs. -/
theorem hasAnalyticInverse_congr_iff {f f' : E → E} {x : E} (he : f =ᶠ[𝓝 x] f') :
    HasAnalyticInverse (𝕜 := 𝕜) f x ↔ HasAnalyticInverse (𝕜 := 𝕜) f' x :=
  ⟨fun h => h.congr he,fun h => h.congr he.symm⟩

end NLS.ComplexAnalysis
