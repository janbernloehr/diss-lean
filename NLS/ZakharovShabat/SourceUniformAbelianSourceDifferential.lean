import NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
import NLS.ZakharovShabat.SourceFullAbelianDifferentialData

/-! Every actual uniform Cauchy family has the same normalized source
differential at real sources, regardless of its ambient primitive chart. -/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem source_hasFDerivAt_of_real (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j : ℤ) (z : ℂ) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    HasFDerivAt (fun ψ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 W j (z,ψ))
      ((sourceCanonicalRoot hp hp1 φ.val z)⁻¹ • sourceDiscriminantCotangent hp z φ.val) φ.val := by
  obtain ⟨V,U,_,D⟩ := exists_sourceFullAbelianDifferentialData hp hp1
  have hφU := D.real_subset φ.property
  have hinc : Continuous (fun ψ : CoeffPair p => (z,ψ)) := continuous_const.prodMk continuous_id
  have hnb := hinc.continuousAt (D.root_domain_open.mem_nhds ⟨hφU,hz⟩)
  have he : (fun ψ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 V j (z,ψ)) =ᶠ[𝓝 φ.val]
      (fun ψ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 W j (z,ψ)) := by
    filter_upwards [hnb,isOpen_ball.mem_nhds hφ] with ψ hψ hψC
    obtain ⟨E⟩ := D.charts ψ hψ.1
    obtain ⟨F⟩ := C.charts ψ hψC
    exact sourceFullAbelianPrimitive_independent_neighborhood E F j z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hψ.2)
  exact (D.source_hasFDerivAt j z φ.val hφU hz).congr_of_eventuallyEq he.symm

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
