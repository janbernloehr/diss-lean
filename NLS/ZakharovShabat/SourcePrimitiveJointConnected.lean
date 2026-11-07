import NLS.FunctionalAnalysis.OpenConnectedFibers
import NLS.ZakharovShabat.SourceFullAbelianDifferentialData

/-! # Connectedness of the actual joint moving-cut primitive domain -/
noncomputable section
open Set Complex NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceFullAbelianDifferentialData.isConnected_jointDomain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {A V : Set (CoeffPair p)}
    (D : SourceFullAbelianDifferentialData hp hp1 A V) (hV : IsConnected V) :
    IsConnected (sourceCanonicalRootJointDomain hp hp1 V) := by
  have hfib (φ : CoeffPair p) (hφ : φ ∈ V) : IsConnected (sourceCanonicalRootDomain hp hp1 φ) := by
    obtain ⟨E⟩ := D.charts φ hφ
    exact E.discs.isConnected_rootDomain φ E.source_mem
  have hproj : Prod.snd '' sourceCanonicalRootJointDomain hp hp1 V = V := by
    ext φ
    constructor
    · rintro ⟨⟨z,φ⟩,h,rfl⟩
      exact h.1
    · intro hφ
      obtain ⟨z,hz⟩ := (hfib φ hφ).nonempty
      exact ⟨(z,φ),⟨hφ,hz⟩,rfl⟩
  refine ⟨?_,isPreconnected_open_product_of_fibers _ V D.root_domain_open hV.isPreconnected hproj ?_⟩
  · obtain ⟨φ,hφ⟩ := hV.nonempty
    obtain ⟨z,hz⟩ := (hfib φ hφ).nonempty
    exact ⟨(z,φ),hφ,hz⟩
  · intro φ hφ
    have he : {z : ℂ | (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 V} = sourceCanonicalRootDomain hp hp1 φ := by
      ext z
      exact and_iff_right hφ
    rw [he]
    exact (hfib φ hφ).isPreconnected

end NLS.ZakharovShabat
