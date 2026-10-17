import NLS.ZakharovShabat.SourceResonantMidpointCenter
import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic

/-! # Singleton periodic strips force actual coordinate zeros

Uniform canonical endpoint pairs identify the closed gap on one common
source neighborhood. The real closed-gap identity then kills both original
Birkhoff coordinates, uniformly at all sufficiently distant indices.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceBirkhoffMapComplexData.exists_uniform_zero_of_singleton_strip
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceLocus p) :
    ∃ K : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧
      ∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → ∀ n : ℤ, K ≤ n.natAbs →
        ∀ c : ℂ, (∀ z ∈ resonantStrip n,
          z ∈ periodicSpectrum hp (periodOnePotential ψ) ↔ z = c) →
        (sourceBirkhoffMap hp hp1 s ψ).1 n = 0 ∧
          (sourceBirkhoffMap hp hp1 s ψ).2 n = 0 := by
  obtain ⟨K,V,ho,hφ,hpair⟩ := exists_uniform_sourceCanonicalEndpointPairs hp hp1 φ.val
  refine ⟨K,V ∩ W,ho.inter D.source_open,⟨hφ,D.real_subset φ.property⟩,
    inter_subset_right,?_⟩
  intro ψ hψ hreal n hn c hc
  have hk := hpair ψ hψ.1 n hn
  have hs := canonicalPeriodicEndpoints_mem_spectrum hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hl := (hc _ (refinedResonantDisk_subset_strip n hk.left_mem)).mp hs.1
  have hr := (hc _ (refinedResonantDisk_subset_strip n hk.right_mem)).mp hs.2
  apply D.real_closed_gap_zero ψ hψ.2 hreal n
  simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,hl,hr,sub_self]

end NLS.ZakharovShabat
