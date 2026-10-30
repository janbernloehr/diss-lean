import NLS.FunctionalAnalysis.FiberContractibleDomain
import NLS.ZakharovShabat.SourcePsiOriginalOmega
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity
import NLS.ZakharovShabat.SourceStandardRootAlgebra

/-!
# Contraction of the original real root-placement domain

The actual midpoint sequence is a common continuous section of every original real placement fiber.
-/

noncomputable section
namespace NLS.ZakharovShabat
open Set Complex Metric
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.convex_originalRootPlacement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    Convex ℝ (sourcePsiOriginalRootPlacement (p := p) D) := by
  intro a ha b hb x y hx hy hxy k
  obtain ⟨d,r,_,he⟩ := hD.discs k
  have hconv : Convex ℝ (D k) := by rw [he]; exact convex_ball _ _
  have h := hconv (ha k) (hb k) hx hy hxy
  have hlin : displacedRoots (x • a+y • b) k = x • displacedRoots a k+y • displacedRoots b k := by
    simp only [displacedRoots,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply]
    rw [smul_add,smul_add]
    have hc : x • ((Real.pi:ℂ)*k)+y • ((Real.pi:ℂ)*k) = (Real.pi:ℂ)*k := by
      rw [← add_smul,hxy,one_smul]
    linear_combination -hc
  rwa [hlin]

theorem SourceIsolatingNeighborhoods.real_midpoint_mem_originalRootPlacement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : realTypeSourceSubmodule p) (hφ : (φ:CoeffPair p) ∈ V) :
    RealCoeff.complexCLM p (Coeff.reCLM p (sourcePeriodicMidpointDisplacement hp hp1 φ)) ∈
      sourcePsiOriginalRootPlacement D := by
  have hreal : ∀ k, (sourcePeriodicMidpointDisplacement hp hp1 φ k).im = 0 := by
    intro k
    have hm := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ φ.property k _
      (sourcePeriodicMidpoint_mem_segment hp hp1 φ k)
    rw [sourcePeriodicMidpointDisplacement_apply,Complex.sub_im,hm]
    simp
  rw [RealCoeff.complexCLM_reCLM _ _ hreal]
  intro k
  simpa [displacedRoots,sourcePeriodicMidpointDisplacement_apply] using
    hD.gap φ hφ k (sourcePeriodicMidpoint_mem_segment hp hp1 φ k)

/-- The union of all supplied original real placement charts contracts
through the actual midpoint section, regardless of overlap shapes. -/
theorem contractible_iUnion_sourcePsiOriginalOmega
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : realTypeSourceSubmodule p → Set (CoeffPair p))
    (D : realTypeSourceSubmodule p → ℤ → Set ℂ)
    (c : realTypeSourceSubmodule p → ℝ)
    (hD : ∀ φ, SourceIsolatingNeighborhoods hp hp1 (V φ) (D φ) (c φ))
    (hV : ∀ φ, (φ:CoeffPair p) ∈ V φ) :
    ContractibleSpace (⋃ φ, sourcePsiOriginalOmega (V φ) (D φ)) := by
  let s : realTypeSourceSubmodule p → RealCoeff p :=
    fun φ => Coeff.reCLM p (sourcePeriodicMidpointDisplacement hp hp1 φ)
  have hs : Continuous s := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    exact (Coeff.reCLM p).continuous.continuousAt.comp
      ((continuousAt_sourcePeriodicMidpointDisplacement_of_realType hp hp1 φ φ.property).comp
        continuous_subtype_val.continuousAt)
  change ContractibleSpace (⋃ φ,
    ((Subtype.val : realTypeSourceSubmodule p → CoeffPair p) ⁻¹' V φ) ×ˢ
      ((RealCoeff.complexCLM p) ⁻¹' sourcePsiOriginalRootPlacement (D φ)))
  apply NLS.FunctionalAnalysis.contractible_iUnion_products_of_section _ _ s hs
  · intro φ
    exact ⟨φ,hV φ⟩
  · intro φ
    exact (hD φ).convex_originalRootPlacement.linear_preimage (RealCoeff.complexCLM p).toLinearMap
  · intro φ ψ hψ
    exact (hD φ).real_midpoint_mem_originalRootPlacement ψ hψ

end NLS.ZakharovShabat
