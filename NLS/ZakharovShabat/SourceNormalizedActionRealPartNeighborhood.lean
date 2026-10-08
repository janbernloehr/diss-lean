import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceContinuity
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic
import NLS.ZakharovShabat.SourceRealActionBallOverlap
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.ZakharovShabat.SpectralStripNeighborhood

/-! # Uniform comparison with the real-type projection on an L² neighborhood

One source neighborhood controls all normalized action coordinates. No
Sobolev norm is used to choose it, so the same neighborhood serves every weight.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Local ℓ² continuity bounds every normalized action's change under real projection. -/
theorem exists_local_sourceNormalizedAction_realPart_bound (ψ : CoeffPair 2)
    (hψ : IsRealType (CoeffPair.toMax 2 ψ)) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ ψ ∈ U ∧
      U ⊆ sourceSpectralStripNeighborhood (by simp) ∧ ∀ χ ∈ U, ∀ n : ℤ,
        ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n χ-
          sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sourceRealPart χ)‖ ≤ 1 ∧
        sourceComplexAction (by simp) (by norm_num) n χ =
          (sourcePeriodicGapDisplacement (by simp) (by norm_num) χ n)^2*
            sourceNormalizedActionComplexExtension (by simp) (by norm_num) n χ := by
  obtain ⟨V,hV,hψV,F,hval,hcont⟩ := exists_local_sourceNormalizedActionDeviation_continuousMap
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num) (by norm_num : (1:ℝ≥0∞) < 2)
    (by simp) (by norm_num) ψ hψ
  obtain ⟨G,hG,hψG,_,hfactor⟩ := exists_local_sourceNormalizedAction_allIndices_analytic_factor
    (by simp) (by norm_num) ψ hψ
  have hfix := sourceRealPart_eq_self_of_realType ψ hψ
  have hF := (hcont ψ hψV).continuousAt (hV.mem_nhds hψV)
  have hFR : ContinuousAt F (sourceRealPart ψ) := by simpa only [hfix] using hF
  have hd : ContinuousAt (fun χ : CoeffPair 2 => ‖F χ-F (sourceRealPart χ)‖) ψ :=
    (hF.sub (hFR.comp (continuous_sourceRealPart (by simp)).continuousAt)).norm
  have hsmall : ∀ᶠ χ : CoeffPair 2 in 𝓝 ψ, ‖F χ-F (sourceRealPart χ)‖ < 4 :=
    hd.eventually (gt_mem_nhds (by simp only [hfix,sub_self,norm_zero]; norm_num))
  obtain ⟨O,hOsub,hO,hψO⟩ := _root_.mem_nhds_iff.mp hsmall
  let U := ((V ∩ (sourceRealPart ⁻¹' V)) ∩ G) ∩
    (O ∩ sourceSpectralStripNeighborhood (by simp))
  have hU : IsOpen U :=
    ((hV.inter (hV.preimage (continuous_sourceRealPart (by simp)))).inter hG).inter
      (hO.inter (isOpen_sourceSpectralStripNeighborhood (by simp)))
  refine ⟨U,hU,⟨⟨⟨hψV,by simpa only [mem_preimage,hfix] using hψV⟩,hψG⟩,
    ⟨hψO,real_mem_sourceSpectralStripNeighborhood (by simp) (by norm_num) ψ hψ⟩⟩,
    fun χ hχ => hχ.2.2,?_⟩
  intro χ hχ n
  refine ⟨?_,hfactor χ hχ.1.2 n⟩
  have hn := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (F χ-F (sourceRealPart χ)) n).trans_lt (hOsub hχ.2.1)
  change ‖F χ n-F (sourceRealPart χ) n‖ < 4 at hn
  rw [hval χ hχ.1.1.1 n,hval (sourceRealPart χ) hχ.1.1.2 n] at hn
  change ‖(4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) n χ-1)-
    (4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sourceRealPart χ)-1)‖ < 4 at hn
  have he (x y : ℂ) : (4*x-1)-(4*y-1) = 4*(x-y) := by ring
  rw [he,norm_mul,Complex.norm_ofNat] at hn
  linarith

/-- A connected L²-open neighborhood of the entire real locus works at every index. -/
theorem exists_sourceNormalizedAction_realPart_neighborhood :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ sourceSpectralStripNeighborhood (by simp) ∧ ∀ χ ∈ U, ∀ n : ℤ,
        ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n χ-
          sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sourceRealPart χ)‖ ≤ 1 ∧
        sourceComplexAction (by simp) (by norm_num) n χ =
          (sourcePeriodicGapDisplacement (by simp) (by norm_num) χ n)^2*
            sourceNormalizedActionComplexExtension (by simp) (by norm_num) n χ := by
  classical
  have hlocal (ψ : realTypeSourceSubmodule 2) :=
    exists_local_sourceNormalizedAction_realPart_bound ψ.val ψ.property
  choose V hV hψV hVS hb using hlocal
  let S : Set (CoeffPair 2) := ⋃ ψ : realTypeSourceSubmodule 2, V ψ
  have hS : IsOpen S := isOpen_iUnion hV
  have hrealS : realTypeSourceLocus 2 ⊆ S := fun ψ hψ =>
    mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hψV ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn S (0 : CoeffPair 2)
  have hzero : (0 : CoeffPair 2) ∈ realTypeSourceLocus 2 := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus 2 ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  refine ⟨U,hS.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),
    hrealU,?_,?_⟩
  · intro χ hχ
    obtain ⟨ψ,hψ⟩ := mem_iUnion.mp (hUS hχ)
    exact hVS ψ hψ
  · intro χ hχ n
    obtain ⟨ψ,hψ⟩ := mem_iUnion.mp (hUS hχ)
    exact hb ψ χ hψ n

end NLS.ZakharovShabat
