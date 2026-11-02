import NLS.MKdV.MiuraL2ActionCoefficientContinuity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Properness of the original L² mKdV action and mean map

Compact native action/mean data give bounded sources. A coefficientwise
subsequence retains every actual spectral action. The mass trace then
rules out norm loss and upgrades the limit to strong original L²
convergence. No independent mKdV inverse chart is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.MKdV

/-- Inverse images of compact full native action and signed-mean data are compact in original L². -/
theorem isProperMap_miuraRealL2ActionMeanMap : IsProperMap miuraRealL2ActionMeanMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_miuraRealL2ActionMeanMap,?_⟩
  intro K hK
  apply IsSeqCompact.isCompact
  intro a ha
  have hbJ : Bornology.IsBounded (range (fun k => miuraRealL2ActionMeanMap (a k))) :=
    hK.isBounded.subset (by rintro _ ⟨k,rfl⟩; exact ha k)
  have hba := miuraRealL2_bounded_of_actionMean_bounded a hbJ
  obtain ⟨J,hJK,σ,hσ,hJσ⟩ := hK.tendsto_subseq ha
  have hbσ : Bornology.IsBounded (range (a ∘ σ)) := hba.subset (range_comp_subset_range _ _)
  obtain ⟨b,τ,hτ,ht⟩ := Coeff.exists_physicalReal_coefficientwise_subseq (a ∘ σ) hbσ
  have hγ : StrictMono (σ ∘ τ) := hσ.comp hτ
  have hJ : Tendsto (fun k => miuraRealL2ActionMeanMap (a ((σ ∘ τ) k))) atTop (𝓝 J) :=
    hJσ.comp hτ.tendsto_atTop
  have hbc : Bornology.IsBounded (range (a ∘ (σ ∘ τ))) := hba.subset (range_comp_subset_range _ _)
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2ActionSequence_domain
  have hseq (u : MiuraRealL2) (m : ℕ) (hm : 1 ≤ m) :
      (miuraL2ActionSequence u.val).val (m : ℤ) = miuraL2Action m u.val := hcoord _ (hreal u.property) m hm
  have he : J = miuraRealL2ActionMeanMap b := by
    apply Prod.ext
    · apply Subtype.ext
      funext n
      let ev := (WeightedCoeff.evalCLM (Weight.sobolev 1) 1 n).comp
        (ContinuousLinearMap.fst ℂ (WeightedCoeff (Weight.sobolev 1) 1) ℂ)
      have hlim := ev.continuous.continuousAt.tendsto.comp hJ
      change Tendsto (fun k => (miuraL2ActionSequence (a ((σ ∘ τ) k)).val).val n) atTop (𝓝 (J.1.val n)) at hlim
      have hactual : Tendsto (fun k => (miuraL2ActionSequence (a ((σ ∘ τ) k)).val).val n) atTop
          (𝓝 ((miuraL2ActionSequence b.val).val n)) := by
        by_cases hn : 0 < n
        · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
          have hnat : 1 ≤ n.toNat := by omega
          rw [← hi]
          have h := tendsto_miuraL2Action_of_bounded_coefficientwise (a ∘ (σ ∘ τ)) b hbc ht n.toNat hnat
          simpa only [hseq _ n.toNat hnat,Function.comp_def] using! h
        · have hzero (u : MiuraRealL2) : (miuraL2ActionSequence u.val).val n = 0 :=
            miuraL2ActionSequence_nonpositive u.val n hn
          simpa only [hzero] using tendsto_const_nhds (x := (0 : ℂ)) (f := atTop)
      exact tendsto_nhds_unique hlim hactual
    · have hm := continuous_snd.continuousAt.tendsto.comp hJ
      exact tendsto_nhds_unique hm (ht 0)
  have hstrong : Tendsto (a ∘ (σ ∘ τ)) atTop (𝓝 b) :=
    tendsto_miuraRealL2_of_coefficientwise_of_actionMean _ b ht (he ▸ hJ)
  have hbK : miuraRealL2ActionMeanMap b ∈ K := he ▸ hJK
  exact ⟨b,hbK,σ ∘ τ,hγ,hstrong⟩

/-- Every complete physical L² action and signed-mean fiber is compact. -/
theorem isCompact_miuraRealL2ActionMeanFiber (z : WeightedCoeff (Weight.sobolev 1) 1 × ℂ) :
    IsCompact {a : MiuraRealL2 | miuraRealL2ActionMeanMap a = z} := by
  have hz : IsCompact ({z} : Set (WeightedCoeff (Weight.sobolev 1) 1 × ℂ)) := isCompact_singleton
  have h := (isProperMap_iff_isCompact_preimage.mp isProperMap_miuraRealL2ActionMeanMap).2 hz
  exact h

end NLS.MKdV
