import NLS.ZakharovShabat.SourceBirkhoffOriginalDomain
import NLS.ZakharovShabat.SourceBirkhoffTheorem15_2

/-!
# The full Birkhoff sequence map for the original root family

Uniform spectral estimates give actual ℓᵖ coordinates and a complex
analytic map on one neighborhood of the whole real locus. The root
family is exactly the one retained from Lemma 12.12. Both the original
indexed-action radius and the historical map interface are available.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The original family gives a full sequence-valued analytic map with actual action radii. -/
theorem exists_original_birkhoff_map (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    ∃ V : Set (CoeffPair p), SourceBirkhoffMapComplexData hp hp1 W W V s ∧
      ∀ ψ ∈ V, ∀ n : ℤ,
        ((sourceBirkhoffMap hp hp1 s ψ).1 n)^2 + ((sourceBirkhoffMap hp hp1 s ψ).2 n)^2 =
          2*sourceIndexedAction hp hp1 n ψ := by
  classical
  let D := H.original_theta_common_domain.toSourceAngularEtaLocalCommonDomainData
  have hW := H.original_theta_common_domain.source_open
  have hrW := H.original_theta_common_domain.real_subset
  obtain ⟨N,hN,hrN,hNW,_,hNradius⟩ := H.exists_original_birkhoff_coordinate_domain
  have hlocal (φ : realTypeSourceLocus p) :
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧ U ⊆ N ∧
        AnalyticOnNhd ℂ (sourceBirkhoffMap hp hp1 s) U ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ‖sourceBirkhoffMap hp hp1 s ψ‖ ≤ M ∧ ∀ n : ℤ,
          ((sourceBirkhoffMap hp hp1 s ψ).1 n = sourceBirkhoffX hp hp1 n s ψ ∧
            (sourceBirkhoffMap hp hp1 s ψ).2 n = sourceBirkhoffY hp hp1 n s ψ) ∧
          (sourceNormalizedActionRoot hp hp1 n ψ)^2 = 4*sourceNormalizedActionComplexExtension hp hp1 n ψ ∧
          sourceComplexAction hp hp1 n ψ =
            (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * sourceNormalizedActionComplexExtension hp hp1 n ψ := by
    obtain ⟨Z,hZ,hφZ,hZW,C,hC,hbound⟩ := D.exists_local_uniform_gapWeightedEtaCoordinate_bound
      hW (Subset.refl _) φ.val (hrW φ.property) φ.property
    obtain ⟨U,hU,hφU,hUZ,hA,M,hM,hdata⟩ := D.exists_local_birkhoffSequence_analytic
      (Z ∩ N) (hZ.inter hN) (fun _ h => hZW h.1)
      (fun n sign => (H.gapWeightedEta_original_analytic n sign).mono (fun _ h => hZW h.1))
      C hC.le (fun ψ hψ => hbound ψ hψ.1) φ.val ⟨hφZ,hrN φ.property⟩ φ.property
    exact ⟨U,hU,hφU,(fun ψ hψ => hZW (hUZ hψ).1),(fun ψ hψ => (hUZ hψ).2),hA,M,hM,hdata⟩
  choose U hU hφU hUW hUN hA M hM hdata using hlocal
  let V := ⋃ φ : realTypeSourceLocus p, U φ
  have hV : IsOpen V := isOpen_iUnion hU
  have hVW : V ⊆ W := iUnion_subset hUW
  have hVN : V ⊆ N := iUnion_subset hUN
  have hrV : realTypeSourceLocus p ⊆ V :=
    fun φ hφ => mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφU ⟨φ,hφ⟩⟩
  have hcoord ψ (hψ : ψ ∈ V) n :
      (sourceBirkhoffMap hp hp1 s ψ).1 n = sourceBirkhoffX hp hp1 n s ψ ∧
      (sourceBirkhoffMap hp hp1 s ψ).2 n = sourceBirkhoffY hp hp1 n s ψ := by
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact ((hdata φ ψ hφ).2 n).1
  refine ⟨V,⟨D,hV,hrV,hVW,?_,?_,hcoord,?_,?_⟩,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hA φ ψ hφ
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact ⟨U φ,hU φ,hφ,subset_iUnion U φ,M φ,hM φ,fun χ hχ => (hdata φ χ hχ).1⟩
  · intro ψ hψ n
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    obtain ⟨P,hμ⟩ := H.angular_original_circles ψ (hUW φ hφ)
    have hprod := sourceGapWeightedEtaCoordinate_mul hp hp1 n s ψ
      ((P n).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ n)))
    rw [(hcoord ψ hψ n).1,(hcoord ψ hψ n).2]
    exact sourceBirkhoffX_sq_add_Y_sq hp hp1 n s ψ
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hprod)
      ((hdata φ ψ hφ).2 n).2.1 ((hdata φ ψ hφ).2 n).2.2
  · intro ψ hψ hreal n hgap
    obtain ⟨P,hμ⟩ := H.angular_original_circles ψ (hVW hψ)
    have hz := sourceGapWeightedEtaCoordinate_eq_zero_of_real_collapsed_gap hp hp1 n s ψ hreal
      ((P n).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ n)))
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
    rw [(hcoord ψ hψ n).1,(hcoord ψ hψ n).2]
    exact sourceBirkhoffXY_eq_zero_of_gapWeighted_eq_zero hp hp1 n s ψ (hz 1) (hz (-1))
  · intro ψ hψ n
    rw [(hcoord ψ hψ n).1,(hcoord ψ hψ n).2]
    exact hNradius ψ (hVN hψ) n

end SourceLemma12_12Data
end NLS.ZakharovShabat
