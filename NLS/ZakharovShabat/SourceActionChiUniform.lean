import NLS.ZakharovShabat.SourceActionChiGapSup
import NLS.ZakharovShabat.SourceCriticalHalfExponentOffsets
import NLS.ZakharovShabat.SourceQuotientDiscSupDecomposition

/-!
# Locally uniform estimates for χ_n on the original domain

Substitute the actual critical displacement into the joint quotient
estimates. Lemma 10.10 bounds its midpoint offset at the half exponent.
One neighborhood works for every refined exponent and every index,
including the finite central block and collapsed complex gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every original isolating family supplies the literal gap-supremum estimate;
the source neighborhood is chosen before all refined target exponents. -/
theorem SourceEquation2_18Data.chiGapSup_refined_on
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hW : IsOpen W)
    (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) :
    ∃ S : Set (CoeffPair p), IsOpen S ∧ φ ∈ S ∧ S ⊆ V ∧
      ∀ (r : ℝ≥0∞), r ≠ ⊤ → 1 < r → p/2 ≤ r →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ S, ∃ a : Coeff r,
          (∀ n : ℤ, a n = (sourceActionChiGapSup hp hp1 ψ n : ℂ)) ∧ ‖a‖ ≤ L := by
  have h6 := H.criticalOffsets.previous.previous.previous
  obtain ⟨U,hU,hφU,hUV,R,G,M,N,K,hE⟩ :=
    h6.quotientDiscEstimates hD hV φ (hVW hφ) hφ (sourceCriticalDisplacement hp hp1 φ)
  obtain ⟨Vb,hVb,_,hφb,_,B,hB,hbound⟩ := H.criticalOffsets.locally_uniform φ (hVW hφ)
  let graph := fun ψ : CoeffPair p => (sourceCriticalDisplacement hp hp1 ψ,ψ)
  have hgraph : ContinuousOn graph W :=
    (h6.roots.roots.symmetric.simplicity.criticalDisplacement_analytic hW).continuousOn.prodMk continuousOn_id
  let S := Vb ∩ (W ∩ graph ⁻¹' U)
  have hS : IsOpen S := hVb.inter (hgraph.isOpen_inter_preimage hW hU)
  have hSV : S ⊆ V := fun ψ hψ => (hUV hψ.2.2).2
  refine ⟨S,hS,⟨hφb,hVW hφ,hφU⟩,hSV,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) := by
    rw [Coeff.halfExponent_eq_div hp]
    exact ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)
  have hhalfr : ENNReal.ofReal (p.toReal/2) ≤ r := by rwa [Coeff.halfExponent_eq_div hp]
  obtain ⟨Lr,Lg,hLr,hLg,hmajor⟩ := hE.majorants hr1 hr (B*G^2) (mul_nonneg hB.le (sq_nonneg _))
  refine ⟨Lr+Lg,add_nonneg hLr hLg,?_⟩
  intro ψ hψ
  let a₀ := sourceCriticalHalfGapOffset hp hp1 ψ
  have ha₀ : ‖a₀‖ ≤ B*G^2 := by
    apply (Coeff.norm_multiplier_le_quasi hhalf.ne' _ _).trans
    exact mul_le_mul ((Coeff.norm_exponentInclusion_le le_top _).trans (hbound ψ hψ.1))
      (hE.squared_gap (graph ψ) hψ.2.2) (lp.norm_nonneg' _) hB.le
  let a : Coeff r := ⟨fun n => a₀ n,(lp.memℓp a₀).of_exponent_ge hhalfr⟩
  have ha : ‖a‖ ≤ B*G^2 :=
    (Coeff.norm_quasiExponentInclusion_le hhalf (zero_lt_one.trans hr1) hr hhalfr a₀).trans ha₀
  have hoff (n : ℤ) : displacedRoots (graph ψ).1 n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = a n := by
    simp only [graph,sourceCriticalDisplacement,displacedRoots_canonicalCriticalDisplacement]
    change _ = sourceCriticalHalfGapOffset hp hp1 ψ n
    rw [sourceCriticalHalfGapOffset_apply,H.criticalOffsets.exact_offset ψ hψ.2.1 n]
    ring
  obtain ⟨A,C,hA,hC,hpoint⟩ := hmajor (graph ψ) hψ.2.2 a ha hoff
  obtain ⟨E,hEeq,hEn,_⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants
    hhalf hr1 hr hhalfr (fun n => (sourceActionChiGapSup hp hp1 ψ n : ℂ)) 0 A C (by
      intro n _
      rw [Complex.norm_real,Real.norm_of_nonneg (H.chiGapSup_nonneg ψ hψ.2.1 n)]
      apply sourceActionChiGapSup_le
      intro z hz
      rw [sourceActionChi_eq_quotient hp hp1 ψ n z (H.segment_subset_omitted ψ hψ.2.1 n hz)]
      exact hpoint n z (hD.gap ψ (hSV hψ) n hz))
  exact ⟨E,fun n => by simpa using hEeq n,hEn.trans (add_le_add hA hC)⟩

/-- The refined bounds hold locally near every complex point of the full W. -/
theorem SourceEquation2_18Data.chiGapSup_refined
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hW : IsOpen W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ S : Set (CoeffPair p), IsOpen S ∧ φ ∈ S ∧ S ⊆ W ∧
      ∀ (r : ℝ≥0∞), r ≠ ⊤ → 1 < r → p/2 ≤ r →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ S, ∃ a : Coeff r,
          (∀ n : ℤ, a n = (sourceActionChiGapSup hp hp1 ψ n : ℂ)) ∧ ‖a‖ ≤ L := by
  obtain ⟨V,hV,_,hφV,hVW,D,c,hD⟩ :=
    H.criticalOffsets.previous.previous.previous.roots.roots.symmetric.isolation φ hφ
  obtain ⟨S,hS,hφS,hSV,hbound⟩ := H.chiGapSup_refined_on hW hV hVW hD φ hφV
  exact ⟨S,hS,hφS,hSV.trans hVW,hbound⟩

/-- One pair of actual summand functions, chosen before every one-plus exponent. -/
theorem SourceEquation2_18Data.chiGapSup_decomposition
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hW : IsOpen W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ S : Set (CoeffPair p), IsOpen S ∧ φ ∈ S ∧ S ⊆ W ∧
      ∃ A : CoeffPair p → Coeff (p/2), ∃ B : CoeffPair p → CoeffOnePlus,
        (∀ ψ ∈ S, ∀ n : ℤ, (sourceActionChiGapSup hp hp1 ψ n : ℂ) = A ψ n+(B ψ).1 n) ∧
        (∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ S, ‖A ψ‖ ≤ L) ∧
        ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
          ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ S, ‖CoeffOnePlus.toCoeff r hr1 hr (B ψ)‖ ≤ L := by
  obtain ⟨S,hS,hφS,hSW,hbound⟩ := H.chiGapSup_refined hW φ hφ
  exact ⟨S,hS,hφS,hSW,Coeff.exists_onePlus_decomposition_of_refined S
    (fun ψ n => (sourceActionChiGapSup hp hp1 ψ n : ℂ)) (ENNReal.div_ne_top hp (by norm_num)) hbound⟩

end NLS.ZakharovShabat
