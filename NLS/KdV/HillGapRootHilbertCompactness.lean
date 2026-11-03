import NLS.KdV.HillGapRootHilbertCoordinates
import NLS.SequenceSpaces.RealCoeff
import NLS.SequenceSpaces.DominatedTails
import NLS.SequenceSpaces.UniformTailContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillGapRootHilbertCoordinates_majorant :
    ∃ b : Coeff 2, ∀ roots : ℕ → ℝ, ∀ hroots : roots ∈ hillGapRootBox q hq hr,
      ∀ m : ℤ, ‖hillGapRootHilbertCoordinates q hq hr roots hroots m‖ ≤ ‖b m‖ := by
  let lower : ℕ → ℝ := fun j => hillRealLabels q hq hr (2*(j+1)-1)
  let upper : ℕ → ℝ := fun j => hillRealLabels q hq hr (2*(j+1))
  have hle (j : ℕ) : lower j ≤ upper j := monotone_hillRealLabels q hq hr (by omega)
  have hlo : lower ∈ hillGapRootBox q hq hr := fun j => ⟨le_rfl,hle j⟩
  have hup : upper ∈ hillGapRootBox q hq hr := fun j => ⟨hle j,le_rfl⟩
  let L := hillGapRootHilbertCoordinates q hq hr lower hlo
  let U := hillGapRootHilbertCoordinates q hq hr upper hup
  refine ⟨RealCoeff.complexCLM 2 (lp.toNorm L+lp.toNorm U),?_⟩
  intro roots hroots m
  change ‖hillGapRootScaledOffset roots m‖ ≤ ‖((‖L m‖+‖U m‖ : ℝ) : ℂ)‖
  rw [norm_real,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  by_cases hm : 0 < m
  · have hbounds := hroots (m.toNat-1)
    have hlohi : lower (m.toNat-1) ≤ roots (m.toNat-1) ∧ roots (m.toNat-1) ≤ upper (m.toNat-1) := hbounds
    have hab : |roots (m.toNat-1)-freeHillValue m.toNat| ≤
        |lower (m.toNat-1)-freeHillValue m.toNat|+|upper (m.toNat-1)-freeHillValue m.toNat| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (lower (m.toNat-1)-freeHillValue m.toNat),abs_nonneg (upper (m.toNat-1)-freeHillValue m.toNat)]
      · linarith [le_abs_self (upper (m.toNat-1)-freeHillValue m.toNat),abs_nonneg (lower (m.toNat-1)-freeHillValue m.toNat)]
    change ‖hillGapRootScaledOffset roots m‖ ≤ ‖hillGapRootScaledOffset lower m‖+‖hillGapRootScaledOffset upper m‖
    simp only [hillGapRootScaledOffset,if_pos hm,norm_div,norm_real,Real.norm_eq_abs]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hab (norm_nonneg _)
  · simp only [hillGapRootScaledOffset,if_neg hm,norm_zero]
    positivity

theorem continuous_hillGapRootHilbertCoordinates :
    Continuous (fun roots : hillGapRootBox q hq hr =>
      hillGapRootHilbertCoordinates q hq hr roots.val roots.property) := by
  let F := fun roots : hillGapRootBox q hq hr => hillGapRootHilbertCoordinates q hq hr roots.val roots.property
  obtain ⟨b,hb⟩ := exists_hillGapRootHilbertCoordinates_majorant q hq hr
  apply continuous_iff_continuousAt.mpr
  intro roots
  apply Coeff.continuousAt_of_coordinatewise_of_uniform_tails F roots
  · intro m
    change ContinuousAt (fun roots : hillGapRootBox q hq hr => hillGapRootScaledOffset roots.val m) roots
    unfold hillGapRootScaledOffset
    by_cases hm : 0 < m
    · simp only [if_pos hm]
      have hc : Continuous (fun roots : hillGapRootBox q hq hr => roots.val (m.toNat-1)) :=
        (continuous_apply (m.toNat-1)).comp continuous_subtype_val
      have hd : Continuous (fun roots : hillGapRootBox q hq hr => roots.val (m.toNat-1)-freeHillValue m.toNat) :=
        hc.sub continuous_const
      exact ((Complex.continuous_ofReal.comp hd).div_const (m : ℂ)).continuousAt
    · simp only [if_neg hm]
      exact continuousAt_const
  · intro ε hε
    obtain ⟨s,hs⟩ := (Coeff.eventually_small_tails_of_majorant (by simp : (2 : ℝ≥0∞) ≠ ⊤) b ε hε).exists
    exact ⟨s,univ,isOpen_univ,mem_univ _,fun roots _ => (hs (F roots) (hb roots.val roots.property)).le⟩

theorem isCompact_range_hillGapRootHilbertCoordinates :
    IsCompact (range (fun roots : hillGapRootBox q hq hr =>
      hillGapRootHilbertCoordinates q hq hr roots.val roots.property)) := by
  let : CompactSpace (hillGapRootBox q hq hr) := isCompact_iff_compactSpace.mp (isCompact_hillGapRootBox q hq hr)
  exact isCompact_range (continuous_hillGapRootHilbertCoordinates q hq hr)

theorem hillGapRootHilbertCoordinates_injective :
    Function.Injective (fun roots : hillGapRootBox q hq hr =>
      hillGapRootHilbertCoordinates q hq hr roots.val roots.property) := by
  intro roots other he
  apply Subtype.ext
  funext k
  apply Complex.ofReal_injective
  rw [hillGapRootHilbertCoordinates_reconstruct q hq hr roots.val roots.property k,
    hillGapRootHilbertCoordinates_reconstruct q hq hr other.val other.property k]
  exact congrArg (fun z : ℂ => (freeHillValue (k+1 : ℕ) : ℂ)+((k+1 : ℕ) : ℂ)*z)
    (congrArg (fun a : Coeff 2 => a ((k+1 : ℕ) : ℤ)) he)

theorem isClosedEmbedding_hillGapRootHilbertCoordinates :
    IsClosedEmbedding (fun roots : hillGapRootBox q hq hr =>
      hillGapRootHilbertCoordinates q hq hr roots.val roots.property) := by
  let : CompactSpace (hillGapRootBox q hq hr) := isCompact_iff_compactSpace.mp (isCompact_hillGapRootBox q hq hr)
  exact (continuous_hillGapRootHilbertCoordinates q hq hr).isClosedEmbedding
    (hillGapRootHilbertCoordinates_injective q hq hr)

end NLS.KdV
