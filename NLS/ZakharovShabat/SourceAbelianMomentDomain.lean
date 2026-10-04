import NLS.ZakharovShabat.SourceAbelianMomentAtlas
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# A simply connected common domain for normalized moments

The atlas domain contracts first to the real-type projection, along a
segment contained in each real-centered source ball. The real locus
then contracts to zero within itself. Consequently the common open
domain is contractible and simply connected, with every normalized
moment analytic and satisfying the identities of Lemma 20.1.
-/

noncomputable section
open Set Metric Complex ContinuousMap
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceAbelianMomentAtlas.sourceRealPart_mem_domain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    sourceRealPart ψ ∈ A.domain := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact mem_iUnion.mpr ⟨φ,(dist_sourceRealPart_le_of_realType hp φ.val φ.property ψ).trans_lt hφ⟩

theorem SourceAbelianMomentAtlas.segment_sourceRealPart_subset_domain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    segment ℝ ψ (sourceRealPart ψ) ⊆ A.domain := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have hreal : sourceRealPart ψ ∈ A.sourceBall φ :=
    (dist_sourceRealPart_le_of_realType hp φ.val φ.property ψ).trans_lt hφ
  exact ((convex_ball φ.val (A.localChart φ).radius).segment_subset hφ hreal).trans
    (subset_iUnion A.sourceBall φ)

theorem SourceAbelianMomentAtlas.contractible_domain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) :
    ContractibleSpace A.domain := by
  let P : C(A.domain,A.domain) := {
    toFun := fun ψ => ⟨sourceRealPart ψ.val,A.sourceRealPart_mem_domain ψ.val ψ.property⟩
    continuous_toFun := ((continuous_sourceRealPart hp).comp continuous_subtype_val).subtype_mk _
  }
  have hzero : (0 : CoeffPair p) ∈ A.domain :=
    A.realType_subset_domain (by simp [realTypeSourceLocus])
  let z : A.domain := ⟨0,hzero⟩
  let H : (ContinuousMap.id A.domain).Homotopy P := {
    toFun := fun q => ⟨(1-(q.1:ℝ)) • q.2.val+(q.1:ℝ) • sourceRealPart q.2.val,by
      apply A.segment_sourceRealPart_subset_domain q.2.val q.2.property
      exact ⟨1-(q.1:ℝ),(q.1:ℝ),sub_nonneg.mpr q.1.property.2,q.1.property.1,
        sub_add_cancel _ _,rfl⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).smul
            ((continuous_sourceRealPart hp).comp (continuous_subtype_val.comp continuous_snd)))
    map_zero_left := by intro ψ; apply Subtype.ext; simp
    map_one_left := by intro ψ; apply Subtype.ext; simp [P]
  }
  let G : P.Homotopy (ContinuousMap.const A.domain z) := {
    toFun := fun q => ⟨(1-(q.1:ℝ)) • sourceRealPart q.2.val,by
      apply A.realType_subset_domain
      exact (realTypeSourceSubmodule p).smul_mem (1-(q.1:ℝ))
        (sourceRealPart_realType q.2.val)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        ((continuous_sourceRealPart hp).comp (continuous_subtype_val.comp continuous_snd))
    map_zero_left := by intro ψ; apply Subtype.ext; simp [P]
    map_one_left := by intro ψ; apply Subtype.ext; simp [z]
  }
  exact (contractible_iff_id_nullhomotopic A.domain).mpr ⟨z,⟨H.trans G⟩⟩

theorem SourceAbelianMomentAtlas.isSimplyConnected_domain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) :
    IsSimplyConnected A.domain := by
  have := A.contractible_domain
  exact SimplyConnectedSpace.ofContractible A.domain

end NLS.ZakharovShabat
