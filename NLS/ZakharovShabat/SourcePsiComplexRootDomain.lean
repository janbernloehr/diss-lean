import NLS.ZakharovShabat.SourcePsiComplexRootAtlas
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# A simply connected common complex domain for psi roots

The atlas domain contracts first to the real-type projection, along a
segment contained in each real-centered source ball. The real locus
then contracts to zero within itself. Consequently the common open
domain is contractible and simply connected, with every signed psi
root branch analytic and satisfying its retained contour equations.
-/

noncomputable section
open Set Metric Complex ContinuousMap
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourcePsiComplexRootAtlas.contractible_domain
    {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourcePsiComplexRootAtlas hp hp1) :
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

theorem SourcePsiComplexRootAtlas.isSimplyConnected_domain
    {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourcePsiComplexRootAtlas hp hp1) :
    IsSimplyConnected A.domain := by
  have := A.contractible_domain
  exact SimplyConnectedSpace.ofContractible A.domain

/-- All canonical psi root maps extend to one open simply connected
complex neighborhood of the entire real-type source locus. -/
theorem exists_global_sourcePsi_complexRoot_branches
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        (∀ n, AnalyticOnNhd ℂ (s n) W) ∧
        (∀ n, ∀ φ : realTypeSourceLocus p, s n φ.val = sourcePsiGapRoot hp hp1 n φ) ∧
        ∀ n, ∀ ψ ∈ W,
          ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
            sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
            ∀ m : ℤ, m ≠ n →
              sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (c m) (R m) = 0 := by
  obtain ⟨A⟩ := nonempty_sourcePsiComplexRootAtlas hp hp1
  exact ⟨A.domain,A.isOpen_domain,A.isSimplyConnected_domain,A.realType_subset_domain,
    A.branch,A.analytic,A.eq_sourcePsiGapRoot_of_real,A.contour_zero⟩

end NLS.ZakharovShabat
