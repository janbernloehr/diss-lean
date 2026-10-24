import NLS.ZakharovShabat.SymmetricSignedGapFiniteProper
import NLS.ZakharovShabat.SymmetricSignedGapZeroFiber
import NLS.ZakharovShabat.SourceSquaredGapUniquenessReduction
import NLS.FunctionalAnalysis.ClosedLocalHomeomorph

/-! # Global injectivity of the actual Hilbert signed-gap map

Properness and the singleton zero fiber make each finite-output restriction
bijective. Global openness then reduces arbitrary collisions to finite-gap
collisions. The resulting actual signed-gap injectivity discharges the
remaining premise in Hilbert squared-gap spectral uniqueness.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Each finitely supported real signed-gap output has a unique symmetric Hilbert source. -/
theorem bijective_symmetricSignedGapFiniteRestriction (S : Finset ℤ) :
    Function.Bijective (symmetricSignedGapFiniteRestriction S) := by
  let a₀ : {a : RealCoeff 2 | symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈
      finiteSignedGapOutputSpace S} := ⟨0,by
    change symmetricSourceSignedGapMap (by simp) (by norm_num) 0 ∈ finiteSignedGapOutputSpace S
    rw [symmetricSourceSignedGapMap_zero_of_finite]
    exact (finiteSignedGapOutputSpace S).zero_mem⟩
  apply NLS.FunctionalAnalysis.bijective_of_closed_localHomeomorph_singleton_fiber
    (symmetricSignedGapFiniteRestriction S)
    (isLocalHomeomorph_symmetricSignedGapFiniteRestriction S)
    (isProperMap_symmetricSignedGapFiniteRestriction S).isClosedMap a₀
  intro a ha
  apply Subtype.ext
  have he := congrArg Subtype.val ha
  change symmetricSourceSignedGapMap (by simp) (by norm_num) a.val =
    symmetricSourceSignedGapMap (by simp) (by norm_num) 0 at he
  rw [symmetricSourceSignedGapMap_zero_of_finite] at he
  exact (symmetricSourceSignedGapMap_eq_zero_iff (by simp) (by norm_num) a.val).mp he

/-- The actual Hilbert signed-gap map is injective on the finite-gap locus. -/
theorem symmetricSignedGap_injOn_finiteGap :
    Set.InjOn (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num))
      {a | symmetricRealSourceCoefficients 2 a ∈ sourceFiniteGapLocus (by simp) (by norm_num)} := by
  intro a ha b _ he
  have hf := (symmetricSource_finiteGap_iff_finite_signedGap_support
    (by simp) (by norm_num) a).mp ha
  let S := hf.toFinset
  have haS : symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈
      finiteSignedGapOutputSpace S := by
    intro n hn
    by_contra hnon
    exact hn (hf.mem_toFinset.mpr hnon)
  have hbS : symmetricSourceSignedGapMap (by simp) (by norm_num) b ∈
      finiteSignedGapOutputSpace S := he ▸ haS
  have h : (⟨a,haS⟩ : {x : RealCoeff 2 | symmetricSourceSignedGapMap
      (by simp) (by norm_num) x ∈ finiteSignedGapOutputSpace S}) = ⟨b,hbS⟩ :=
    (bijective_symmetricSignedGapFiniteRestriction S).1 (Subtype.ext he)
  exact congrArg Subtype.val h

/-- The actual symmetric Hilbert signed-gap map is globally injective. -/
theorem symmetricSourceSignedGapMap_injective :
    Function.Injective (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) :=
  (symmetricSignedGap_injective_iff_finiteGap_of_isOpenMap (by simp) (by norm_num)
    isOpenMap_symmetricSourceSignedGapMap).mpr symmetricSignedGap_injOn_finiteGap

/-- Actual Hilbert squared gaps determine the full periodic spectrum with multiplicities. -/
theorem source_isospectral_of_squared_gaps
    (φ ψ : realTypeSourceSubmodule 2)
    (hgaps : ∀ n,
      (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n)^2 =
      (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem _) n)^2) :
    ψ ∈ sourceIsospectralSet (by simp) φ :=
  source_isospectral_of_squared_gaps_of_symmetricSignedGap_injective
    symmetricSourceSignedGapMap_injective φ ψ hgaps

end NLS.ZakharovShabat
