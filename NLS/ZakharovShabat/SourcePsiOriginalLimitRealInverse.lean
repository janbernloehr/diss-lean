import NLS.ZakharovShabat.SourcePsiOriginalLimitReal

/-!
# Bounded invertibility of the real original limit operator

Conjugation symmetry and uniqueness make the complex preimage of real
data real. The actual real lp limit operator is therefore bijective
and admits a continuous real linear inverse.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original bounded real limit operator is bijective on real lp.
Conjugation and uniqueness make the complex preimage of real data real. -/
theorem SourceLemma12_4Data.originalLimitRealOperator_bijective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W)
    (hφV : (φ:CoeffPair p) ∈ V)
    (a : RealCoeff p) (ha : RealCoeff.complexCLM p a ∈ sourcePsiOriginalRootPlacement D) :
    Function.Bijective (sourcePsiOriginalLimitRealOperator hp hp1 a φ) := by
  let Q := sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p a) φ
  have hQ := H.originalLimitOperator_bijective hW hD hV φ hφW hφV φ.property
    (RealCoeff.complexCLM p a) ha (fun k => by simp)
  have hinc (x : RealCoeff p) := H.originalLimitRealOperator_complex hD φ hφW hφV a ha x
  constructor
  · intro x y hxy
    have he : RealCoeff.complexCLM p x = RealCoeff.complexCLM p y := by
      apply hQ.1
      rw [← hinc x,← hinc y,hxy]
    simpa only [RealCoeff.reCLM_complexCLM] using congrArg (Coeff.reCLM p) he
  · intro y
    obtain ⟨x,hx⟩ := hQ.2 (RealCoeff.complexCLM p y)
    have hs : star x = x := by
      apply hQ.1
      rw [Coeff.operator_star_of_real_entries hp Q
        (H.originalLimitOperator_entry_real hD φ hφW hφV φ.property
          (RealCoeff.complexCLM p a) ha (fun k => by simp)),hx]
      ext m
      simp
    have hxReal (m : ℤ) : (x m).im = 0 :=
      Complex.conj_eq_iff_im.mp (congrArg (fun b : Coeff p => b m) hs)
    refine ⟨Coeff.reCLM p x,?_⟩
    have he := hinc (Coeff.reCLM p x)
    rw [RealCoeff.complexCLM_reCLM p x hxReal,hx] at he
    simpa only [RealCoeff.reCLM_complexCLM] using congrArg (Coeff.reCLM p) he

/-- The real original limit has a continuous linear inverse at every
point of the original real root-placement domain. -/
theorem SourceLemma12_4Data.exists_originalLimitRealEquiv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W)
    (hφV : (φ:CoeffPair p) ∈ V)
    (a : RealCoeff p) (ha : RealCoeff.complexCLM p a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ e : RealCoeff p ≃L[ℝ] RealCoeff p,
      e.toContinuousLinearMap = sourcePsiOriginalLimitRealOperator hp hp1 a φ := by
  have hb := H.originalLimitRealOperator_bijective hW hD hV φ hφW hφV a ha
  exact ⟨ContinuousLinearEquiv.ofBijective (sourcePsiOriginalLimitRealOperator hp hp1 a φ)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

end NLS.ZakharovShabat
