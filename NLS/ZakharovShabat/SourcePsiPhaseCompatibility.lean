import NLS.ZakharovShabat.SourcePhaseCompatibility
import NLS.ZakharovShabat.SourcePsiGapRootIsospectral
import NLS.ZakharovShabat.SourcePsiReflectionPeriods
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls
import NLS.ComplexAnalysis.OddSquareDescentCongruence

noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual source phase preserves the full real periodic spectral
data, including every algebraic multiplicity. -/
theorem sourcePhase_mem_sourceIsospectralSet (hp : p≠⊤)
    (φ : realTypeSourceSubmodule p) :
    (⟨sourcePhase φ.val,isRealType_sourcePhase φ.val φ.property⟩ : realTypeSourceSubmodule p)∈
      sourceIsospectralSet hp φ :=
  ⟨periodicSpectrum_periodOne_sourcePhase hp φ.val,
    periodicAlgebraicMultiplicity_periodOne_sourcePhase hp φ.val⟩

/-- ONE complex neighborhood precedes ALL deleted indices and ALL
frequencies and energies. The verified normalized family is unchanged by
the source phase, including the filled zero-energy numerator. -/
theorem SourceTheorem12_1Data.exists_common_sourcePhase_agreement
    {hp : p≠⊤} {hp1 : 1<p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (hW : IsOpen W)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val∈W) (hphase : sourcePhase φ.val∈W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val∈U ∧ U⊆W ∧
      (∀ ψ∈U, sourcePhase ψ∈W) ∧
      ∀ ψ∈U, ∀ n : ℤ, s n (sourcePhase ψ)=s n ψ ∧
        (∀ z : ℂ, sourceSelectedPsiNumerator s n (z,sourcePhase ψ)=
          sourceSelectedPsiNumerator s n (z,ψ)) ∧
        ∀ E : ℂ, sourcePsiEnergyNumerator s n (E,sourcePhase ψ)=
          sourcePsiEnergyNumerator s n (E,ψ) := by
  have ho := hW.inter (hW.preimage (sourcePhase (p := p)).continuous)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp ho φ.val ⟨hφ,hphase⟩
  have he (n : ℤ) : EqOn (fun ψ => s n (sourcePhase ψ)) (s n) (ball φ.val r) := by
    have hf : DifferentiableOn ℂ (fun ψ => s n (sourcePhase ψ)) (ball φ.val r) := by
      intro ψ hψ
      exact ((H.analytic n _ (hball hψ).2).comp
        (f := fun χ : CoeffPair p => sourcePhase χ) (sourcePhase.analyticAt ψ)).differentiableAt.differentiableWithinAt
    have hg : DifferentiableOn ℂ (s n) (ball φ.val r) := fun ψ hψ =>
      (H.analytic n ψ (hball hψ).1).differentiableAt.differentiableWithinAt
    have hid := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ r r
      (fun ψ => s n (sourcePhase ψ)) (s n) hf hg (fun χ _ => by
        let θ : realTypeSourceSubmodule p :=
          ⟨sourcePhase χ.val,isRealType_sourcePhase χ.val χ.property⟩
        rw [H.real_agreement n θ,H.real_agreement n χ]
        exact sourcePsiGapRoot_eq_of_isospectral hp hp1 χ θ
          (sourcePhase_mem_sourceIsospectralSet hp χ) n)
    exact fun ψ hψ => hid ⟨hψ,hψ⟩
  refine ⟨ball φ.val r,isOpen_ball,mem_ball_self hr,
    (fun ψ hψ => (hball hψ).1),(fun ψ hψ => (hball hψ).2),?_⟩
  intro ψ hψ n
  have hroot := he n hψ
  have hnum (z : ℂ) : sourceSelectedPsiNumerator s n (z,sourcePhase ψ)=
      sourceSelectedPsiNumerator s n (z,ψ) := by
    simp only [sourceSelectedPsiNumerator,sourcePsiDeletedCandidate,hroot]
  exact ⟨hroot,hnum,fun E => jointOddSquareDescent_congr_slice _ _ (sourcePhase ψ) ψ hnum E⟩

end NLS.ZakharovShabat
