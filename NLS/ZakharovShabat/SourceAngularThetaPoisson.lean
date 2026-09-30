import NLS.ZakharovShabat.SourceAngularThetaDifferential
import NLS.Poisson.SourceFiniteBracketTransfer

/-! # Branch-independent brackets of the actual angle differentials

The global logarithmic phase differential defines the angle brackets
without choosing a modulo-pi representative. They agree with the
ordinary bracket in every analytic chart. Their formulas reduce the
canonical identities to phase brackets. The actual angle-angle bracket
is analytic, and its zero identity extends from finite real potentials
to the full real source locus in the joint open-gap domain.

This is the analytic and density part of Corollary 13.2. The finite
spectral canonical identities are still explicit hypotheses and remain
to be proved.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularThetaThetaBracket (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s ψ)
    (sourceAngularThetaDifferential hp hp1 m s ψ)

def sourceAngularThetaFunctionalBracket (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (F : CoeffPair p → ℂ) (ψ : CoeffPair p) : ℂ :=
  sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s ψ) (fderiv ℂ F ψ)

@[simp] theorem sourceAngularThetaThetaBracket_self (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2:ℝ≥0∞) ≤ p) (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) :
    sourceAngularThetaThetaBracket hp hp1 h2p n n s ψ = 0 := sourceBivector_self _ _

theorem sourceAngularThetaThetaBracket_eq_phase_bracket (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s ψ =
      (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)⁻¹*
        (2*I*sourceAngularThetaAnalyticPhase hp hp1 m s ψ)⁻¹*
          sourceBracket h2p (sourceAngularThetaAnalyticPhase hp hp1 n s)
            (sourceAngularThetaAnalyticPhase hp hp1 m s) ψ := by
  simp only [sourceAngularThetaThetaBracket,sourceAngularThetaDifferential,
    map_smul,smul_apply,smul_eq_mul,sourceBracket]
  ring

theorem sourceAngularThetaFunctionalBracket_eq_phase_bracket (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2:ℝ≥0∞) ≤ p) (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (F : CoeffPair p → ℂ) (ψ : CoeffPair p) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s F ψ =
      (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)⁻¹*
        sourceBracket h2p (sourceAngularThetaAnalyticPhase hp hp1 n s) F ψ := by
  simp only [sourceAngularThetaFunctionalBracket,sourceAngularThetaDifferential,
    map_smul,smul_apply,smul_eq_mul,sourceBracket]

theorem SourceAngularEtaAnalyticChartData.thetaFunctionalBracket_eq_chart
    {hp : p ≠ ⊤} {hp1 : 1 < p} (h2p : (2:ℝ≥0∞) ≤ p) {n : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (hbeta : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 n s) U)
    (F : CoeffPair p → ℂ) (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s F ψ =
      sourceBracket h2p (sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε) F ψ := by
  rw [sourceAngularThetaFunctionalBracket,D.thetaDifferential_eq_fderiv_representative hbeta ψ hψ]
  rfl

/-- On the nonzero phase domain, the angle-angle zero identity is exactly
the corresponding single-valued phase identity. -/
theorem sourceAngularThetaThetaBracket_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (ψ : CoeffPair p) (hn : sourceAngularThetaAnalyticPhase hp hp1 n s ψ ≠ 0)
    (hm : sourceAngularThetaAnalyticPhase hp hp1 m s ψ ≠ 0) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s ψ = 0 ↔
      sourceBracket h2p (sourceAngularThetaAnalyticPhase hp hp1 n s)
        (sourceAngularThetaAnalyticPhase hp hp1 m s) ψ = 0 := by
  have hkn : 2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hn
  have hkm : 2*I*sourceAngularThetaAnalyticPhase hp hp1 m s ψ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hm
  rw [sourceAngularThetaThetaBracket_eq_phase_bracket]
  have hprod : (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)⁻¹*
      (2*I*sourceAngularThetaAnalyticPhase hp hp1 m s ψ)⁻¹ ≠ 0 :=
    mul_ne_zero (inv_ne_zero hkn) (inv_ne_zero hkm)
  rw [mul_eq_zero]
  simp only [hprod,false_or]

/-- A prescribed mixed angle bracket is equivalent to a phase bracket,
so the canonical computation can be performed without an angle branch. -/
theorem sourceAngularThetaFunctionalBracket_eq_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2:ℝ≥0∞) ≤ p) (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (F : CoeffPair p → ℂ) (ψ : CoeffPair p) (c : ℂ)
    (hn : sourceAngularThetaAnalyticPhase hp hp1 n s ψ ≠ 0) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s F ψ = c ↔
      sourceBracket h2p (sourceAngularThetaAnalyticPhase hp hp1 n s) F ψ =
        (2*I*sourceAngularThetaAnalyticPhase hp hp1 n s ψ)*c := by
  rw [sourceAngularThetaFunctionalBracket_eq_phase_bracket]
  exact inv_mul_eq_iff_eq_mul₀ (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hn)

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)

include D

theorem analyticOnNhd_thetaThetaBracket (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ) :
    AnalyticOnNhd ℂ (sourceAngularThetaThetaBracket hp hp1 h2p n m s)
      ({ψ : CoeffPair p | ψ ∈ W ∧ canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} ∩
      {ψ : CoeffPair p | ψ ∈ W ∧ canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0}) := by
  intro ψ hψ
  exact ((sourceBivector h2p).analyticAt_bilinear _).comp₂
    (D.analyticOnNhd_thetaDifferential n ψ hψ.1) (D.analyticOnNhd_thetaDifferential m ψ hψ.2)

theorem thetaThetaBracket_eq_zero_of_finite_realType (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ)
    (hfinite : ∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) →
      Coeff.HasFiniteSupport ψ.fst → Coeff.HasFiniteSupport ψ.snd →
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0 →
        sourceAngularThetaThetaBracket hp hp1 h2p n m s ψ = 0)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s φ = 0 := by
  apply eq_of_continuousOn_of_finite_realType hp ((D.open_gap n).inter (D.open_gap m))
    (D.analyticOnNhd_thetaThetaBracket h2p n m).continuousOn 0
    (fun ψ hψ hreal hleft hright => hfinite ψ hψ.1.1 hreal hleft hright hψ.1.2 hψ.2.2)
    φ ⟨⟨hφ,hn⟩,⟨hφ,hm⟩⟩ hreal

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
