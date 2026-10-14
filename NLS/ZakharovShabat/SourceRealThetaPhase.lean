import NLS.ZakharovShabat.SourceAngularThetaTheorem13_1
import NLS.ZakharovShabat.SourceGapWeightedEtaAngle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The real angle modulo 2π and its analytic phase modulo π

Dividing the signed eta coordinate by the canonical gap fixes the real
angle's orientation. This phase agrees with exp(i theta) on every chart
with the canonical half-gap. Its square is the complex analytic phase.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The oriented unit phase of the real theta angle, asserted on real open gaps. -/
def sourceAngularThetaRealPhase (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) : ℂ :=
  sourceGapWeightedEtaCoordinate hp hp1 n s 1 φ /
    canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n *
      Complex.exp (Complex.I*sourceAngularBetaCorrection hp hp1 n s φ)

/-- The real angle as an actual class in ℝ/(2πℤ). -/
def sourceAngularThetaRealAngle (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) : Real.Angle :=
  (Complex.arg (sourceAngularThetaRealPhase hp hp1 n s φ) : Real.Angle)

namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {B V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

/-- Canonical half-gap charts identify the sign of exp(i theta), before squaring. -/
theorem realThetaPhase_eq_exp_representative
    (E : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (φ : CoeffPair p) (hφ : φ ∈ U)
    (hδ : δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n/2)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    sourceAngularThetaRealPhase hp hp1 n s φ =
      Complex.exp (Complex.I*sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε φ) := by
  rw [sourceAngularThetaRealPhase,E.gapWeightedEtaCoordinate_eq_gap_exp φ hφ 1 (Or.inl rfl) hδ]
  simp only [one_mul, mul_div_cancel_left₀ _ hg]
  rw [← Complex.exp_add]
  congr 1
  simp only [sourceAngularThetaCauchyRepresentative,mul_add]

/-- A real canonical chart represents the same real angle modulo 2π. -/
theorem realThetaAngle_eq_representative
    (E : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (φ : CoeffPair p) (hφ : φ ∈ U)
    (hδ : δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n/2)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0)
    (hr : (sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε φ).im = 0) :
    sourceAngularThetaRealAngle hp hp1 n s φ =
      ((sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε φ).re : Real.Angle) := by
  rw [sourceAngularThetaRealAngle,E.realThetaPhase_eq_exp_representative φ hφ hδ hg]
  have he : sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε φ =
      ((sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε φ).re : ℂ) := by
    apply Complex.ext <;> simp [hr]
  rw [he,mul_comm Complex.I,Complex.arg_exp_mul_I]
  exact Real.Angle.coe_toIocMod _ _

end SourceAngularEtaAnalyticChartData

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The real oriented phase has unit norm, and its square is the common complex phase. -/
theorem realThetaPhase_norm_and_sq (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    ‖sourceAngularThetaRealPhase hp hp1 n s φ.val‖ = 1 ∧
      (sourceAngularThetaRealPhase hp hp1 n s φ.val)^2 = sourceAngularThetaAnalyticPhase hp hp1 n s φ.val := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφ,_,hδ,E⟩ := D.local_charts n φ.val (D.real_subset φ.property) hg
  have hr := E.theta_representative_im_eq_zero_of_realType D.psi.toSourcePsiIsolatingComplexExtension
    φ.val hφ φ.property (D.correction_real φ.val (D.real_subset φ.property) φ.property n)
  rw [E.realThetaPhase_eq_exp_representative φ.val hφ hδ hg,E.theta_phase_eq_exp_representative φ.val hφ]
  constructor
  · simp [Complex.norm_exp,Complex.mul_re,hr]
  · rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- Exponentiating the real angle class recovers its oriented phase. -/
theorem exp_realThetaAngle (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    Complex.exp (Complex.I*((sourceAngularThetaRealAngle hp hp1 n s φ.val).toReal : ℂ)) =
      sourceAngularThetaRealPhase hp hp1 n s φ.val := by
  rw [sourceAngularThetaRealAngle,Complex.arg_coe_angle_toReal_eq_arg,mul_comm Complex.I]
  simpa only [(D.realThetaPhase_norm_and_sq n φ hg).1,Complex.ofReal_one,one_mul] using
    Complex.norm_mul_exp_arg_mul_I (sourceAngularThetaRealPhase hp hp1 n s φ.val)

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
