import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.L2Discriminant

/-!
# The unique discriminant extension in the original source norm

Agreement is with the physical L² monodromy trace. Above two it is an
extension along the Hilbert inclusion; below two it is a restriction to the
stronger source space. Finite Fourier agreement determines the function
uniquely even among jointly continuous functions.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The classical finite-source trace is independent of the ambient exponent. -/
theorem sourceDiscriminant_finite_eq_classical (hp : p ≠ ⊤)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (CoeffPair.ofFinsupp (p := p) a)) z =
      classicalDiscriminant (finiteSourceCurve a) z := by
  rcases le_total p 2 with h | h
  · have he := sourceDiscriminant_exponent hp (by simp) h (CoeffPair.ofFinsupp (p := p) a) z
    rw [CoeffPair.exponentInclusion_ofFinsupp] at he
    exact he.trans (canonicalDiscriminant_finite_eq_classical a z)
  · have he := sourceDiscriminant_exponent (by simp) hp h (CoeffPair.ofFinsupp (p := 2) a) z
    rw [CoeffPair.exponentInclusion_ofFinsupp] at he
    exact he.symm.trans (canonicalDiscriminant_finite_eq_classical a z)

/-- Above two, the original Hilbert discriminant extends along the source inclusion. -/
theorem sourceDiscriminant_eq_l2_of_two_le (hp : p ≠ ⊤) (h2p : 2 ≤ p)
    (φ : CoeffPair 2) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z =
      l2Discriminant (sourcePhysicalL2 φ) z :=
  (sourceDiscriminant_exponent (by simp) hp h2p φ z).symm.trans
    (canonicalDiscriminant_eq_l2_source φ z)

/-- Below two, the original source discriminant is the restriction of the Hilbert trace. -/
theorem sourceDiscriminant_eq_l2_of_le_two (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ) z =
      l2Discriminant (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)) z :=
  (sourceDiscriminant_exponent hp (by simp) hp2 φ z).trans
    (canonicalDiscriminant_eq_l2_source _ z)

/-- Finite Fourier agreement determines the source discriminant at each parameter. -/
theorem sourceDiscriminant_unique_continuous (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (F : CoeffPair p → ℂ) (hF : Continuous F)
    (hfinite : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F (CoeffPair.ofFinsupp (p := p) a) = classicalDiscriminant (finiteSourceCurve a) z) :
    F = fun φ => canonicalDiscriminant hp (periodOnePotential φ) z := by
  have hc : Continuous (fun φ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential φ) z) := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    have hpair : AnalyticAt ℂ (fun ψ : CoeffPair p => (z,ψ)) φ :=
      analyticAt_const.prod analyticAt_id
    exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
      (z,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair p => (z,ψ)) hpair).continuousAt
  apply (denseRange_finiteSourcePairs hp).equalizer hF hc
  funext a
  exact (hfinite a).trans (sourceDiscriminant_finite_eq_classical hp a z).symm

/-- The jointly analytic extension is unique, even among jointly continuous candidates. -/
theorem sourceDiscriminant_unique_joint_continuous (hp : p ≠ ⊤) (hp1 : 1 < p)
    (F : ℂ × CoeffPair p → ℂ) (hF : Continuous F)
    (hfinite : ∀ z : ℂ, ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F (z,CoeffPair.ofFinsupp (p := p) a) = classicalDiscriminant (finiteSourceCurve a) z) :
    F = fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1 := by
  funext t
  exact congrFun (sourceDiscriminant_unique_continuous hp hp1 t.1 (fun φ => F (t.1,φ))
    (hF.comp (continuous_const.prodMk continuous_id)) (hfinite t.1)) t.2

end NLS.ZakharovShabat
