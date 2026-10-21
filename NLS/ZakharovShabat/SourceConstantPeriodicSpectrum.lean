import NLS.ZakharovShabat.ConstantPeriodicSpectrum
import NLS.ZakharovShabat.SourceLemma6_7Counterexample
import NLS.ZakharovShabat.PeriodOneEmbedding

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original constant source depends continuously and linearly on its amplitudes. -/
def sourceConstantPotentialCLM : (ℂ × ℂ) →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p 0).prodMap
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p 0))

@[simp] theorem sourceConstantPotentialCLM_apply (a b : ℂ) :
    sourceConstantPotentialCLM (p := p) (a,b) = sourceConstantPotential a b := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext k <;>
    simp [sourceConstantPotentialCLM, lp.single_apply, Pi.single_apply]

theorem continuous_sourceConstantPotential :
    Continuous (fun v : ℂ × ℂ => sourceConstantPotential (p := p) v.1 v.2) := by
  exact (sourceConstantPotentialCLM (p := p)).continuous.congr
    (fun v => sourceConstantPotentialCLM_apply v.1 v.2)

@[simp] theorem toMax_sourceConstantPotential (a b : ℂ) :
    CoeffPair.toMax p (sourceConstantPotential a b) = constantPeriodicPair a b := by
  apply Prod.ext <;> ext k <;>
    simp [constantPeriodicPair, lp.single_apply, Pi.single_apply]

private theorem periodDouble_single_zero (a : ℂ) :
    Coeff.periodDouble (lp.single p 0 a) = lp.single p 0 a := by
  ext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, Coeff.periodDouble_even]
    simp [lp.single_apply, Pi.single_apply]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, Coeff.periodDouble_odd]
    simp [lp.single_apply, show 2*(k/2)+1 ≠ 0 by omega]

@[simp] theorem periodOnePotential_sourceConstantPotential (a b : ℂ) :
    periodOnePotential (sourceConstantPotential (p := p) a b) = constantPeriodicPair a b := by
  have hf : (sourceConstantPotential (p := p) a b).fst = lp.single p 0 a := by
    ext k; simp [lp.single_apply, Pi.single_apply]
  have hs : (sourceConstantPotential (p := p) a b).snd = lp.single p 0 b := by
    ext k; simp [lp.single_apply, Pi.single_apply]
  rw [periodOnePotential_apply, hf, hs, periodDouble_single_zero, periodDouble_single_zero]
  rfl

/-- The equation characterizes the original period-two source spectrum. -/
theorem not_mem_sourceResolventSet_constant_iff (hp : p ≠ ⊤)
    (a b z : ℂ) (ha : a ≠ 0) :
    z ∉ sourceResolventSet hp (sourceConstantPotential a b) ↔
      ∃ k : ℤ, z^2 = ((Real.pi : ℂ)*k)^2+a*b := by
  rw [sourceResolventSet_eq, toMax_sourceConstantPotential]
  exact mem_periodicSpectrum_constantPeriodicPair_iff hp a b z ha

/-- The same equation holds after the original period-one source embedding. -/
theorem mem_periodicSpectrum_sourceConstant_iff (hp : p ≠ ⊤)
    (a b z : ℂ) (ha : a ≠ 0) :
    z ∈ periodicSpectrum hp (periodOnePotential (sourceConstantPotential a b)) ↔
      ∃ k : ℤ, z^2 = ((Real.pi : ℂ)*k)^2+a*b := by
  rw [periodOnePotential_sourceConstantPotential]
  exact mem_periodicSpectrum_constantPeriodicPair_iff hp a b z ha

end NLS.ZakharovShabat
