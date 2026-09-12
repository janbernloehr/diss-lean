import NLS.ZakharovShabat.Operator
import NLS.Fourier.PhysicalConvolution
import NLS.Fourier.SobolevDerivative
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Physical realization of the Hilbert-space Zakharov–Shabat operator

The coefficient operator acts as `diag(i,-i) ∂ₓ + [[0,φ₋],[φ₊,0]]` on the
actual continuous `H¹` representative, for arbitrary `L²` potentials. The
identity is almost everywhere on a full physical period, as required for
classical derivatives and `L²` potentials. Interval reflection is a separate step.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- The physical representative of a base-space coefficient pair. -/
def physicalBase (φ : PairSpace 2) (x : ℝ) : ℂ × ℂ :=
  (circlePullback (l2Synthesis φ.1) x, circlePullback (l2Synthesis φ.2) x)

/-- The continuous physical representative of the one-derivative pair domain. -/
def physicalDomain (a : Domain 2) (x : ℝ) : ℂ × ℂ :=
  (sobolevSynthesis (by simp) a.1 (x : AddCircle (2 : ℝ)),
    sobolevSynthesis (by simp) a.2 (x : AddCircle (2 : ℝ)))

/-- The original differential expression, with actual component derivatives. -/
def physicalOperator (φ f : ℝ → ℂ × ℂ) (x : ℝ) : ℂ × ℂ :=
  (Complex.I * deriv (fun t => (f t).1) x + (φ x).1 * (f x).2,
    -Complex.I * deriv (fun t => (f t).2) x + (φ x).2 * (f x).1)

theorem memLp_physicalBase (φ : PairSpace 2) :
    MemLp (physicalBase φ) 2 (volume.restrict (Ioc 0 2)) :=
  memLp_prod_iff.mpr ⟨memLp_circlePullback _, memLp_circlePullback _⟩

private theorem scalar_realization (c : ℂ) (φ : Coeff 2) (a d : ScalarDomain 2) :
    circlePullback (l2Synthesis (c • derivative a + potentialMul (by simp) φ d))
      =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x : ℝ => c * deriv (fun t : ℝ => sobolevSynthesis (by simp) a
        (t : AddCircle (2 : ℝ))) x + circlePullback (l2Synthesis φ) x *
        sobolevSynthesis (by simp) d (x : AddCircle (2 : ℝ))) := by
  rw [map_add, map_smul]
  have ha := circle_ae_pullback (Lp.coeFn_add (c • l2Synthesis (derivative a))
    (l2Synthesis (potentialMul (by simp) φ d)))
  have hs := circle_ae_pullback (Lp.coeFn_smul c (l2Synthesis (derivative a)))
  filter_upwards [ha, hs, deriv_sobolevSynthesis_ae a, circlePullback_potentialMul φ d]
    with x hax hsx hdx hpx
  change deriv (fun t : ℝ => sobolevSynthesis (by simp) a (t : AddCircle (2 : ℝ))) x =
    circlePullback (l2Synthesis (derivative a)) x at hdx
  change circlePullback (c • l2Synthesis (derivative a) + l2Synthesis (potentialMul (by simp) φ d)) x =
    circlePullback (c • l2Synthesis (derivative a)) x +
      circlePullback (l2Synthesis (potentialMul (by simp) φ d)) x at hax
  change circlePullback (c • l2Synthesis (derivative a)) x = c *
    circlePullback (l2Synthesis (derivative a)) x at hsx
  rw [hax, hsx, hpx, hdx]

/-- The existing coefficient operator is exactly the physical differential expression almost everywhere. -/
theorem physical_operator_realization (φ : PairSpace 2) (a : Domain 2) :
    physicalBase (operator (by simp) φ a) =ᵐ[volume.restrict (Ioc 0 2)]
      physicalOperator (physicalBase φ) (physicalDomain a) := by
  filter_upwards [scalar_realization Complex.I φ.1 a.1 a.2,
    scalar_realization (-Complex.I) φ.2 a.2 a.1] with x h₁ h₂
  exact Prod.ext h₁ h₂

/-- The actual physical differential expression lies in the original square-integrable base space. -/
theorem memLp_physicalOperator (φ : PairSpace 2) (a : Domain 2) :
    MemLp (physicalOperator (physicalBase φ) (physicalDomain a)) 2 (volume.restrict (Ioc 0 2)) :=
  (memLp_congr_ae (physical_operator_realization φ a)).mp (memLp_physicalBase _)

private theorem scalar_inclusion_realization (a : ScalarDomain 2) :
    circlePullback (l2Synthesis (scalarInclusion a)) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) := by
  rw [← toLp_sobolevSynthesis]
  exact circle_ae_pullback (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle (sobolevSynthesis (by simp) a))

/-- The base-space and continuous representatives of a domain element agree almost everywhere. -/
theorem physicalBase_domainInclusion (a : Domain 2) :
    physicalBase (domainInclusion a) =ᵐ[volume.restrict (Ioc 0 2)] physicalDomain a := by
  filter_upwards [scalar_inclusion_realization a.1, scalar_inclusion_realization a.2] with x h₁ h₂
  exact Prod.ext h₁ h₂

/-- Scalar multiplication is respected by the physical `L²` realization. -/
theorem physicalBase_smul (c : ℂ) (φ : PairSpace 2) :
    physicalBase (c • φ) =ᵐ[volume.restrict (Ioc 0 2)] (fun x => c • physicalBase φ x) := by
  have h₁ := circle_ae_pullback (Lp.coeFn_smul c (l2Synthesis φ.1))
  have h₂ := circle_ae_pullback (Lp.coeFn_smul c (l2Synthesis φ.2))
  filter_upwards [h₁, h₂] with x hx hy
  change (circlePullback (l2Synthesis (c • φ.1)) x, circlePullback (l2Synthesis (c • φ.2)) x) = _
  rw [map_smul, map_smul]
  exact Prod.ext hx hy

/-- Equality almost everywhere on one physical period determines both coefficient sequences. -/
theorem physicalBase_injective (φ ψ : PairSpace 2)
    (h : physicalBase φ =ᵐ[volume.restrict (Ioc 0 2)] physicalBase ψ) : φ = ψ := by
  have hc {a b : Coeff 2} (he : circlePullback (l2Synthesis a)
      =ᵐ[volume.restrict (Ioc 0 2)] circlePullback (l2Synthesis b)) : a = b := by
    ext n
    have hi := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2) he) n
    simpa only [← periodTwoCoefficient_eq_fourierCoeffOn, periodTwoCoefficient_circlePullback,
      fourierCoeff_l2Synthesis] using hi
  apply Prod.ext
  · apply hc
    exact h.fun_comp Prod.fst
  · apply hc
    exact h.fun_comp Prod.snd

theorem physicalBase_zero :
    physicalBase 0 =ᵐ[volume.restrict (Ioc 0 2)] (0 : ℝ → ℂ × ℂ) := by
  have h := circle_ae_pullback (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := AddCircle.haarAddCircle))
  filter_upwards [h] with x hx
  simp [physicalBase, circlePullback]

/-- Nonzero coefficient-domain vectors give nonzero physical `L²` functions. -/
theorem physicalDomain_eq_zero_ae_iff (a : Domain 2) :
    (physicalDomain a =ᵐ[volume.restrict (Ioc 0 2)] (0 : ℝ → ℂ × ℂ)) ↔ a = 0 := by
  constructor
  · intro h
    apply domainInclusion_injective
    rw [map_zero]
    exact physicalBase_injective _ _ ((physicalBase_domainInclusion a).trans (h.trans physicalBase_zero.symm))
  · rintro rfl
    exact Filter.Eventually.of_forall fun x => by simp [physicalDomain]

/-- The coefficient eigen-equation is equivalent to the actual physical equation on a full period. -/
theorem operator_eq_smul_iff_physical (φ : PairSpace 2) (a : Domain 2) (z : ℂ) :
    operator (by simp) φ a = z • domainInclusion a ↔
      physicalOperator (physicalBase φ) (physicalDomain a)
        =ᵐ[volume.restrict (Ioc 0 2)] (fun x => z • physicalDomain a x) := by
  have hz : physicalBase (z • domainInclusion a) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x => z • physicalDomain a x) :=
    (physicalBase_smul z (domainInclusion a)).trans ((physicalBase_domainInclusion a).fun_comp (fun v => z • v))
  constructor
  · intro h
    have ho := physical_operator_realization φ a
    rw [h] at ho
    exact ho.symm.trans hz
  · intro h
    exact physicalBase_injective _ _ ((physical_operator_realization φ a).trans (h.trans hz.symm))

end NLS.ZakharovShabat
