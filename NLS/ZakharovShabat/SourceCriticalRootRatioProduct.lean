import NLS.ZakharovShabat.SourceCriticalRootRatioFactorization
import NLS.ZakharovShabat.SourceSingleRootQuotientAbsolute
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic

/-!
# The literal product in equation (2.15)

The critical-root factors have absolutely summable deviations from one.
Inserting one omitted factor identifies their unconditional product with
i times the actual discriminant derivative divided by the canonical root.
This proves the printed -i normalization, even at zeros of a numerator
factor. Symmetric cutoff products converge to the same value.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual critical displacement recovers the entire indexed critical-root sequence. -/
theorem displacedRoots_canonicalCriticalDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) :
    displacedRoots (canonicalCriticalDisplacement hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ)) =
      canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) := by
  funext m
  simp only [displacedRoots,canonicalCriticalDisplacement_apply]
  ring

/-- Equation (2.15) has absolutely summable individual factor errors, without pairing. -/
theorem summable_norm_sourceCriticalRootRatio_factor_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Summable (fun m : ℤ => ‖(canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
        sourceStandardRoot hp hp1 ψ m z-1‖) := by
  simpa only [displacedRoots_canonicalCriticalDisplacement] using
    summable_norm_sourceSingleRootQuotient_error hp hp1 ψ
      (canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) z

/-- The full unordered product is i times the actual spectral quotient off all gap segments. -/
theorem sourceCriticalRootRatio_hasProd (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    HasProd (fun m : ℤ => (canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/sourceStandardRoot hp hp1 ψ m z)
      (Complex.I*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) := by
  let a := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let f (m : ℤ) := (canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/sourceStandardRoot hp hp1 ψ m z
  let Q := sourceSingleRootQuotientJointProduct hp hp1 0 (z,(a,ψ))
  have hprod : HasProd (fun m : {m : ℤ // m ≠ 0} => f m) Q := by
    simpa only [a,f,Q,displacedRoots_canonicalCriticalDisplacement] using
      hasProd_sourceSingleRootQuotient_subtype hp hp1 ψ a z 0 (fun m _ => hz m)
  have hcompl : HasProd (({0} : Set ℤ)ᶜ.domRestrict f) Q := hprod
  have hall : HasProd f (f 0*Q) := (hasProd_singleton 0 f).mul_compl hcompl
  have he : sourceCriticalRootRatioJoint hp hp1 (z,ψ) = f 0*(-Complex.I*Q) :=
    sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ 0 z hz
  have hvalue : f 0*Q = Complex.I*sourceCriticalRootRatioJoint hp hp1 (z,ψ) := by
    rw [he]
    calc
      f 0*Q = -(Complex.I*Complex.I)*(f 0*Q) := by simp
      _ = Complex.I*(f 0*(-Complex.I*Q)) := by ring
  exact hvalue ▸ hall

/-- Equation (2.15), with the literal product over all signed indices and the printed normalization. -/
theorem sourceCriticalRootRatio_product (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z =
      -Complex.I*(∏' m : ℤ, (canonicalCriticalPoints hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/sourceStandardRoot hp hp1 ψ m z) := by
  rw [(sourceCriticalRootRatio_hasProd hp hp1 ψ z hz).tprod_eq]
  change sourceCriticalRootRatioJoint hp hp1 (z,ψ) = _
  simp only [← mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul]

/-- Literal symmetric cutoff products converge to the same normalized actual quotient. -/
theorem sourceCriticalRootRatio_symmetricProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    Tendsto (fun N : ℕ => -Complex.I*(∏ m ∈ Finset.Icc (-(N : ℤ)) N,
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
        sourceStandardRoot hp hp1 ψ m z)) atTop (𝓝 (sourceCriticalRootRatioJoint hp hp1 (z,ψ))) := by
  have h := ((sourceCriticalRootRatio_hasProd hp hp1 ψ z hz).comp Finset.tendsto_Icc_neg).const_mul (-Complex.I)
  simpa only [Function.comp_def,← mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul] using h

end NLS.ZakharovShabat
