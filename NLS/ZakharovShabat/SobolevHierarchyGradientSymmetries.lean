import NLS.ZakharovShabat.SobolevHierarchyGradientVariation

/-! # Physical gradient covariance on the full Sobolev domain -/
noncomputable section
open Complex
namespace NLS.ZakharovShabat

theorem hierarchyL2GradientCovector_finite (s : ℕ) (g : Coeff 2 × Coeff 2)
    (a b : ℤ →₀ ℂ) :
    hierarchyL2GradientCovector s g (sobolevSourceOfFinsupp s (a,b)) =
      a.sum (fun n z => g.1 (-n)*z) + b.sum (fun n z => g.2 (-n)*z) := by
  have he (c : ℤ →₀ ℂ) : hierarchySobolevJetL2 s 0 (by omega)
      (WeightedCoeff.ofFinsupp _ 2 c) = Coeff.ofFinsupp c := by
    ext j
    simp
  simp only [hierarchyL2GradientCovector_apply, sobolevSourceOfFinsupp, he,
    Coeff.dualPairing_finite_right, Coeff.reflection_apply]

/-- Smooth Fourier modes in Hˢ determine an L² gradient uniquely. -/
theorem hierarchyL2GradientCovector_injective (s : ℕ) :
    Function.Injective (hierarchyL2GradientCovector s) := by
  intro g h he
  apply Prod.ext
  · ext n
    have hc := congrArg (fun L : SobolevSource s →L[ℂ] ℂ =>
      L (sobolevSourceOfFinsupp s (Finsupp.single (-n) 1,0))) he
    rw [hierarchyL2GradientCovector_finite, hierarchyL2GradientCovector_finite] at hc
    simpa using hc
  · ext n
    have hc := congrArg (fun L : SobolevSource s →L[ℂ] ℂ =>
      L (sobolevSourceOfFinsupp s (0,Finsupp.single (-n) 1))) he
    rw [hierarchyL2GradientCovector_finite, hierarchyL2GradientCovector_finite] at hc
    simpa using hc

theorem hierarchyL2GradientCovector_swap (s : ℕ) (g : Coeff 2 × Coeff 2) :
    hierarchyL2GradientCovector s (g.2,g.1) =
      (hierarchyL2GradientCovector s g).comp (hierarchyComponentSwap s) := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [ContinuousLinearMap.comp_apply, hierarchyComponentSwap_apply,
    hierarchyL2GradientCovector_apply, add_comm]

theorem hierarchyL2GradientCovector_scaling (s : ℕ) (g : Coeff 2 × Coeff 2) (c : ℂ) :
    hierarchyL2GradientCovector s (c • g.1,c⁻¹ • g.2) =
      (hierarchyL2GradientCovector s g).comp (hierarchyReciprocalScaling s c) := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [ContinuousLinearMap.comp_apply, hierarchyReciprocalScaling_apply,
    hierarchyL2GradientCovector_apply, map_smul, smul_apply, smul_eq_mul]

/-- The actual L²-gradient swap identity, with no smoothness restriction. -/
theorem sobolevNLSHierarchyGradient_swap (s n : ℕ) (hk : n+1 ≤ s+1)
    (ab : SobolevSource s) :
    sobolevNLSHierarchyGradient s (n+1) (hierarchyComponentSwap s ab) =
      (-1 : ℂ)^n • ((sobolevNLSHierarchyGradient s (n+1) ab).2,
        (sobolevNLSHierarchyGradient s (n+1) ab).1) := by
  have hd := fderiv_sobolevNLSHamiltonian_swap s n hk ab
  simp only [fderiv_sobolevNLSHamiltonian_eq_gradient] at hd
  rw [← hierarchyL2GradientCovector_swap, ← map_smul] at hd
  have he := hierarchyL2GradientCovector_injective s hd
  exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)

/-- The gradient transforms contragrediently under every nonzero reciprocal
field scaling, hence under each real phase rotation. -/
theorem sobolevNLSHierarchyGradient_reciprocal_scaling (s k : ℕ) (hk : k ≤ s+1)
    (ab : SobolevSource s) (c : ℂ) (hc : c ≠ 0) :
    sobolevNLSHierarchyGradient s k (hierarchyReciprocalScaling s c ab) =
      (c⁻¹ • (sobolevNLSHierarchyGradient s k ab).1,
        c • (sobolevNLSHierarchyGradient s k ab).2) := by
  have hd := fderiv_sobolevNLSHamiltonian_reciprocal_scaling s k hk ab c hc
  simp only [fderiv_sobolevNLSHamiltonian_eq_gradient] at hd
  rw [← hierarchyL2GradientCovector_scaling] at hd
  have he := hierarchyL2GradientCovector_injective s hd
  apply Prod.ext
  · have h := congrArg Prod.fst he
    have ht := congrArg (fun v : Coeff 2 => c⁻¹ • v) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using ht
  · have h := congrArg Prod.snd he
    have ht := congrArg (fun v : Coeff 2 => c • v) h
    simpa only [smul_smul, mul_inv_cancel₀ hc, one_smul] using ht

/-- Apply the physical NLS Poisson tensor -iJ to the certified L² gradient. -/
def sobolevNLSHierarchyVectorField (s k : ℕ) (ab : SobolevSource s) : Coeff 2 × Coeff 2 :=
  (-I • (sobolevNLSHierarchyGradient s k ab).2,
    I • (sobolevNLSHierarchyGradient s k ab).1)

theorem sobolevNLSHierarchyVectorField_swap (s n : ℕ) (hk : n+1 ≤ s+1)
    (ab : SobolevSource s) :
    sobolevNLSHierarchyVectorField s (n+1) (hierarchyComponentSwap s ab) =
      (-1 : ℂ)^(n+1) • ((sobolevNLSHierarchyVectorField s (n+1) ab).2,
        (sobolevNLSHierarchyVectorField s (n+1) ab).1) := by
  simp only [sobolevNLSHierarchyVectorField, sobolevNLSHierarchyGradient_swap s n hk]
  apply Prod.ext <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_smul, pow_succ] <;> congr 1 <;> ring

theorem sobolevNLSHierarchyVectorField_reciprocal_scaling (s k : ℕ) (hk : k ≤ s+1)
    (ab : SobolevSource s) (c : ℂ) (hc : c ≠ 0) :
    sobolevNLSHierarchyVectorField s k (hierarchyReciprocalScaling s c ab) =
      (c • (sobolevNLSHierarchyVectorField s k ab).1,
        c⁻¹ • (sobolevNLSHierarchyVectorField s k ab).2) := by
  simp only [sobolevNLSHierarchyVectorField,
    sobolevNLSHierarchyGradient_reciprocal_scaling s k hk ab c hc]
  apply Prod.ext <;> exact smul_comm _ _ _

end NLS.ZakharovShabat
