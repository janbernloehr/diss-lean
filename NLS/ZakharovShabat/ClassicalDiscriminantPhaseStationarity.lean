import NLS.ZakharovShabat.ClassicalDiscriminantCommutation

/-! # Infinitesimal phase invariance of the actual physical discriminant

The actual transported-monodromy diagonal has matching endpoint values.
Its derivative is twice the phase-gradient pairing. The fundamental
theorem of calculus therefore proves that the physical discriminant
cotangent annihilates opposite component phase rotations.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The infinitesimal opposite phase rotation with the original source
Poisson sign. It is the mass Hamiltonian direction. -/
def classicalMassHamiltonianDirection (Φ : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => (-I*(Φ t).1,I*(Φ t).2),by fun_prop⟩

/-- The actual physical discriminant is stationary in the mass
Hamiltonian direction, at every continuous complex potential. -/
theorem fderiv_classicalDiscriminant_massHamiltonianDirection_eq_zero
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ)
      (classicalMassHamiltonianDirection Φ) = 0 := by
  let f : ℝ → ℂ := fun s => 2*((extend Φ s).1*(classicalDiscriminantGradient Φ z s).1-
    (extend Φ s).2*(classicalDiscriminantGradient Φ z s).2)
  have hf : Continuous f := by
    have hΦ := continuous_extend Φ
    have hg := continuous_classicalDiscriminantGradient Φ z
    exact continuous_const.mul ((hΦ.fst.mul hg.fst).sub (hΦ.snd.mul hg.snd))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ) ≤ 1) (continuous_classicalDiscriminantDiagonal Φ z).continuousOn
    (fun s (hs : s ∈ Ioo (0:ℝ) 1) => by
      simpa only [f,NLS.LinearVolterra.extend,projIcc_of_mem _ ⟨hs.1.le,hs.2.le⟩] using
        hasDerivAt_classicalDiscriminantDiagonal Φ z ⟨s,⟨hs.1.le,hs.2.le⟩⟩)
    (hf.intervalIntegrable 0 1)
  have hzero : (∫ s in (0:ℝ)..1, f s) = 0 := by simpa using hi
  rw [fderiv_classicalDiscriminant_eq_gradient_integral]
  calc
    _ = (-I/2)*(∫ s in (0:ℝ)..1, f s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0:ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs
      simp only [classicalMassHamiltonianDirection,ContinuousMap.coe_mk,f,
        NLS.LinearVolterra.extend,projIcc_of_mem _ hs']
      ring
    _ = 0 := by rw [hzero,mul_zero]

end NLS.ZakharovShabat
