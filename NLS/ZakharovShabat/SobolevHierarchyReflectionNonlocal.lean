import NLS.ZakharovShabat.SobolevHierarchyReflectionDerivative

/-! # Corrected nonlocal recurrence on every original complex Sobolev input

Both gradients retain their original unconjugated Fourier/L2 meaning. The
spatial derivative is the actual derivative of the continuous lower gradient,
and the primitive is the literal physical integral, not a formal inverse D.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

def hierarchyPhysicalPotential (s : ℕ) (ab : SobolevSource s) (x : ℝ) : ℂ × ℂ :=
  (lowerSobolevJet s (false,0) ab (x : AddCircle (2:ℝ)),
   lowerSobolevJet s (true,0) ab (x : AddCircle (2:ℝ)))

def hierarchyPhysicalRPairing (s k : ℕ) (ab : SobolevSource s) (x : ℝ) : ℂ :=
  I*((hierarchyPhysicalPotential s ab x).1*(hierarchyPhysicalGradient s k ab x).1)-
    I*((hierarchyPhysicalPotential s ab x).2*(hierarchyPhysicalGradient s k ab x).2)

theorem hierarchyNonlocalPrimitive_eq_native_physical
    (s k : ℕ) (ab : SobolevSource s) (t : Icc (0:ℝ) 1) :
    hierarchyNonlocalPrimitive s k ab t = ∫ y in (0:ℝ)..t.val, hierarchyPhysicalRPairing s k ab y := by
  rw [hierarchyNonlocalPrimitive_eq_physical]
  apply intervalIntegral.integral_congr
  intro y hy
  have hyI : y ∈ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1] at hy
    exact ⟨hy.1,hy.2.trans t.property.2⟩
  rw [extend_coe _ ⟨y,hyI⟩]
  rfl

/-- The exact original-domain all-order corrected nonlocal identity. -/
theorem hierarchyReflection_physical_nonlocal
    (m : ℕ) (ε : ℂ) (hε : ε=1 ∨ ε = -1) (ab : SobolevSource (2*m+1))
    (hT : hierarchyMidpointReflection (2*m+1) ab=ε • ab) :
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      (I*unitL2SynthesisEquiv (sobolevNLSHierarchyGradient (2*m+1) (2*m+2) ab).1 x,
       -I*unitL2SynthesisEquiv (sobolevNLSHierarchyGradient (2*m+1) (2*m+2) ab).2 x) =
        ((deriv (hierarchyPhysicalGradient (2*m+1) (2*m+1) ab) x).1+
          2*I*(hierarchyPhysicalPotential (2*m+1) ab x).2*
            (∫ y in (0:ℝ)..x, hierarchyPhysicalRPairing (2*m+1) (2*m+1) ab y),
         (deriv (hierarchyPhysicalGradient (2*m+1) (2*m+1) ab) x).2-
          2*I*(hierarchyPhysicalPotential (2*m+1) ab x).1*
            (∫ y in (0:ℝ)..x, hierarchyPhysicalRPairing (2*m+1) (2*m+1) ab y)) := by
  filter_upwards [hierarchyReflection_physical_hasDerivAt m ε hε ab hT,
    ae_restrict_mem measurableSet_Ioc] with x hxd hx
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨hx.1.le,hx.2⟩
  have hN := hierarchyNonlocalPrimitive_eq_native_physical (2*m+1) (2*m+1) ab ⟨x,hxI⟩
  have ht₁ : extend ((hierarchyUnitPotential (2*m+1) ab).2*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab) x =
      (hierarchyPhysicalPotential (2*m+1) ab x).2*
        (∫ y in (0:ℝ)..x, hierarchyPhysicalRPairing (2*m+1) (2*m+1) ab y) := by
    rw [extend_coe _ ⟨x,hxI⟩]
    change (hierarchyPhysicalPotential (2*m+1) ab x).2*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab ⟨x,hxI⟩ = _
    rw [hN]
  have ht₂ : extend (-((hierarchyUnitPotential (2*m+1) ab).1*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab)) x =
      -((hierarchyPhysicalPotential (2*m+1) ab x).1*
        (∫ y in (0:ℝ)..x, hierarchyPhysicalRPairing (2*m+1) (2*m+1) ab y)) := by
    rw [extend_coe _ ⟨x,hxI⟩]
    change -((hierarchyPhysicalPotential (2*m+1) ab x).1*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab ⟨x,hxI⟩) = _
    rw [hN]
  rw [hxd.deriv,ht₁,ht₂]
  apply Prod.ext <;> dsimp only <;> ring

end NLS.ZakharovShabat
