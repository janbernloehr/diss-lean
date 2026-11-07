import NLS.ZakharovShabat.ClassicalBoundaryMonodromy

/-! # Arbitrary reciprocal field scaling of the physical ZS equation

The diagonal state gauge proves the actual normalized fundamental-matrix
identity for every nonzero complex scaling. Real phase rotations are a
special case; no spectral invariance is assumed in the proof.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalReciprocalScaling (c : ℂ) (Φ : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => (c*(Φ t).1,c⁻¹*(Φ t).2),by fun_prop⟩

@[simp] theorem classicalReciprocalScaling_apply (c : ℂ) (Φ : Curve (ℂ × ℂ))
    (t : Icc (0:ℝ) 1) :
    classicalReciprocalScaling c Φ t = (c*(Φ t).1,c⁻¹*(Φ t).2) := rfl

theorem classicalSolution_reciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalSolution (classicalReciprocalScaling c Φ) z (c*v.1,v.2) t =
      (c*(classicalSolution Φ z v t).1,(classicalSolution Φ z v t).2) := by
  let u : ℝ → ℂ × ℂ := fun x =>
    (c*(classicalSolution Φ z v x).1,(classicalSolution Φ z v x).2)
  have hu : ContinuousOn u (Icc 0 1) :=
    ((continuous_const.mul (continuous_classicalSolution Φ z v).fst).prodMk
      (continuous_classicalSolution Φ z v).snd).continuousOn
  have h0 : u 0 = (c*v.1,v.2) := by simp [u]
  have hd (x : Icc (0:ℝ) 1) (_ : x.val ∈ Ioo (0:ℝ) 1) :
      HasDerivAt u (classicalODECoefficient (classicalReciprocalScaling c Φ x) z (u x)) x := by
    have h := hasDerivAt_classicalSolution Φ z v x
    have hh := ((HasFDerivAt.hasDerivAt h.fst).const_mul c).prodMk
      (HasFDerivAt.hasDerivAt h.snd)
    convert! hh using 1
    apply Prod.ext <;>
      simp only [u,classicalReciprocalScaling_apply,classicalODECoefficient_apply,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
    · dsimp
      ring
    · dsimp
      field_simp [hc]
  exact (classicalSolution_unique (classicalReciprocalScaling c Φ) z (c*v.1,v.2)
    u hu h0 hd t.property).symm

/-- The normalized fundamental matrix has the exact diagonal gauge,
including the off-diagonal factors, at every point of the closed interval. -/
theorem classicalFundamentalMatrix_reciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0:ℝ) 1) :
    classicalFundamentalMatrix (classicalReciprocalScaling c Φ) z t =
      !![(classicalFundamentalMatrix Φ z t) 0 0,c*(classicalFundamentalMatrix Φ z t) 0 1;
        c⁻¹*(classicalFundamentalMatrix Φ z t) 1 0,(classicalFundamentalMatrix Φ z t) 1 1] := by
  have h1 := classicalSolution_reciprocalScaling c hc Φ z (1,0) t
  have h2 := classicalSolution_reciprocalScaling c hc Φ z (0,1) t
  have hinit : (c*(1:ℂ), (0:ℂ)) = c • ((1,0):ℂ × ℂ) := by simp
  rw [hinit,classicalSolution_smul] at h1
  have h00 : (classicalSolution (classicalReciprocalScaling c Φ) z (1,0) t).1 =
      (classicalSolution Φ z (1,0) t).1 := by
    exact mul_left_cancel₀ hc (congrArg Prod.fst h1)
  have h10 : (classicalSolution (classicalReciprocalScaling c Φ) z (1,0) t).2 =
      c⁻¹*(classicalSolution Φ z (1,0) t).2 := by
    have h := congrArg Prod.snd h1
    change c*(classicalSolution (classicalReciprocalScaling c Φ) z (1,0) t).2 = _ at h
    have ht := congrArg (fun w : ℂ => c⁻¹*w) h
    simpa only [← mul_assoc,inv_mul_cancel₀ hc,one_mul] using ht
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · simpa [classicalFundamentalMatrix] using congrArg Prod.fst h2
  · exact h10
  · simpa [classicalFundamentalMatrix] using congrArg Prod.snd h2

theorem classicalDiscriminant_reciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant (classicalReciprocalScaling c Φ) z = classicalDiscriminant Φ z := by
  unfold classicalDiscriminant classicalMonodromy
  rw [classicalFundamentalMatrix_reciprocalScaling c hc Φ z ⟨1,by norm_num⟩]
  simp [Matrix.trace_fin_two]

end NLS.ZakharovShabat
