import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics

/-! # Spatial reflection with component swap

Reversing the interval and swapping the potential components preserves the
spectral parameter. The actual normalized monodromy has unchanged diagonal
entries and negative swapped off-diagonal entries. Consequently both
separated characteristics and the discriminant are preserved, while the
anti-discriminant changes sign.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Reflection about the midpoint, with the component swap required by the first-order system. -/
def classicalSpatialReflection (Φ : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => (Φ ⟨1-t.val, by constructor <;> linarith [t.property.1,t.property.2]⟩).swap,
    by fun_prop⟩

@[simp] theorem classicalSpatialReflection_apply (Φ : Curve (ℂ × ℂ))
    (t : Icc (0 : ℝ) 1) :
    classicalSpatialReflection Φ t =
      (Φ ⟨1-t.val, by constructor <;> linarith [t.property.1,t.property.2]⟩).swap := rfl

@[simp] theorem classicalSpatialReflection_involutive (Φ : Curve (ℂ × ℂ)) :
    classicalSpatialReflection (classicalSpatialReflection Φ) = Φ := by
  apply ContinuousMap.ext
  intro t
  simp only [classicalSpatialReflection_apply,Prod.swap_swap]
  congr 1
  apply Subtype.ext
  simp

/-- Reflection preserves the original differential equation after the component swap. -/
theorem classicalODECoefficient_spatialReflection (φ y : ℂ × ℂ) (z : ℂ) :
    -(classicalODECoefficient φ z y).swap = classicalODECoefficient φ.swap z y.swap := by
  apply Prod.ext <;> simp [classicalODECoefficient_apply]

/-- The reflected original solution starts at the swapped terminal value. -/
theorem classicalSolution_spatialReflection (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution (classicalSpatialReflection Φ) z (classicalSolution Φ z v 1).swap t =
      (classicalSolution Φ z v (1-t.val)).swap := by
  let u : ℝ → ℂ × ℂ := fun x => (classicalSolution Φ z v (1-x)).swap
  have hu : ContinuousOn u (Icc 0 1) := by
    exact (((continuous_classicalSolution Φ z v).comp (continuous_const.sub continuous_id)).snd.prodMk
      ((continuous_classicalSolution Φ z v).comp (continuous_const.sub continuous_id)).fst).continuousOn
  have h0 : u 0 = (classicalSolution Φ z v 1).swap := by simp [u]
  have hd (x : Icc (0 : ℝ) 1) (_ : x.val ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt u (classicalODECoefficient (classicalSpatialReflection Φ x) z (u x)) x := by
    let y : Icc (0 : ℝ) 1 := ⟨1-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩
    have h : HasDerivAt (classicalSolution Φ z v)
        (classicalODECoefficient (Φ y) z (classicalSolution Φ z v y)) (1-x.val) := by
      convert hasDerivAt_classicalSolution Φ z v y using 1
    have hinner : HasDerivAt (fun t : ℝ => 1-t) (-1 : ℝ) x.val :=
      (hasDerivAt_id x.val).const_sub 1
    have hc := h.scomp x.val hinner
    have hf := (HasFDerivAt.hasDerivAt hc.snd).prodMk (HasFDerivAt.hasDerivAt hc.fst)
    convert! hf using 1
    apply Prod.ext <;> simp [u,y,classicalODECoefficient_apply]
  exact (classicalSolution_unique (classicalSpatialReflection Φ) z
    (classicalSolution Φ z v 1).swap u hu h0 hd t.property).symm

/-- The full original monodromy transforms without changing the spectral parameter. -/
theorem classicalMonodromy_spatialReflection (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalMonodromy (classicalSpatialReflection Φ) z =
      !![(classicalMonodromy Φ z) 0 0, -(classicalMonodromy Φ z) 1 0;
        -(classicalMonodromy Φ z) 0 1, (classicalMonodromy Φ z) 1 1] := by
  let M := classicalMonodromy Φ z
  let R := classicalMonodromy (classicalSpatialReflection Φ) z
  have h₁ := classicalSolution_spatialReflection Φ z (1,0) ⟨1,by norm_num⟩
  have h₂ := classicalSolution_spatialReflection Φ z (0,1) ⟨1,by norm_num⟩
  rw [classicalSolution_eq_columns _ _ _ ⟨1,by norm_num⟩] at h₁ h₂
  have ha : R 0 0 * M 1 0 + R 0 1 * M 0 0 = 0 := by
    simpa [R,M,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.fst h₁
  have hb : R 1 0 * M 1 0 + R 1 1 * M 0 0 = 1 := by
    simpa [R,M,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.snd h₁
  have hc : R 0 0 * M 1 1 + R 0 1 * M 0 1 = 1 := by
    simpa [R,M,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.fst h₂
  have hd : R 1 0 * M 1 1 + R 1 1 * M 0 1 = 0 := by
    simpa [R,M,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.snd h₂
  have he : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa [M,Matrix.det_fin_two] using det_classicalMonodromy Φ z
  change R = !![M 0 0, -M 1 0; -M 0 1, M 1 1]
  ext i j
  fin_cases i <;> fin_cases j
  · change R 0 0 = M 0 0
    linear_combination M 0 0 * hc - M 0 1 * ha - R 0 0 * he
  · change R 0 1 = -M 1 0
    linear_combination M 1 1 * ha - M 1 0 * hc - R 0 1 * he
  · change R 1 0 = -M 0 1
    linear_combination M 0 0 * hd - M 0 1 * hb - R 1 0 * he
  · change R 1 1 = M 1 1
    linear_combination M 1 1 * hb - M 1 0 * hd - R 1 1 * he

@[simp] theorem classicalDiscriminant_spatialReflection (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant (classicalSpatialReflection Φ) z = classicalDiscriminant Φ z := by
  simp [classicalDiscriminant,classicalMonodromy_spatialReflection,Matrix.trace_fin_two]

@[simp] theorem classicalSeparatedCharacteristic_spatialReflection (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSeparatedCharacteristic b (classicalSpatialReflection Φ) z =
      classicalSeparatedCharacteristic b Φ z := by
  simp only [classicalSeparatedCharacteristic,classicalMonodromy_spatialReflection,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

@[simp] theorem classicalAntiDiscriminant_spatialReflection (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAntiDiscriminant (classicalSpatialReflection Φ) z = -classicalAntiDiscriminant Φ z := by
  simp [classicalAntiDiscriminant,classicalMonodromy_spatialReflection]

end NLS.ZakharovShabat
