import NLS.ZakharovShabat.ClassicalFundamentalSolution
import NLS.ZakharovShabat.HilbertDiscriminant
import NLS.ZakharovShabat.ExponentSourcePotentials

/-! # Exact monodromy for ordered triangular couplings

When the upper coupling acts before the lower coupling, the interaction
matrix is the product of two triangular matrices. The formula below uses
integrals of the actual continuous potential and gives an exact periodic
spectral criterion. No height violation or norm estimate is asserted here.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The upper integrating-factor primitive. -/
def upperInteractionPrimitive (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, I*(extend Φ s).1*exp (2*I*z*s)

/-- The lower integrating-factor primitive, with the original sign. -/
def lowerInteractionPrimitive (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, -I*(extend Φ s).2*exp (-2*I*z*s)

@[simp] theorem upperInteractionPrimitive_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    upperInteractionPrimitive Φ z 0 = 0 := by simp [upperInteractionPrimitive]

@[simp] theorem lowerInteractionPrimitive_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    lowerInteractionPrimitive Φ z 0 = 0 := by simp [lowerInteractionPrimitive]

theorem hasDerivAt_upperInteractionPrimitive (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    HasDerivAt (upperInteractionPrimitive Φ z) (I*(extend Φ t).1*exp (2*I*z*t)) t := by
  have hc : Continuous (fun s : ℝ => I*(extend Φ s).1*exp (2*I*z*s)) := by
    have := continuous_extend Φ
    fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem hasDerivAt_lowerInteractionPrimitive (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    HasDerivAt (lowerInteractionPrimitive Φ z) (-I*(extend Φ t).2*exp (-2*I*z*t)) t := by
  have hc : Continuous (fun s : ℝ => -I*(extend Φ s).2*exp (-2*I*z*s)) := by
    have := continuous_extend Φ
    fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The potential has only its upper component before a cut, and only its lower component after it. -/
def HasOrderedTriangularSupport (Φ : Curve (ℂ × ℂ)) (c : ℝ) : Prop :=
  ∀ t : Icc (0 : ℝ) 1, (t.val ≤ c → (Φ t).2 = 0) ∧ (c ≤ t.val → (Φ t).1 = 0)

/-- The explicit product of the two interaction matrices, applied to initial data. -/
def orderedTriangularSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  (exp (-I*z*t)*(v.1+upperInteractionPrimitive Φ z t*v.2),
   exp (I*z*t)*(lowerInteractionPrimitive Φ z t*v.1+
     (1+upperInteractionPrimitive Φ z t*lowerInteractionPrimitive Φ z t)*v.2))

@[simp] theorem orderedTriangularSolution_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    orderedTriangularSolution Φ z v 0 = v := by simp [orderedTriangularSolution]

/-- A vanishing upper-coupling/lower-primitive product is the precise interaction condition. -/
theorem classicalSolution_eq_orderedTriangular_of_vanishing (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hcross : ∀ t : Icc (0 : ℝ) 1, (Φ t).1*lowerInteractionPrimitive Φ z t = 0)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z v t = orderedTriangularSolution Φ z v t := by
  have he (c : ℂ) (s : ℝ) : HasDerivAt (fun x : ℝ => exp (c*x)) (exp (c*s)*c) s := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul c).cexp
  have hd (s : ℝ) := ((he (-I*z) s).mul
      ((hasDerivAt_upperInteractionPrimitive Φ z s).mul_const v.2 |>.const_add v.1)).prodMk
    ((he (I*z) s).mul (((hasDerivAt_lowerInteractionPrimitive Φ z s).mul_const v.1).add
      ((((hasDerivAt_upperInteractionPrimitive Φ z s).mul
        (hasDerivAt_lowerInteractionPrimitive Φ z s)).const_add 1).mul_const v.2)))
  have hu : ContinuousOn (orderedTriangularSolution Φ z v) (Icc 0 1) := by
    intro s _
    exact (hd s).continuousAt.continuousWithinAt
  have h := classicalSolution_unique Φ z v (orderedTriangularSolution Φ z v) hu
    (orderedTriangularSolution_zero Φ z v) (by
      intro s _
      have hE₁ : exp (-I*z*s.val)*exp (2*I*z*s.val) = exp (I*z*s.val) := by
        rw [← exp_add]; congr 1; ring
      have hE₂ : exp (I*z*s.val)*exp (-2*I*z*s.val) = exp (-I*z*s.val) := by
        rw [← exp_add]; congr 1; ring
      have hc := hcross s
      convert! hd s.val using 1
      simp only [extend_coe, orderedTriangularSolution, classicalODECoefficient_apply]
      apply Prod.ext
      · dsimp
        linear_combination (norm := ring_nf)
          (-I*(Φ s).1*v.2)*hE₁ +
          (I*exp (I*z*s.val)*(v.1+upperInteractionPrimitive Φ z s.val*v.2))*hc
      · dsimp
        linear_combination (norm := ring_nf)
          (I*(Φ s).2*(v.1+upperInteractionPrimitive Φ z s.val*v.2))*hE₂ -
          (I*exp (I*z*s.val)*exp (2*I*z*s.val)*v.2)*hc)
  exact (h t.property).symm

/-- Before the cut, the lower integrating-factor primitive is zero. -/
theorem lowerInteractionPrimitive_eq_zero_before_cut (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    {c : ℝ} (hΦ : HasOrderedTriangularSupport Φ c) (t : Icc (0 : ℝ) 1) (ht : t.val ≤ c) :
    lowerInteractionPrimitive Φ z t = 0 := by
  unfold lowerInteractionPrimitive
  calc
    _ = ∫ _s in (0 : ℝ)..t.val, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.property.1] at hs
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
      dsimp only
      rw [show extend Φ s = Φ ⟨s,hs1⟩ from extend_coe Φ ⟨s,hs1⟩,
        (hΦ ⟨s,hs1⟩).1 (hs.2.trans ht)]
      simp
    _ = 0 := by simp

/-- Ordered supports imply the exact vanishing interaction used by the solution formula. -/
theorem upper_mul_lowerPrimitive_eq_zero_of_ordered (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    {c : ℝ} (hΦ : HasOrderedTriangularSupport Φ c) (t : Icc (0 : ℝ) 1) :
    (Φ t).1*lowerInteractionPrimitive Φ z t = 0 := by
  by_cases ht : t.val ≤ c
  · rw [lowerInteractionPrimitive_eq_zero_before_cut Φ z hΦ t ht, mul_zero]
  · rw [(hΦ t).2 (le_of_not_ge ht), zero_mul]

/-- The two scalar primitives determine the actual solution for ordered triangular supports. -/
theorem classicalSolution_eq_orderedTriangular (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    {c : ℝ} (hΦ : HasOrderedTriangularSupport Φ c) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z v t = orderedTriangularSolution Φ z v t :=
  classicalSolution_eq_orderedTriangular_of_vanishing Φ z
    (upper_mul_lowerPrimitive_eq_zero_of_ordered Φ z hΦ) v t

/-- Exact monodromy, including both off-diagonal entries and their interaction term. -/
theorem classicalMonodromy_orderedTriangular (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    {c : ℝ} (hΦ : HasOrderedTriangularSupport Φ c) :
    classicalMonodromy Φ z =
      !![exp (-I*z), exp (-I*z)*upperInteractionPrimitive Φ z 1;
         exp (I*z)*lowerInteractionPrimitive Φ z 1,
         exp (I*z)*(1+upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1)] := by
  unfold classicalMonodromy classicalFundamentalMatrix
  rw [classicalSolution_eq_orderedTriangular Φ z hΦ (1,0) ⟨1,by constructor <;> norm_num⟩,
    classicalSolution_eq_orderedTriangular Φ z hΦ (0,1) ⟨1,by constructor <;> norm_num⟩]
  simp [orderedTriangularSolution]

/-- The actual trace includes the product of the two spatially separated couplings. -/
theorem classicalDiscriminant_orderedTriangular (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    {c : ℝ} (hΦ : HasOrderedTriangularSupport Φ c) :
    classicalDiscriminant Φ z = exp (-I*z)+exp (I*z)*
      (1+upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1) := by
  rw [classicalDiscriminant, classicalMonodromy_orderedTriangular Φ z hΦ]
  simp [Matrix.trace_fin_two]

/-- Both Floquet signs reduce to one exact scalar interaction equation. -/
theorem classicalDiscriminant_orderedTriangular_level_iff (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    {c : ℝ} (hΦ : HasOrderedTriangularSupport Φ c) (σ : ℂ) (hσ : σ^2 = 1) :
    classicalDiscriminant Φ z = 2*σ ↔
      upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 = -(exp (-I*z)-σ)^2 := by
  rw [classicalDiscriminant_orderedTriangular Φ z hΦ]
  have he : exp (-I*z)*exp (I*z) = 1 := by rw [← exp_add]; simp
  constructor
  · intro h
    linear_combination exp (-I*z)*h -
      (1+upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1)*he + hσ
  · intro h
    linear_combination exp (I*z)*h - (exp (-I*z)-2*σ)*he - exp (I*z)*hσ

/-- The same scalar equation characterizes actual source periodic spectral points
at every finite exponent at least two, retaining the original coefficients. -/
theorem source_mem_periodicSpectrum_orderedTriangular_iff
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hphysical : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    {c : ℝ} (hΦ : HasOrderedTriangularSupport Φ c) (z : ℂ) :
    z ∈ periodicSpectrum hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) ↔
      upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 = -(exp (-I*z)-1)^2 ∨
      upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 = -(exp (-I*z)+1)^2 := by
  rw [← periodOnePotential_exponent,
    ← periodicSpectrum_exponent (by simp) hp h2p,
    ← canonicalDiscriminant_sq_eq_four_iff _ (periodOnePotential_mem φ),
    canonicalDiscriminant_eq_classical _ (periodOnePotential_mem φ) Φ hphysical]
  have he : (classicalDiscriminant Φ z)^2 = 4 ↔
      classicalDiscriminant Φ z = 2 ∨ classicalDiscriminant Φ z = -2 := by
    rw [show (4 : ℂ) = (2 : ℂ)^2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg]
  rw [he]
  have hplus := classicalDiscriminant_orderedTriangular_level_iff Φ z hΦ 1 (by norm_num)
  have hminus := classicalDiscriminant_orderedTriangular_level_iff Φ z hΦ (-1) (by norm_num)
  norm_num only [mul_one, mul_neg, sub_neg_eq_add] at hplus hminus
  exact or_congr hplus hminus

end NLS.ZakharovShabat

