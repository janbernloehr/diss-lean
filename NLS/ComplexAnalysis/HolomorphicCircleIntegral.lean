import NLS.ComplexAnalysis.ParametricCircleIntegral
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-! # Differentiating holomorphic parameter-dependent contour integrals

Complex Fréchet differentiability suffices for the circle integral
parameter derivative. The existing automatic C¹ theorem supplies the
continuous derivative and compact-circle bounds used in the proof.
No joint analyticity hypothesis is needed.
-/
noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
open scoped Interval
namespace NLS.ComplexAnalysis
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- A uniform joint derivative bound permits differentiation under the circle integral. -/
theorem hasFDerivAt_circleIntegral_of_jointDifferentiable_bound
    (F : ℂ × A → B) (D : Set (ℂ × A))
    (hDopen : IsOpen D) (hF : DifferentiableOn ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set A) (hVopen : IsOpen V) (a : A) (haV : a ∈ V)
    (M : ℝ)
    (hdom : ∀ b ∈ V, ∀ θ : ℝ, (circleMap c R θ,b) ∈ D)
    (hbound : ∀ b ∈ V, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M) :
    HasFDerivAt (fun b : A => ∮ z in C(c, R), F (z,b))
      (∫ θ in (0:ℝ)..2*Real.pi,
        (deriv (circleMap c R) θ) •
          (fderiv ℂ F (circleMap c R θ,a)).comp
            (ContinuousLinearMap.inr ℂ ℂ A)) a := by
  let J : A →L[ℂ] ℂ × A := ContinuousLinearMap.inr ℂ ℂ A
  let G : A → ℝ → B := fun b θ =>
    deriv (circleMap c R) θ • F (circleMap c R θ,b)
  let G' : A → ℝ → A →L[ℂ] B := fun b θ =>
    (deriv (circleMap c R) θ) •
      (fderiv ℂ F (circleMap c R θ,b)).comp J
  have hmap (b : A) : Continuous (fun θ : ℝ => (circleMap c R θ,b)) :=
    (continuous_circleMap c R).prodMk continuous_const
  have hderiv : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hGcont (b : A) (hb : b ∈ V) : Continuous (G b) := by
    have hsection : Continuous (fun θ : ℝ => F (circleMap c R θ,b)) :=
      hF.continuousOn.comp_continuous (hmap b) (hdom b hb)
    exact hderiv.smul hsection
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (contDiffOn_one_of_differentiableOn F hDopen hF).continuousOn_fderiv_of_isOpen
      hDopen (by norm_num)
  have hG'cont (b : A) (hb : b ∈ V) : Continuous (G' b) := by
    have hsection : Continuous (fun θ : ℝ => fderiv ℂ F (circleMap c R θ,b)) :=
      hdf.comp_continuous (hmap b) (hdom b hb)
    exact hderiv.smul (hsection.clm_comp continuous_const)
  have hmeas : ∀ᶠ b in 𝓝 a,
      AEStronglyMeasurable (G b) (volume.restrict (Ι (0:ℝ) (2*Real.pi))) :=
    by
      filter_upwards [hVopen.mem_nhds haV] with b hb
      exact (hGcont b hb).aestronglyMeasurable
  have hint : IntervalIntegrable (G a) volume 0 (2*Real.pi) :=
    (hGcont a haV).intervalIntegrable _ _
  have hmeas' : AEStronglyMeasurable (G' a)
      (volume.restrict (Ι (0:ℝ) (2*Real.pi))) :=
    (hG'cont a haV).aestronglyMeasurable
  have hderiv_bound (b : A) (hb : b ∈ V) (θ : ℝ) :
      ‖G' b θ‖ ≤ R*M := by
    have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℂ ℂ A
    have hnorm : ‖deriv (circleMap c R) θ‖ = R := by
      simp [deriv_circleMap, abs_of_nonneg hR]
    calc
      ‖G' b θ‖ = R * ‖(fderiv ℂ F (circleMap c R θ,b)).comp J‖ := by
        simp only [G', norm_smul, hnorm]
      _ ≤ R * ‖fderiv ℂ F (circleMap c R θ,b)‖ := by
        apply mul_le_mul_of_nonneg_left _ hR
        calc
          ‖(fderiv ℂ F (circleMap c R θ,b)).comp J‖ ≤
              ‖fderiv ℂ F (circleMap c R θ,b)‖ * ‖J‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖fderiv ℂ F (circleMap c R θ,b)‖ := by
            nlinarith [norm_nonneg (fderiv ℂ F (circleMap c R θ,b))]
      _ ≤ R*M := mul_le_mul_of_nonneg_left (hbound b hb θ) hR
  have hdiff (θ : ℝ) (b : A) (hb : b ∈ V) :
      HasFDerivAt (fun x : A => G x θ) (G' b θ) b := by
    have hinc : HasFDerivAt (fun x : A => (circleMap c R θ,x)) J b :=
      hasFDerivAt_prodMk_right (circleMap c R θ) b
    have hcomp := (((hF _ (hdom b hb θ)).differentiableAt (hDopen.mem_nhds (hdom b hb θ))).hasFDerivAt.comp b hinc)
    have hfun :
        (deriv (circleMap c R) θ • fun x : A => F (circleMap c R θ,x)) =
          (fun x : A => deriv (circleMap c R) θ • F (circleMap c R θ,x)) := by
      funext x
      rfl
    simpa only [G, G', Function.comp_def, hfun] using
      hcomp.const_smul (deriv (circleMap c R) θ)
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := G') (s := V) (x₀ := a) (bound := fun _ : ℝ => R*M)
    (hVopen.mem_nhds haV) hmeas hint hmeas'
    (Filter.Eventually.of_forall fun θ _ b hb => hderiv_bound b hb θ)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ b hb => hdiff θ b hb)
  change HasFDerivAt (fun b : A => ∫ θ in (0:ℝ)..2*Real.pi, G b θ)
    (∫ θ in (0:ℝ)..2*Real.pi, G' a θ) a
  exact hmain

/-- A common neighborhood bounds the derivative on a fixed compact circle. -/
theorem exists_uniform_joint_fderiv_bound_on_circle_of_differentiableOn
    (F : ℂ × A → B) (D : Set (ℂ × A))
    (hDopen : IsOpen D) (hF : DifferentiableOn ℂ F D)
    (c : ℂ) (R : ℝ) (a : A)
    (hcircle : ∀ z ∈ sphere c R, (z,a) ∈ D) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ z ∈ sphere c R, ∀ b ∈ V,
          (z,b) ∈ D ∧ ‖fderiv ℂ F (z,b)‖ ≤ M := by
  let K : Set (ℂ × A) := sphere c R ×ˢ {a}
  have hK : IsCompact K := (isCompact_sphere c R).prod isCompact_singleton
  have hKD : K ⊆ D := by
    rintro ⟨z,b⟩ ⟨hz,hb⟩
    have : b = a := hb
    subst b
    exact hcircle z hz
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (contDiffOn_one_of_differentiableOn F hDopen hF).continuousOn_fderiv_of_isOpen
      hDopen (by norm_num)
  obtain ⟨T, hKT, hTopen, hbounded⟩ :=
    exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
      hK hDopen hKD hdf
  have hKTD : K ⊆ T ∩ D := fun x hx => ⟨hKT hx, hKD hx⟩
  obtain ⟨U, V, _, hVopen, hKU, haV, hUV⟩ :=
    generalized_tube_lemma (isCompact_sphere c R) isCompact_singleton
      (hTopen.inter hDopen) hKTD
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  refine ⟨V, hVopen, haV (mem_singleton a), max 0 C,
    le_max_left _ _, ?_⟩
  intro z hz b hb
  have hzbTD : (z,b) ∈ T ∩ D := hUV ⟨hKU hz, hb⟩
  have hzbT : (z,b) ∈ T := hzbTD.1
  have hzbD : (z,b) ∈ D := hzbTD.2
  exact ⟨hzbD, (hC _ ⟨(z,b), hzbT, rfl⟩).trans (le_max_right _ _)⟩


/-- The operator-valued derivative formula for a circle integral needs only
complex differentiability on an open joint domain. -/
theorem hasFDerivAt_circleIntegral_of_jointDifferentiable
    (F : ℂ × A → B) (D : Set (ℂ × A))
    (hD : IsOpen D) (hF : DifferentiableOn ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (a : A)
    (hcircle : ∀ z ∈ sphere c R, (z,a) ∈ D) :
    HasFDerivAt (fun b : A => ∮ z in C(c,R), F (z,b))
      (∮ z in C(c,R), (fderiv ℂ F (z,a)).comp (ContinuousLinearMap.inr ℂ ℂ A)) a := by
  obtain ⟨V,hV,ha,M,_,hb⟩ :=
    exists_uniform_joint_fderiv_bound_on_circle_of_differentiableOn F D hD hF c R a hcircle
  simpa only [circleIntegral] using
    hasFDerivAt_circleIntegral_of_jointDifferentiable_bound F D hD hF c R hR V hV a ha M
      (fun b hbV θ => (hb _ (circleMap_mem_sphere c hR θ) b hbV).1)
      (fun b hbV θ => (hb _ (circleMap_mem_sphere c hR θ) b hbV).2)

end NLS.ComplexAnalysis
