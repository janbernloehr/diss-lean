import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-!
# Analyticity of fixed interval integrals in Banach parameters

Joint analyticity on a neighborhood of a compact real interval gives a
uniform bound on the parameter derivative. Differentiating under the
integral and repeating for the operator-valued derivatives proves complex
smoothness of every order, and hence an actual Banach power series.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
open scoped Interval ContDiff
namespace NLS.ComplexAnalysis

universe u
variable {A B : Type u} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

/-- A compact set of spectral points has one parameter neighborhood with
a uniform bound on the full derivative of a jointly analytic family. -/
theorem exists_uniform_joint_fderiv_bound_on_compact
    (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (K : Set ℂ) (hK : IsCompact K) (a : A)
    (hKD : ∀ z ∈ K, (z,a) ∈ D) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ K, ∀ b ∈ V, (z,b) ∈ D ∧ ‖fderiv ℂ F (z,b)‖ ≤ M := by
  have hprod : IsCompact (K ×ˢ {a}) := hK.prod isCompact_singleton
  have hsub : K ×ˢ {a} ⊆ D := by
    rintro ⟨z,b⟩ ⟨hz,hb⟩
    have : b = a := hb
    subst b
    exact hKD z hz
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (hF.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hD (by norm_num)
  obtain ⟨T,hKT,hT,hbounded⟩ :=
    exists_isOpen_isBounded_image_of_isCompact_of_continuousOn hprod hD hsub hdf
  obtain ⟨U,V,_,hV,hKU,haV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton
    (hT.inter hD) (fun x hx => ⟨hKT hx,hsub hx⟩)
  obtain ⟨C,hC⟩ := hbounded.exists_norm_le
  refine ⟨V,hV,haV (mem_singleton a),max 0 C,le_max_left _ _,?_⟩
  intro z hz b hb
  have hzb : (z,b) ∈ T ∩ D := hUV (show (z,b) ∈ U ×ˢ V from ⟨hKU hz,hb⟩)
  exact ⟨hzb.2,(hC _ ⟨(z,b),hzb.1,rfl⟩).trans (le_max_right _ _)⟩

/-- The source derivative of an interval integral is the integral of the
parameter-direction derivative, with no global derivative bound assumed. -/
theorem hasFDerivAt_intervalIntegral_of_jointAnalytic
    (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (l r : ℝ) (a : A)
    (hsegment : ∀ t ∈ uIcc l r, ((t:ℂ),a) ∈ D) :
    HasFDerivAt (fun b : A => ∫ t in l..r, F ((t:ℂ),b))
      (∫ t in l..r, (fderiv ℂ F ((t:ℂ),a)).comp
        (ContinuousLinearMap.inr ℂ ℂ A)) a := by
  let K := Complex.ofReal '' uIcc l r
  have hK : IsCompact K := isCompact_uIcc.image Complex.continuous_ofReal
  obtain ⟨V,hV,haV,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_compact
    F hD hF K hK a (by rintro z ⟨t,ht,rfl⟩; exact hsegment t ht)
  let J := ContinuousLinearMap.inr ℂ ℂ A
  let G : A → ℝ → B := fun b t => F ((t:ℂ),b)
  let G' : A → ℝ → A →L[ℂ] B := fun b t => (fderiv ℂ F ((t:ℂ),b)).comp J
  have hdom (b : A) (hb : b ∈ V) (t : ℝ) (ht : t ∈ uIcc l r) : ((t:ℂ),b) ∈ D :=
    (hbound _ ⟨t,ht,rfl⟩ b hb).1
  have hmap (b : A) : Continuous (fun t : ℝ => ((t:ℂ),b)) :=
    Complex.continuous_ofReal.prodMk continuous_const
  have hG (b : A) (hb : b ∈ V) : ContinuousOn (G b) (uIcc l r) :=
    hF.continuousOn.comp (hmap b).continuousOn (hdom b hb)
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (hF.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hD (by norm_num)
  have hG' (b : A) (hb : b ∈ V) : ContinuousOn (G' b) (uIcc l r) :=
    (hdf.comp (hmap b).continuousOn (hdom b hb)).clm_comp continuousOn_const
  have hmeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (G b) (volume.restrict (Ι l r)) := by
    filter_upwards [hV.mem_nhds haV] with b hb
    exact (intervalIntegrable_iff.mp (hG b hb).intervalIntegrable).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (G' a) (volume.restrict (Ι l r)) :=
    (intervalIntegrable_iff.mp (hG' a haV).intervalIntegrable).aestronglyMeasurable
  have hderBound (t : ℝ) (ht : t ∈ uIcc l r) (b : A) (hb : b ∈ V) : ‖G' b t‖ ≤ M := by
    calc
      ‖G' b t‖ ≤ ‖fderiv ℂ F ((t:ℂ),b)‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℂ F ((t:ℂ),b)‖ := by
        have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℂ ℂ A
        nlinarith [norm_nonneg (fderiv ℂ F ((t:ℂ),b))]
      _ ≤ M := (hbound _ ⟨t,ht,rfl⟩ b hb).2
  have hdiff (t : ℝ) (ht : t ∈ uIcc l r) (b : A) (hb : b ∈ V) :
      HasFDerivAt (fun x : A => G x t) (G' b t) b :=
    (hF _ (hdom b hb t ht)).differentiableAt.hasFDerivAt.comp b
      (hasFDerivAt_prodMk_right (t:ℂ) b)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := G') (s := V) (x₀ := a) (bound := fun _ : ℝ => M)
    (hV.mem_nhds haV) hmeas (hG a haV).intervalIntegrable hmeas'
    (Filter.Eventually.of_forall fun t ht b hb => hderBound t (uIoc_subset_uIcc ht) b hb)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht b hb => hdiff t (uIoc_subset_uIcc ht) b hb)

/-- Every finite complex differentiability order passes through a fixed
interval integral of a jointly analytic Banach-valued family. -/
theorem contDiffOn_nat_intervalIntegral_of_jointAnalytic
    (k : ℕ) (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D) (l r : ℝ)
    {V : Set A} (hV : IsOpen V)
    (hsegment : ∀ a ∈ V, ∀ t ∈ uIcc l r, ((t:ℂ),a) ∈ D) :
    ContDiffOn ℂ k (fun a : A => ∫ t in l..r, F ((t:ℂ),a)) V := by
  induction k generalizing B F D V hD hF hV hsegment with
  | zero =>
      apply contDiffOn_zero.mpr
      intro a ha
      exact (hasFDerivAt_intervalIntegral_of_jointAnalytic F hD hF l r a
        (hsegment a ha)).continuousAt.continuousWithinAt
  | succ k ih =>
      let I : A → B := fun a => ∫ t in l..r, F ((t:ℂ),a)
      let G : ℂ × A → (A →L[ℂ] B) := fun t =>
        (fderiv ℂ F t).comp (ContinuousLinearMap.inr ℂ ℂ A)
      let J : A → (A →L[ℂ] B) := fun a => ∫ t in l..r, G ((t:ℂ),a)
      have hG : AnalyticOnNhd ℂ G D := analyticOnNhd_parameterDerivative F hF
      have hI (a : A) (ha : a ∈ V) : HasFDerivAt I (J a) a :=
        hasFDerivAt_intervalIntegral_of_jointAnalytic F hD hF l r a (hsegment a ha)
      have hJ : ContDiffOn ℂ k J V := ih G hD hG hV hsegment
      have hderiv : ContDiffOn ℂ k (fderiv ℂ I) V := hJ.congr (fun a ha => (hI a ha).fderiv)
      have hs : ContDiffOn ℂ ((k : ℕ∞ω)+1) I V :=
        (contDiffOn_succ_iff_fderiv_of_isOpen hV).2
          ⟨fun a ha => (hI a ha).differentiableAt.differentiableWithinAt,by simp,hderiv⟩
      simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hs

/-- Joint analyticity passes through fixed real-interval integration on an
open parameter domain. The conclusion is full Banach-space analyticity. -/
theorem analyticOnNhd_intervalIntegral_of_jointAnalytic
    (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D) (l r : ℝ)
    {V : Set A} (hV : IsOpen V)
    (hsegment : ∀ a ∈ V, ∀ t ∈ uIcc l r, ((t:ℂ),a) ∈ D) :
    AnalyticOnNhd ℂ (fun a : A => ∫ t in l..r, F ((t:ℂ),a)) V := by
  apply analyticOnNhd_of_complexSmoothOn _ hV
  exact contDiffOn_infty.mpr (fun k =>
    contDiffOn_nat_intervalIntegral_of_jointAnalytic k F hD hF l r hV hsegment)

end NLS.ComplexAnalysis
