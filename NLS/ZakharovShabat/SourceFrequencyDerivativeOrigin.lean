import NLS.ZakharovShabat.SourceFrequencyOpeningOrigin
import NLS.ZakharovShabat.SourceFrequencyActionExponentCompatibility
import NLS.ComplexAnalysis.DerivativeRayLimit
import NLS.SequenceSpaces.OperatorBasisExt

/-! # The derivative of the actual action-frequency map at zero

One opened Hilbert action determines each Fourier direction. Compatibility
with larger source exponents and density of finite Fourier sums then
identify the full bounded derivative.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W P : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every differentiable action map recovering the actual frequencies
has derivative minus twice the identity at zero. No frequency Taylor
coefficient is assumed: it follows from the regular moment factors. -/
theorem sourceFrequency_fderiv_zero
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (h2p : 2 ≤ p)
    (F : Coeff q → Coeff q) (hF : DifferentiableAt ℂ F 0) (hFzero : F 0 = 0)
    (hrec : ∀ ψ : realTypeSourceSubmodule p, ∀ n,
      F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val) :
    fderiv ℂ F 0 = (-2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q) := by
  obtain ⟨W₂,V₂,_,_,hV₂,hrealV₂,s₂,hs₂,⟨A₂⟩⟩ :=
    exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨W₀₂,B₂,X₂,t₂,D₂⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  apply Coeff.continuousLinearMap_eq_of_single (Coeff.doublingExponent_ne_top hp)
  intro k
  ext n
  let v : Coeff q := lp.single q k 1
  let γ := fun a : ℝ => D₂.hilbertGapOpening 0 k a
  let ψ := fun a : ℝ => realTypeSourceExponentInclusion h2p (γ a)
  let α := fun a : ℝ => ((a^2/2 : ℝ) : ℂ)
  have hi (a : ℝ) : sourceActionSequence (q := q) hp hp1 t (ψ a).val = α a • v := by
    ext j
    rw [D.actionSequence_apply _ (D.real_subset (ψ a).property) j]
    have haction := sourceComplexAction_real_exponent (by simp) hp (by norm_num) hp1 h2p j (γ a)
    change sourceComplexAction hp hp1 j ((CoeffPair.exponentInclusion h2p) (γ a).val) = _
    rw [← haction]
    change sourceComplexAction (by simp) (by norm_num) j (D₂.hilbertGapOpening 0 k a).val = _
    rw [D₂.hilbertGapOpening_zero_source_action]
    by_cases hjk : j = k
    · subst j
      simp [α,v,lp.single_apply]
    · simp [α,v,lp.single_apply,hjk]
  have he (a : ℝ) : F (α a • v) n = A₂.renormalizedFrequency n (γ a).val := by
    have hr := hrec (ψ a) n
    rw [hi a] at hr
    exact hr.trans (A.renormalizedFrequency_real_eq_of_coefficients A₂ hs
      hs₂.toSourcePsiIsolatingComplexExtension (ψ a) (γ a) (fun _ => ⟨rfl,rfl⟩) n)
  have hα : Tendsto α (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous α := by dsimp [α]; fun_prop
    simpa only [α,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,ofReal_zero] using
      (hc.tendsto 0).mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hαne : ∀ᶠ a in 𝓝[≠] (0 : ℝ), α a ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hane : a ≠ 0 := ha
    dsimp only [α]
    exact_mod_cast div_ne_zero (pow_ne_zero 2 hane) (by norm_num : (2 : ℝ) ≠ 0)
  let L := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).comp (fderiv ℂ F 0)
  have hG : HasFDerivAt (fun b : Coeff q => F b n) L 0 := by
    exact (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).hasFDerivAt.comp 0 hF.hasFDerivAt
  have hGzero : F 0 n = 0 := by rw [hFzero]; rfl
  have hlim : Tendsto (fun a : ℝ => F (α a • v) n / α a) (𝓝[≠] 0)
      (𝓝 (if k = n then (-2 : ℂ) else 0)) := by
    simpa only [he,α,γ] using A₂.tendsto_frequency_div_opening_action
      hs₂.toSourcePsiNormalizedComplexExtension hV₂ hrealV₂ D₂ n k
  have hd := NLS.ComplexAnalysis.derivative_apply_eq_of_ray_limit
    (fun b : Coeff q => F b n) L hG hGzero v α hα hαne _ hlim
  change (fderiv ℂ F 0 v) n = if k = n then (-2 : ℂ) else 0 at hd
  change (fderiv ℂ F 0 v) n = _
  rw [hd]
  change (if k = n then (-2 : ℂ) else 0) =
    ((-2 : ℂ) • (lp.single q k 1 : Coeff q)) n
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply]
  by_cases hnk : n = k
  · subst n
    simp
  · simp [hnk,Ne.symm hnk]

end NLS.ZakharovShabat
