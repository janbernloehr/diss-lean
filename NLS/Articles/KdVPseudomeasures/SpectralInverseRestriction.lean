import NLS.Articles.KdVPseudomeasures.SpectralRealAdapted
import NLS.Fourier.PeriodicWeightCongruence

/-! The actual adapted Fourier map and inverse regularity in the original
unweighted and weighted distribution spaces,with no change of frequency or norm. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The original unweighted endpoint space is isometrically the source unit-weight space. -/
def sourceUnitWeightEquiv (r : ℝ) : FourierLebesgueSpace (2:ℝ) (-r) ⊤ ≃ₗᵢ[ℂ]
    PeriodicFourierLebesgue (2:ℝ) (SpectralWeight.one.negativeSobolev r) ⊤ :=
  weightCongr _ _ (fun k => by simp only [SpectralWeight.negativeSobolev_eq_product,
    SpectralWeight.one_apply, one_mul])

@[simp] theorem sourceUnitWeightEquiv_val (r : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    (sourceUnitWeightEquiv r q).val = q.val := weightCongr_val _ _ _ q

@[simp] theorem sourceUnitWeightEquiv_symm_val (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (SpectralWeight.one.negativeSobolev r) ⊤) :
    ((sourceUnitWeightEquiv r).symm q).val = q.val := by
  have hh := sourceUnitWeightEquiv_val r ((sourceUnitWeightEquiv r).symm q)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  exact hh.symm

/-- Forgetting the unit extra weight is exactly this isometric inverse. -/
theorem sourceForgetUnitWeight_eq (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (SpectralWeight.one.negativeSobolev r) ⊤) :
    sourceForgetWeight SpectralWeight.one r q = (sourceUnitWeightEquiv r).symm q := by
  apply Subtype.ext
  rw [sourceForgetWeight_val, sourceUnitWeightEquiv_symm_val]

/-- The actual adapted map on the EXACT original unweighted endpoint Banach space. -/
def sourceAdaptedFourier (r : ℝ) (hr : AdmissiblePredualOrder r) (N : ℕ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : FourierLebesgueSpace (2:ℝ) (-r) ⊤ :=
  (sourceUnitWeightEquiv r).symm (sourceWeightedAdaptedFourier SpectralWeight.one r hr N (sourceUnitWeightEquiv r q))

@[simp] theorem sourceAdaptedFourier_val (r : ℝ) (hr : AdmissiblePredualOrder r) (N : ℕ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    (sourceAdaptedFourier r hr N q).val =
      (sourceWeightedAdaptedFourier SpectralWeight.one r hr N (sourceUnitWeightEquiv r q)).val :=
  sourceUnitWeightEquiv_symm_val r _

/-- Every actual weighted restriction represents the SAME original adapted distribution. -/
theorem sourceAdaptedFourier_weight_agreement (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ R) :
    (sourceAdaptedFourier r hr N (sourceForgetWeight w r q)).val =
      (sourceWeightedAdaptedFourier w r hr N q).val := by
  rw [sourceAdaptedFourier_val]
  apply sourceWeightedAdaptedFourier_weight_agreement SpectralWeight.one w r hr N R hR hcut
  · exact ((sourceUnitWeightEquiv r).norm_map _).trans_le ((norm_sourceForgetWeight_le w r q).trans hq)
  · exact hq
  · rw [sourceUnitWeightEquiv_val, sourceForgetWeight_val]

/-- The unweighted map has exactly the original actual adapted Fourier values. -/
theorem sourceAdaptedFourier_coefficients (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (k : ℤ) :
    (sourceAdaptedFourier r hr N q).val (mode (-k)) = sourceAdaptedFourierValues r hr N q k := by
  have hv := (sourceWeightedAdaptedFourier_spec SpectralWeight.one r hr N R hR hcut
    (sourceUnitWeightEquiv r q) (((sourceUnitWeightEquiv r).norm_map q).trans_le hq)).1 k
  simpa only [sourceAdaptedFourier_val, sourceForgetUnitWeight_eq,
    LinearIsometryEquiv.symm_apply_apply] using hv

/-- Analyticity is in the EXACT original unweighted endpoint norm. -/
theorem analyticOnNhd_sourceAdaptedFourier (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (R : ℝ) (hR : 0 < R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2) :
    AnalyticOnNhd ℂ (sourceAdaptedFourier r hr N) (ball 0 R) := by
  intro q hq
  have hqu : sourceUnitWeightEquiv r q ∈ ball 0 R := by
    simpa only [mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using mem_ball_zero_iff.mp hq
  have hA := analyticOnNhd_sourceWeightedAdaptedFourier SpectralWeight.one r hr N R hR hcut _ hqu
  have hi := (sourceUnitWeightEquiv r).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt q
  exact ((sourceUnitWeightEquiv r).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    (hA.comp (f := (sourceUnitWeightEquiv r).toContinuousLinearEquiv.toContinuousLinearMap) hi)

/-- One cutoff BEFORE BOTH weight and original potential gives genuine inverse
regularity gain from the adapted image. The supplied source need not already
belong to the stronger weighted space. -/
theorem source_uniform_weighted_inverse_restriction (r : ℝ) (hr : AdmissiblePredualOrder r)
    (m : ℝ) (hm : 0 < m) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*(2*m)) ≤ 1/2) ∧
      ∀ w : SpectralWeight,
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ m →
      ∀ y : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖y‖ ≤ m/2 →
        y.val = (sourceAdaptedFourier r hr N q).val →
        ∃ p : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, p.val = q.val ∧ ‖p‖ ≤ m := by
  obtain ⟨N, hN, hcut, hmap⟩ := source_uniform_adaptedFourier_inverse r hr m hm
  obtain ⟨_, _, _, _, hinj, _, _, _⟩ := hmap SpectralWeight.one
  refine ⟨N, hN, hcut, fun w q hq y hy hval => ?_⟩
  obtain ⟨_, _, g, _, _, hright, _, _⟩ := hmap w
  obtain ⟨hpm, he⟩ := hright y (by linarith)
  have hp : ‖g y‖ ≤ m := (mem_ball_zero_iff.mp hpm).le
  have hpu : ‖sourceUnitWeightEquiv r (sourceForgetWeight w r (g y))‖ ≤ m :=
    ((sourceUnitWeightEquiv r).norm_map _).trans_le ((norm_sourceForgetWeight_le w r (g y)).trans hp)
  have hqu : ‖sourceUnitWeightEquiv r q‖ ≤ m := ((sourceUnitWeightEquiv r).norm_map q).trans_le hq
  have hforward : (sourceAdaptedFourier r hr N (sourceForgetWeight w r (g y))).val = y.val := by
    rw [sourceAdaptedFourier_weight_agreement w r hr N (2*m) (by positivity) hcut (g y) (by linarith), he]
  have heq : sourceUnitWeightEquiv r (sourceForgetWeight w r (g y)) = sourceUnitWeightEquiv r q := by
    apply hinj
      (by simpa only [mem_closedBall, dist_zero_right] using hpu)
      (by simpa only [mem_closedBall, dist_zero_right] using hqu)
    apply Subtype.ext
    simpa only [sourceAdaptedFourier_val] using hforward.trans hval
  have hdist := congrArg Subtype.val heq
  simp only [sourceUnitWeightEquiv_val, sourceForgetWeight_val] at hdist
  exact ⟨g y, hdist, hp⟩

/-- Source Proposition2.19 in literal original-distribution membership and norm
form. The exact adapted image is in the CLOSED stronger half-ball;the same
original source distribution then lies in the CLOSED stronger source ball. -/
theorem sourceProposition2_19 (r : ℝ) (hr : AdmissiblePredualOrder r) (m : ℝ) (hm : 1 ≤ m) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ m →
      ∀ hy : (sourceAdaptedFourier r hr N q).val ∈
        periodicFourierLebesgueSubmodule (w.negativeSobolev r) ⊤,
        let y : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ :=
          ⟨(sourceAdaptedFourier r hr N q).val, hy⟩
        ‖y‖ ≤ m/2 →
        ∃ hq : q.val ∈ periodicFourierLebesgueSubmodule (w.negativeSobolev r) ⊤,
          let p : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ := ⟨q.val, hq⟩
          ‖p‖ ≤ m := by
  obtain ⟨N, hN, _, hgain⟩ := source_uniform_weighted_inverse_restriction r hr m (by linarith)
  refine ⟨N, hN, fun w q hq hy hnorm => ?_⟩
  obtain ⟨p, hp, hpn⟩ := hgain w q hq ⟨_,hy⟩ hnorm rfl
  have hmem : q.val ∈ periodicFourierLebesgueSubmodule (w.negativeSobolev r) ⊤ := hp ▸ p.property
  refine ⟨hmem, ?_⟩
  have he : (⟨q.val, hmem⟩ : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) = p := Subtype.ext hp.symm
  rwa [he]

end NLS.Articles.KdVPseudomeasures
