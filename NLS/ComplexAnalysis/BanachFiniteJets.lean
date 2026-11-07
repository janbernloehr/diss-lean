import NLS.ComplexAnalysis.PoweredAnalyticJet
import NLS.ComplexAnalysis.ScalarTaylorAlgebra

/-! # Normalized finite Taylor jets in complex Banach spaces -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
open NLS.FunctionalAnalysis
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Ordinary Taylor coefficients at zero, with their exact factorial normalization. -/
def analyticFiniteJet (N : ℕ) (f : ℂ → F) : Fin N → F :=
  fun k => ((k.val.factorial:ℂ)⁻¹) • iteratedDeriv k.val f 0

omit [CompleteSpace F] in
/-- Finite domain polynomials are analytic in the full norm. -/
theorem analyticAt_chainPolynomial (N : ℕ) (v : Fin N → F) (t : ℂ) :
    AnalyticAt ℂ (pencilChainPolynomial N v) t := by
  unfold pencilChainPolynomial
  apply Finset.analyticAt_fun_sum Finset.univ
  intro j _
  exact (analyticAt_id.pow j.val).smul analyticAt_const

/-- Normalized derivatives recover the ordinary coefficients of any convergent Banach series. -/
theorem analyticFiniteJet_eq_series {f : ℂ → F} {p : FormalMultilinearSeries ℂ ℂ F}
    (hf : HasFPowerSeriesAt f p 0) (N : ℕ) (k : Fin N) :
    analyticFiniteJet N f k = p k.val (fun _ => 1) := by
  obtain ⟨r,hr⟩ := hf
  have he : (k.val.factorial:ℂ) • p k.val (fun _ => 1) = iteratedDeriv k.val f 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv, Nat.cast_smul_eq_nsmul]
    exact hr.factorial_smul (1:ℂ) k.val
  change ((k.val.factorial:ℂ)⁻¹) • iteratedDeriv k.val f 0 = _
  rw [← he, inv_smul_smul₀ (by exact_mod_cast Nat.factorial_ne_zero k.val)]

/-- A finite polynomial has precisely its given finite coefficient vector as Taylor jet. -/
theorem analyticFiniteJet_chainPolynomial (N : ℕ) (v : Fin N → F) :
    analyticFiniteJet N (pencilChainPolynomial N v) = v := by
  funext k
  change ((k.val.factorial:ℂ)⁻¹) • iteratedDeriv k.val (pencilChainPolynomial N v) 0 = v k
  rw [iteratedDeriv_chainPolynomial, inv_smul_smul₀ (by exact_mod_cast Nat.factorial_ne_zero k.val)]

/-- Every bounded linear observation commutes with the full normalized finite jet. -/
theorem analyticFiniteJet_compCLM (T : F →L[ℂ] G) {f : ℂ → F}
    (hf : AnalyticAt ℂ f 0) (N : ℕ) :
    analyticFiniteJet N (fun t => T (f t)) = fun k => T (analyticFiniteJet N f k) := by
  obtain ⟨p,hp⟩ := hf
  have hT : HasFPowerSeriesAt (fun t => T (f t)) (T.compFormalMultilinearSeries p) 0 := by
    obtain ⟨r,hr⟩ := hp
    exact ⟨r,T.comp_hasFPowerSeriesOnBall hr⟩
  funext k
  rw [analyticFiniteJet_eq_series hT, analyticFiniteJet_eq_series hp]
  rfl

/-- Addition of analytic germs is addition of their finite jets. -/
theorem analyticFiniteJet_add {f g : ℂ → F} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (N : ℕ) :
    analyticFiniteJet N (fun t => f t+g t) = analyticFiniteJet N f+analyticFiniteJet N g := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  have hs : HasFPowerSeriesAt (fun t => f t+g t) (p+q) 0 := by
    simpa only [Pi.add_def] using hp.add hq
  funext k
  rw [analyticFiniteJet_eq_series hs]
  change p k.val (fun _ => 1)+q k.val (fun _ => 1) = _
  rw [← analyticFiniteJet_eq_series hp N k, ← analyticFiniteJet_eq_series hq N k]
  rfl

/-- Subtraction of analytic germs is subtraction of their finite jets. -/
theorem analyticFiniteJet_sub {f g : ℂ → F} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (N : ℕ) :
    analyticFiniteJet N (fun t => f t-g t) = analyticFiniteJet N f-analyticFiniteJet N g := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  have hs : HasFPowerSeriesAt (fun t => f t-g t) (p-q) 0 := by
    simpa only [Pi.sub_def] using hp.sub hq
  funext k
  rw [analyticFiniteJet_eq_series hs]
  change p k.val (fun _ => 1)-q k.val (fun _ => 1) = _
  rw [← analyticFiniteJet_eq_series hp N k, ← analyticFiniteJet_eq_series hq N k]
  rfl

omit [CompleteSpace F] in
/-- A zero finite jet is exactly vanishing of all retained spectral derivatives. -/
theorem analyticFiniteJet_eq_zero_iff (N : ℕ) (f : ℂ → F) :
    analyticFiniteJet N f = 0 ↔ ∀ k : Fin N, iteratedDeriv k.val f 0 = 0 := by
  simp only [analyticFiniteJet, funext_iff, Pi.zero_apply, smul_eq_zero,
    inv_eq_zero, Nat.cast_eq_zero, Nat.factorial_ne_zero, false_or]

/-- Actual multiplication by an analytic scalar germ agrees with the existing
formal scalar Taylor convolution on every retained polynomial coefficient. -/
theorem factorial_mul_scalarTaylorJetMap {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HasFPowerSeriesAt f p 0)
    (N : ℕ) (v : Fin N → ℂ) (k : Fin N) :
    (k.val.factorial:ℂ)*scalarTaylorJetMap (scalarFormalTaylor p) N v k =
      iteratedDeriv k.val (fun t => f t*pencilChainPolynomial N v t) 0 := by
  rw [scalarTaylorJetMap_apply_eq_sum, Finset.mul_sum,
    iteratedDeriv_fun_mul hf.analyticAt.contDiffAt (analyticAt_chainPolynomial N v 0).contDiffAt]
  apply Finset.sum_congr rfl
  intro i hi
  have hiK : i ≤ k.val := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hki : k.val-i < N := (Nat.sub_le k.val i).trans_lt k.isLt
  rw [dif_pos hki, ← factorial_mul_coeff_scalarFormalTaylor hf i,
    iteratedDeriv_chainPolynomial N v ⟨k.val-i,hki⟩]
  simp only [smul_eq_mul]
  have hc : (k.val.choose i:ℂ)*(i.factorial:ℂ)*((k.val-i).factorial:ℂ) = k.val.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hiK
  calc
    _ = ((k.val.choose i:ℂ)*(i.factorial:ℂ)*((k.val-i).factorial:ℂ))*
        (PowerSeries.coeff i (scalarFormalTaylor p)*v ⟨k.val-i,hki⟩) := by rw [hc]
    _ = _ := by ring

omit [CompleteSpace F] [CompleteSpace G] in
/-- Continuous linear maps commute with the actual finite polynomial, without a Taylor argument. -/
theorem chainPolynomial_compCLM (T : F →L[ℂ] G) (N : ℕ) (v : Fin N → F) (t : ℂ) :
    T (pencilChainPolynomial N v t) = pencilChainPolynomial N (fun k => T (v k)) t := by
  unfold pencilChainPolynomial
  rw [map_sum]
  simp only [map_smul]

/-- The finite jet of a pair is the pair of its finite jets. -/
theorem analyticFiniteJet_prod {f : ℂ → F} {g : ℂ → G}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (N : ℕ) :
    analyticFiniteJet N (fun t => (f t,g t)) =
      fun k => (analyticFiniteJet N f k,analyticFiniteJet N g k) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  funext k
  rw [analyticFiniteJet_eq_series (hp.prod hq),
    analyticFiniteJet_eq_series hp, analyticFiniteJet_eq_series hq]
  rfl

omit [CompleteSpace F] in
/-- Finite jets depend only on the analytic germ, not the chosen total extension. -/
theorem analyticFiniteJet_congr {f g : ℂ → F} (he : f =ᶠ[𝓝 0] g) (N : ℕ) :
    analyticFiniteJet N f = analyticFiniteJet N g := by
  funext k
  exact congrArg (fun v => ((k.val.factorial:ℂ)⁻¹) • v) (he.iteratedDeriv_eq k.val)

/-- The normalized jet of an actual analytic scalar times a finite polynomial
is exactly the existing formal Taylor multiplication map. -/
theorem analyticFiniteJet_scalarProduct {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HasFPowerSeriesAt f p 0)
    (N : ℕ) (v : Fin N → ℂ) :
    analyticFiniteJet N (fun t => f t*pencilChainPolynomial N v t) =
      scalarTaylorJetMap (scalarFormalTaylor p) N v := by
  funext k
  change ((k.val.factorial:ℂ)⁻¹) • iteratedDeriv k.val
    (fun t => f t*pencilChainPolynomial N v t) 0 = _
  rw [← factorial_mul_scalarTaylorJetMap hf N v k]
  have hfac : (k.val.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k.val
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

omit [CompleteSpace F] [CompleteSpace G] in
/-- A jointly analytic operator and vector may be evaluated together in the full norm. -/
theorem analyticAt_operatorApply {A : ℂ → F →L[ℂ] G} {v : ℂ → F}
    (hA : AnalyticAt ℂ A 0) (hv : AnalyticAt ℂ v 0) :
    AnalyticAt ℂ (fun t => A t (v t)) 0 := by
  let e : (F →L[ℂ] G) →L[ℂ] F →L[ℂ] G := (ContinuousLinearMap.apply ℂ G).flip
  exact (e.analyticAt_bilinear (A 0,v 0)).comp (f := fun t : ℂ => (A t,v t)) (hA.prod hv)

end NLS.ComplexAnalysis
