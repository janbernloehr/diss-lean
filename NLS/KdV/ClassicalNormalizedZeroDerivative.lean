import NLS.KdV.ClassicalNormalizedZeroFactorization

/-! # Operator regularity and diagonal derivatives of the zero equation

The partial derivative is operator-norm analytic and equal to Id at the
free source. On an analytic root graph it therefore has a constructed
inverse on one smaller source neighborhood. Coordinate locality identifies
all its off-diagonal entries without a coordinatewise limit assumption.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillZeroPartial (N : ℕ)
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2 :=
  (fderiv ℂ (classicalHillZeroMap N Q n) t).comp
    (ContinuousLinearMap.inl ℂ (NLS.Coeff 2) (NLS.LinearVolterra.Curve ℂ))

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem zeroPartial_analytic
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillZeroPartial N Q n) (classicalHillCandidateDomain V) := by
  let L := (ContinuousLinearMap.compL ℂ (NLS.Coeff 2)
    (NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (NLS.Coeff 2)).flip
      (ContinuousLinearMap.inl ℂ (NLS.Coeff 2) (NLS.LinearVolterra.Curve ℂ))
  intro t ht
  simpa only [classicalHillZeroPartial,L,Function.comp_def] using!
    (L.analyticAt _).comp (f := fderiv ℂ (classicalHillZeroMap N Q n))
      ((D.zeroMap_spec Q hQa hQ n).2.fderiv t ht)

theorem zeroPartial_free
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) :
    classicalHillZeroPartial N Q n (0,0) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
  have h00 : ((0 : NLS.Coeff 2),(0 : NLS.LinearVolterra.Curve ℂ)) ∈ classicalHillCandidateDomain V :=
    ⟨mem_ball_self (by positivity),D.zero_mem⟩
  have hd := ((D.zeroMap_spec Q hQa hQ n).2 _ h00).differentiableAt.hasFDerivAt.comp
    (f := fun x : NLS.Coeff 2 => (x,(0 : NLS.LinearVolterra.Curve ℂ))) 0
    (hasFDerivAt_prodMk_left (0 : NLS.Coeff 2) (0 : NLS.LinearVolterra.Curve ℂ))
  have he : fderiv ℂ (fun x : NLS.Coeff 2 => classicalHillZeroMap N Q n (x,0)) 0 =
      classicalHillZeroPartial N Q n (0,0) := by simpa only [Function.comp_def] using! hd.fderiv
  exact he.symm.trans (D.zeroMap_free_derivative Q hQa hQ hQ0 n)

/-- The root graph has a genuine inverse partial derivative on one
smaller neighborhood, before every coordinate index. -/
theorem exists_regular_zero_graph
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+)
    (s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2) (U : Set (NLS.LinearVolterra.Curve ℂ))
    (hU : IsOpen U) (h0U : 0 ∈ U) (hs0 : s 0 = 0) (hsa : AnalyticOnNhd ℂ s U)
    (ht : ∀ q ∈ U, (s q,q) ∈ classicalHillCandidateDomain V) :
    ∃ W : Set (NLS.LinearVolterra.Curve ℂ), W ⊆ U ∧ IsOpen W ∧ 0 ∈ W ∧
      ∀ q ∈ W, Function.Bijective (classicalHillZeroPartial N Q n (s q,q)) := by
  let T := fun q => classicalHillZeroPartial N Q n (s q,q)
  have hTa : AnalyticOnNhd ℂ T U := by
    intro q hq
    exact (D.zeroPartial_analytic Q hQa hQ n (s q,q) (ht q hq)).comp
      (f := fun a : NLS.LinearVolterra.Curve ℂ => (s a,a)) ((hsa q hq).prod analyticAt_id)
  have hT0 : T 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
    dsimp only [T]
    rw [hs0,D.zeroPartial_free Q hQa hQ hQ0 n]
  obtain ⟨W,J,hWU,hW,h0W,_,_,hJ⟩ := exists_analytic_operator_inverse_near_zero T U hU h0U hTa hT0
  refine ⟨W,hWU,hW,h0W,?_⟩
  intro q hq
  exact ContinuousLinearMap.isUnit_iff_bijective.mp ⟨⟨T q,J q,(hJ q hq).1,(hJ q hq).2.1⟩,rfl⟩

theorem zeroMap_coordinate_congr
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n : ℕ+)
    (t u : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V) (hu : u ∈ classicalHillCandidateDomain V)
    (j : ℤ) (hq : t.2 = u.2) (hx : t.1 j = u.1 j) :
    classicalHillZeroMap N Q n t j = classicalHillZeroMap N Q n u j := by
  rw [(D.zeroMap_spec Q hQa hQ n).1 t ht,(D.zeroMap_spec Q hQa hQ n).1 u hu]
  by_cases hj : 0 < j
  · let k := positiveIntegerIndex j hj
    have hkj : (k : ℤ) = j := positiveIntegerIndex_int j hj
    have he : classicalHillCandidateEnergy N k t = classicalHillCandidateEnergy N k u := by
      simp only [classicalHillCandidateEnergy,classicalHillCandidateFrequency,hq,hkj,hx]
    have hr : classicalHillCandidateRow N n k t = classicalHillCandidateRow N n k u := by
      ext m
      rw [(D.candidateRow_spec n k).1 t ht,(D.candidateRow_spec n k).1 u hu]
      simp only [classicalHillCandidateRowCoordinates,hq,he]
    have hg : classicalHillZeroBracket N Q n k t = classicalHillZeroBracket N Q n k u := by
      simp only [classicalHillZeroBracket,hq,hr]
    rw [classicalHillZeroCoordinates,dif_pos hj,classicalHillZeroCoordinates,dif_pos hj]
    change (if k = n then _ else _) = (if k = n then _ else _)
    split_ifs
    · exact hx
    · change ((classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/
          (2*classicalHillCriticalFrequency N k t.2*(k : ℂ)))*classicalHillZeroCoefficients Q n t.2 j+
          t.1 j*(1+t.1 j/(2*classicalHillCriticalFrequency N k t.2))*classicalHillZeroBracket N Q n k t =
        ((classicalHillCandidateEnergy N k u-classicalHillUniformCriticalPoint N n u.2)/
          (2*classicalHillCriticalFrequency N k u.2*(k : ℂ)))*classicalHillZeroCoefficients Q n u.2 j+
          u.1 j*(1+u.1 j/(2*classicalHillCriticalFrequency N k u.2))*classicalHillZeroBracket N Q n k u
      simp only [hq,hx,he,hg]
  · simp only [classicalHillZeroCoordinates,dif_neg hj,hx]

theorem zeroMap_coordinate_curve_hasDerivAt
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (k j : ℤ) :
    HasDerivAt (fun c : ℂ => classicalHillZeroMap N Q n
      (t.1+c • lp.single 2 k 1,t.2) j) (classicalHillZeroPartial N Q n t (lp.single 2 k 1) j) 0 := by
  have hi : HasDerivAt (fun c : ℂ => (t.1+c • lp.single 2 k (1 : ℂ),t.2))
      ((lp.single 2 k (1 : ℂ) : NLS.Coeff 2),0) 0 := by
    simpa using ((hasDerivAt_const (0 : ℂ) t.1).add
      ((hasDerivAt_id (0 : ℂ)).smul_const (lp.single 2 k (1 : ℂ) : NLS.Coeff 2))).prodMk
        (hasDerivAt_const (0 : ℂ) t.2)
  have hF := ((D.zeroMap_spec Q hQa hQ n).2 t ht).differentiableAt.hasFDerivAt
  have hF' : HasFDerivAt (classicalHillZeroMap N Q n) (fderiv ℂ (classicalHillZeroMap N Q n) t)
      (t.1+(0 : ℂ) • lp.single 2 k (1 : ℂ),t.2) := by
    simpa only [zero_smul,add_zero,Prod.eta] using! hF
  have hh := hF'.comp_hasDerivAt 0 hi
  have hv := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).hasFDerivAt.comp_hasDerivAt 0 hh
  simpa only [classicalHillZeroPartial,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
    Function.comp_def,zero_smul,add_zero] using! hv

theorem zeroPartial_single_offDiagonal
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (k j : ℤ) (hjk : j ≠ k) :
    classicalHillZeroPartial N Q n t (lp.single 2 k 1) j = 0 := by
  have hi : ContinuousAt (fun c : ℂ => (t.1+c • lp.single 2 k (1 : ℂ),t.2)) 0 :=
    (continuousAt_const.add (continuousAt_id.smul continuousAt_const)).prodMk continuousAt_const
  have hU : IsOpen (classicalHillCandidateDomain V) := isOpen_ball.prod D.isOpen
  have he : ∀ᶠ c : ℂ in 𝓝 0, (t.1+c • lp.single 2 k (1 : ℂ),t.2) ∈ classicalHillCandidateDomain V := by
    have hbase : (t.1+(0 : ℂ) • lp.single 2 k (1 : ℂ),t.2) ∈ classicalHillCandidateDomain V := by
      simpa only [zero_smul,add_zero,Prod.eta] using ht
    exact hi.eventually (hU.mem_nhds hbase)
  have hc : (fun c : ℂ => classicalHillZeroMap N Q n (t.1+c • lp.single 2 k (1 : ℂ),t.2) j) =ᶠ[𝓝 0]
      (fun _ => classicalHillZeroMap N Q n t j) := by
    filter_upwards [he] with c hc
    apply D.zeroMap_coordinate_congr Q hQa hQ n _ t hc ht j rfl
    simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_apply,if_neg hjk,mul_zero,add_zero]
  have hd := D.zeroMap_coordinate_curve_hasDerivAt Q hQa hQ n t ht k j
  exact hd.unique ((hasDerivAt_const (0 : ℂ) (classicalHillZeroMap N Q n t j)).congr_of_eventuallyEq hc)

/-- Actual invertibility of the partial map forces every scalar diagonal
root derivative to be nonzero, simultaneously over the full index set. -/
theorem zeroPartial_single_diagonal_ne_zero
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (hbij : Function.Bijective (classicalHillZeroPartial N Q n t)) (k : ℤ) :
    classicalHillZeroPartial N Q n t (lp.single 2 k 1) k ≠ 0 := by
  intro hz
  have he : classicalHillZeroPartial N Q n t (lp.single 2 k 1) = 0 := by
    ext j
    by_cases hjk : j = k
    · subst j; simpa only [lp.coeFn_zero,Pi.zero_apply] using hz
    · simpa only [lp.coeFn_zero,Pi.zero_apply] using D.zeroPartial_single_offDiagonal Q hQa hQ n t ht k j hjk
  have hunit : (lp.single 2 k (1 : ℂ) : NLS.Coeff 2) = 0 := hbij.1 (he.trans (map_zero _).symm)
  have hv := congrArg (fun x : NLS.Coeff 2 => x k) hunit
  simp only [lp.single_apply,Pi.single_apply,ite_true,lp.coeFn_zero,Pi.zero_apply] at hv
  exact one_ne_zero hv

end ClassicalAllContourPeriodData
end NLS.KdV
