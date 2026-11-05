import NLS.MKdV.MiuraActionFlowGroup
import NLS.MKdV.MiuraMeanSquareDescent

/-! # Original spectral actions and signed mean along the Gardner group

All original NLS actions and physical mKdV actions are conserved. The
previously proved mean-squared factor and continuity fix the signed mean
along the entire orbit, including an orbit of zero mean.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraActionFlow_isospectral (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    miuraActionInitialSource s (miuraActionFlow s a ha n t) (miuraActionFlow_real s a ha n t) ∈
      sourceIsospectralSet (by simp) (miuraActionInitialSource s a ha) := by
  rw [miuraActionFlow_source]
  exact miuraActionFlowFamily.data.hilbertPairedActionFlow_mem_isospectralSet _ _ _ t

theorem miuraH1ActionFlow_isospectral (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    realDiagonalH1Source (miuraH1ActionFlow a ha n t) (miuraH1ActionFlow_real a ha n t) ∈
      sourceIsospectralSet (by simp) (realDiagonalH1Source a ha) := by
  rw [miuraH1ActionFlow_source]
  exact miuraActionFlowFamily.data.hilbertPairedActionFlow_mem_isospectralSet _ _ _ t

theorem miuraNLSAction_miuraActionFlow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) (m : ℤ) :
    miuraNLSAction (miuraH1ActionFlow a ha n t) m = miuraNLSAction a m := by
  let b := miuraH1ActionFlow a ha n t
  have hb := miuraH1ActionFlow_real a ha n t
  let φ := realDiagonalH1Source a ha
  let ψ := realDiagonalH1Source b hb
  have hi : ψ ∈ sourceIsospectralSet (by simp) φ := by
    exact miuraH1ActionFlow_isospectral a ha n t
  change sourceIndexedAction (by simp) (by norm_num) m ψ.val =
    sourceIndexedAction (by simp) (by norm_num) m φ.val
  exact (sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) m ψ.val ψ.property).trans
    ((sourceRealAction_eq_of_isospectral (by simp) (by norm_num) φ ψ hi m).trans
      (sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) m φ.val φ.property).symm)

theorem miuraMKdVAction_miuraActionFlow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    miuraMKdVAction (miuraH1ActionFlow a ha n t) (miuraH1ActionFlow_real a ha n t) m =
      miuraMKdVAction a ha m := by
  let b := miuraH1ActionFlow a ha n t
  have hb := miuraH1ActionFlow_real a ha n t
  let φ := realDiagonalH1Source a ha
  let ψ := realDiagonalH1Source b hb
  have hi : ψ ∈ sourceIsospectralSet (by simp) φ := by
    exact miuraH1ActionFlow_isospectral a ha n t
  rw [← miuraL2Action_eq_physical b hb m hm,← miuraL2Action_eq_physical a ha m hm,
    miuraL2Action,miuraL2Action,scalarL2Diagonal_scalarInclusion,scalarL2Diagonal_scalarInclusion]
  apply congrArg (fun z : ℂ => (1/2 : ℂ)*z)
  change sourceDiagonalLaurentAction (by simp) (by norm_num) m 0 ψ.val =
    sourceDiagonalLaurentAction (by simp) (by norm_num) m 0 φ.val
  rw [sourceDiagonalLaurentAction_eq_real (by simp) (by norm_num) ψ
      (realDiagonalH1Source_mem_LaurentDomain b hb) m 0 (by omega),
    sourceDiagonalLaurentAction_eq_real (by simp) (by norm_num) φ
      (realDiagonalH1Source_mem_LaurentDomain a ha) m 0 (by omega)]
  exact sourceRealLaurentAction_eq_of_isospectral (by simp) (by norm_num) φ ψ hi m 0

theorem miuraActionFlow_mean_square (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    ((miuraH1ActionFlow a ha n t).val 0)^2 = (a.val 0)^2 := by
  obtain ⟨I,U,_,_,_,_,hI,V,G,_,_,_,_,hrec⟩ := exists_miuraMeanSquare_action_extension
  let b := miuraH1ActionFlow a ha n t
  have hb := miuraH1ActionFlow_real a ha n t
  have he : I (sobolevSourceInclusion (b,b)) = I (sobolevSourceInclusion (a,a)) := by
    ext m
    rw [hI b hb m,hI a ha m]
    exact miuraNLSAction_miuraActionFlow a ha n t m
  exact (hrec b hb).symm.trans ((congrArg G he).trans (hrec a ha))

/-- The signed mean, not only its square, is conserved on every entire
connected orbit. No global signed-mean recovery from NLS actions is used. -/
theorem miuraActionFlow_mean (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    (miuraH1ActionFlow a ha n t).val 0 = a.val 0 := by
  by_cases hz : a.val 0 = 0
  · have hs := miuraActionFlow_mean_square a ha n t
    rw [hz,zero_pow (by norm_num : 2 ≠ 0)] at hs
    exact (sq_eq_zero_iff.mp hs).trans hz.symm
  have hc : Continuous (fun r => (miuraH1ActionFlow a ha n r).val 0) :=
    (WeightedCoeff.evalCLM (Weight.sobolev 1) 2 0).continuous.comp (continuous_miuraH1ActionFlow a ha n)
  have he := isPreconnected_univ.eq_of_sq_eq hc.continuousOn continuousOn_const
    (fun r _ => miuraActionFlow_mean_square a ha n r) (fun _ => hz) (mem_univ (0 : ℝ))
    (by rw [miuraH1ActionFlow_zero])
  exact he (mem_univ t)

end NLS.MKdV
