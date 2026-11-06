import NLS.MKdV.MiuraActionGradientRecurrence
import NLS.MKdV.MiuraL2Actions
import NLS.ZakharovShabat.SourceDiagonalLaurentOrdinaryDifferential
import NLS.ZakharovShabat.SourceComponentSwapPoisson

/-! # The actual Gardner action direction equals the diagonal NLS direction

The scalar action is the analytic extension of the independent physical
Hill contour. Its actual bilinear L2 gradient has a square-summable spatial
derivative. The period-one distribution derivative equals the diagonal
Hamiltonian direction of I_n-I_(-n), with the original Poisson signs.
-/
noncomputable section
open Set Metric Complex NLS.Fourier NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate SchwartzMap
namespace NLS.MKdV

theorem miuraActionGardner_coefficient (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (m : ℤ) :
    (2*I*(Real.pi : ℂ)*m)*l2ScalarGradient (miuraL2Action n) (scalarInclusion a) m =
      I*((CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (sobolevSourceInclusion (a,a)))).1 (-m)-
        (CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (sobolevSourceInclusion (a,a)))).2 (-m)) := by
  have hmem : scalarInclusion a ∈ miuraL2ActionDomain :=
    real_mem_miuraL2ActionDomain _ (by intro j; simpa only [scalarInclusion_apply] using ha j)
  rw [l2ScalarGradient_miuraL2Action n hn _ hmem m,scalarL2Diagonal_scalarInclusion]
  have h := miuraLaurentActionGradient_fourier a ha n 1 m (by omega)
  simp only [sub_self] at h
  let φ : realDiagonalSourceLocus 2 := ⟨(realDiagonalH1Source a ha).val,⟨(realDiagonalH1Source a ha).property,rfl⟩⟩
  have he : fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n 1) (sobolevSourceInclusion (a,a)) =
      fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion (a,a)) :=
    fderiv_sourceDiagonalLaurentAction_one _ _ φ n (by omega)
  rw [he] at h
  linear_combination (1/2 : ℂ)*h

theorem miuraActionGardner_memlp (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*l2ScalarGradient (miuraL2Action n) (scalarInclusion a) m) 2 := by
  let L := CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
    (sobolevSourceInclusion (a,a)))
  let q : Coeff 2 := I • Coeff.reflection (L.1-L.2)
  have he : (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*l2ScalarGradient (miuraL2Action n) (scalarInclusion a) m) = q := by
    funext m
    rw [miuraActionGardner_coefficient a ha n hn m]
    rfl
  rw [he]
  exact q.property

/-- The Gardner field is the actual distribution derivative of the
actual scalar Frechet gradient, with an L2 representative. -/
theorem miuraActionGardner_distribution (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    TemperedDistribution.derivCLM ℂ (periodOneL2Distribution (l2ScalarGradient (miuraL2Action n) (scalarInclusion a))) =
      periodOneL2Distribution (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) :=
  l2SpatialDerivative_distribution _ (miuraActionGardner_memlp a ha n hn)

theorem miuraActionGardnerDirection_apply (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (m : ℤ) :
    l2GardnerDirection (miuraL2Action n) (scalarInclusion a) m =
      I*((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion (a,a)))
        (CoeffPair.inlCLM (lp.single 2 (-m) 1))-
       (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion (a,a)))
        (CoeffPair.inrCLM (lp.single 2 (-m) 1))) := by
  rw [l2GardnerDirection,l2SpatialDerivative_apply _ (miuraActionGardner_memlp a ha n hn) m,
    miuraActionGardner_coefficient a ha n hn m,CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd]

theorem miuraActionDifference_direction (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    sourceHamiltonianDirection le_rfl
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion (a,a))-
       fderiv ℂ (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) (sobolevSourceInclusion (a,a))) =
      scalarL2Diagonal (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) := by
  let ψ := realDiagonalH1Source a ha
  have hs : sourceComponentSwap ψ.val = ψ.val := (sourceComponentSwap_eq_self_iff ψ.val).mpr rfl
  have he := fderiv_sourceComplexAction_componentSwap (by simp) (by norm_num) ψ n
  rw [hs] at he
  have hleft (m : ℤ) := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (CoeffPair.inlCLM (lp.single 2 (-m) 1))) he
  have hright (m : ℤ) := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (CoeffPair.inrCLM (lp.single 2 (-m) 1))) he
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext m
    change (sourceHamiltonianDirection le_rfl
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val-
       fderiv ℂ (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) ψ.val)).fst m =
      (scalarL2Diagonal (l2GardnerDirection (miuraL2Action n) (scalarInclusion a))).fst m
    rw [sourceHamiltonianDirection_fst_apply,scalarL2Diagonal_fst,miuraActionGardnerDirection_apply a ha n hn m]
    change -I*((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val)
      (CoeffPair.inrCLM (lp.single 2 (-m) 1))-
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) ψ.val)
      (CoeffPair.inrCLM (lp.single 2 (-m) 1))) = _
    have hr := hright m
    change (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val)
      (CoeffPair.inlCLM (lp.single 2 (-m) 1)) = _ at hr
    rw [← hr]
    dsimp only [ψ,realDiagonalH1Source]
    ring
  · ext m
    change (sourceHamiltonianDirection le_rfl
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val-
       fderiv ℂ (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) ψ.val)).snd m =
      (scalarL2Diagonal (l2GardnerDirection (miuraL2Action n) (scalarInclusion a))).snd m
    rw [sourceHamiltonianDirection_snd_apply,scalarL2Diagonal_snd,miuraActionGardnerDirection_apply a ha n hn m]
    change I*((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val)
      (CoeffPair.inlCLM (lp.single 2 (-m) 1))-
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) ψ.val)
      (CoeffPair.inlCLM (lp.single 2 (-m) 1))) = _
    have hl := hleft m
    change (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val)
      (CoeffPair.inrCLM (lp.single 2 (-m) 1)) = _ at hl
    rw [← hl]
    rfl

/-- The source's bracket-transfer identity for every actual source
cotangent. This includes the original local angular differentials. -/
theorem miuraGardner_cotangent_transfer (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (L : CoeffPair 2 →L[ℂ] ℂ) :
    (L.comp scalarL2Diagonal) (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) =
      sourceBivector le_rfl L (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion (a,a)))-
      sourceBivector le_rfl L (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) (sobolevSourceInclusion (a,a))) := by
  rw [ContinuousLinearMap.comp_apply,← miuraActionDifference_direction a ha n hn,apply_sourceHamiltonianDirection,map_sub]

end NLS.MKdV
