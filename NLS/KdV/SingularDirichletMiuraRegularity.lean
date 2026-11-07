import NLS.KdV.SingularDirichletMiuraEquation
import NLS.Fourier.UnitIntervalFirstOrderRegularity
import NLS.Fourier.UnitIntervalSobolevRealization

/-! # Native Dirichlet eigenvectors recover H1 quasi-derivatives

The native weak equation starts with an L2 quasi-derivative. Its retained
boundary-defect coefficient gives an absolutely continuous interval lift,
then the first-order equation upgrades the actual derivative to L2.
No equality of quasi-derivative endpoint values is required.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- The raw coefficient quasi-derivative is the literal physical expression. -/
theorem unitDirichletQuasiDerivative_representative (u : Coeff 2) (f : UnitDirichletH1) :
    unitL2SynthesisEquiv (unitDirichletQuasiDerivative u f) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => deriv (unitDirichletRepresentative f) x-
        unitL2SynthesisEquiv u x*unitDirichletRepresentative f x) := by
  unfold unitDirichletQuasiDerivative
  rw [map_sub]
  filter_upwards [unitL2Synthesis_unitDerivative f.val, unitL2Synthesis_potentialMul u f.val,
    Lp.coeFn_sub (unitL2SynthesisEquiv ((2:ℂ) • derivative f.val))
      (unitL2SynthesisEquiv (potentialMul (by norm_num) u f.val))] with x hd hp hsub
  rw [hsub]
  exact congrArg₂ (fun a b : ℂ => a-b) hd hp

/-- Every native Miura eigenvector recovers a full H1 interval quasi-derivative
satisfying the second physical row and retaining its exact endpoint jump. -/
theorem exists_intervalH1_quasiDerivative_of_native_eigen (u : Coeff 2) (lambda : ℂ)
    (f : UnitDirichletH1)
    (he : singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
      lambda • singularDirichletDomainInclusion f) :
    ∃ G : ℝ → ℂ, Continuous G ∧ AbsolutelyContinuousOnInterval G 0 1 ∧
      MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) ∧
      unitL2SynthesisEquiv (unitDirichletQuasiDerivative u f) =ᵐ[volume.restrict (Ioc 0 1)] G ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1),
        HasDerivAt G (-lambda*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x) x) ∧
      G 1-G 0 = unitDirichletMiuraDefect u lambda f := by
  have hcoeff (n : ℤ) : 2*I*(Real.pi:ℂ)*n*unitDirichletQuasiDerivative u f n =
      (∑' k : ℤ, (-u) (n-k)*unitDirichletQuasiDerivative u f k)+
        ((-lambda) • scalarInclusion f.val) n+(-unitDirichletMiuraDefect u lambda f) := by
    simp only [lp.coeFn_neg, Pi.neg_apply, neg_mul, tsum_neg, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, scalarInclusion_apply]
    linear_combination unitDirichletMiura_eigen_weak_equation u lambda f he n
  obtain ⟨G, hGc, hGa, hGr, hQG, hGd, hjump⟩ :=
    exists_intervalH1_of_weak_firstOrder (-u) (unitDirichletQuasiDerivative u f)
      ((-lambda) • scalarInclusion f.val) (-unitDirichletMiuraDefect u lambda f) hcoeff
  refine ⟨G, hGc, hGa, hGr, hQG, ?_, ?_⟩
  · rw [map_neg, map_smul] at hGd
    filter_upwards [hGd, Lp.coeFn_neg (unitL2SynthesisEquiv u),
      Lp.coeFn_smul (-lambda) (unitL2SynthesisEquiv (scalarInclusion f.val)),
      unitL2Synthesis_scalarInclusion f.val] with x hd hneg hsm hy
    simp only [hneg, hsm, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hy] at hd
    convert hd using 1
    simp only [unitDirichletRepresentative]
    ring
  · simpa only [neg_neg] using hjump

/-- The recovered quasi-derivative also gives the first actual physical row. -/
theorem native_Miura_first_row (u : Coeff 2) (f : UnitDirichletH1)
    (G : ℝ → ℂ)
    (hQG : unitL2SynthesisEquiv (unitDirichletQuasiDerivative u f)
      =ᵐ[volume.restrict (Ioc 0 1)] G) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
      (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x := by
  have hac := NLS.FunctionalAnalysis.ae_differentiableAt_complex
    (absolutelyContinuous_unitDirichletRepresentative f)
  filter_upwards [ae_restrict_of_ae hac, ae_restrict_mem measurableSet_Ioc,
    unitDirichletQuasiDerivative_representative u f, hQG] with x hd hx hq hg
  have hdiff := hd (by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ⟨hx.1.le, hx.2⟩)
  have heq : deriv (unitDirichletRepresentative f) x =
      unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x := by
    linear_combination hq.symm+hg
  rw [← heq]
  exact hdiff.hasDerivAt

end NLS.KdV
