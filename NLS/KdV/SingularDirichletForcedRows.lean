import NLS.KdV.SingularDirichletForcedResidual
import NLS.KdV.SingularDirichletPhysicalRows

/-! # Full interval H1 rows of native associated-vector equations

The forcing is the actual preceding native H1 chain coefficient. Both
directions retain the full dual weak equation, the actual scalar positions,
the L2 Miura profile and the unrestricted quasi-derivative endpoint jump.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- Every native inhomogeneous equation recovers the actual H1 interval
quasi-derivative, its forced second row and its original boundary jump. -/
theorem exists_intervalH1_quasiDerivative_of_native_forced (u : Coeff 2) (lambda : ℂ)
    (f g : UnitDirichletH1)
    (he : singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g) :
    ∃ G : ℝ → ℂ, Continuous G ∧ AbsolutelyContinuousOnInterval G 0 1 ∧
      MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) ∧
      unitL2SynthesisEquiv (unitDirichletQuasiDerivative u f) =ᵐ[volume.restrict (Ioc 0 1)] G ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
        (-lambda*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x-
          unitDirichletRepresentative g x) x) ∧
      G 1-G 0 = unitDirichletMiuraForcedDefect u lambda f g := by
  have hcoeff (n : ℤ) : 2*I*(Real.pi:ℂ)*n*unitDirichletQuasiDerivative u f n =
      (∑' k : ℤ, (-u) (n-k)*unitDirichletQuasiDerivative u f k)+
        (((-lambda) • scalarInclusion f.val)-scalarInclusion g.val) n+
          (-unitDirichletMiuraForcedDefect u lambda f g) := by
    simp only [lp.coeFn_neg, Pi.neg_apply, neg_mul, tsum_neg, lp.coeFn_sub,
      Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, scalarInclusion_apply]
    linear_combination unitDirichletMiura_forced_weak_equation u lambda f g he n
  obtain ⟨G, hGc, hGa, hGr, hQG, hGd, hjump⟩ :=
    exists_intervalH1_of_weak_firstOrder (-u) (unitDirichletQuasiDerivative u f)
      (((-lambda) • scalarInclusion f.val)-scalarInclusion g.val)
        (-unitDirichletMiuraForcedDefect u lambda f g) hcoeff
  refine ⟨G, hGc, hGa, hGr, hQG, ?_, ?_⟩
  · rw [map_neg, map_sub, map_smul] at hGd
    filter_upwards [hGd, Lp.coeFn_neg (unitL2SynthesisEquiv u),
      Lp.coeFn_sub ((-lambda) • unitL2SynthesisEquiv (scalarInclusion f.val))
        (unitL2SynthesisEquiv (scalarInclusion g.val)),
      Lp.coeFn_smul (-lambda) (unitL2SynthesisEquiv (scalarInclusion f.val)),
      unitL2Synthesis_scalarInclusion f.val, unitL2Synthesis_scalarInclusion g.val]
        with x hd hneg hsub hsm hy hz
    simp only [hneg, hsub, hsm, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hy, hz] at hd
    convert hd using 1
    simp only [unitDirichletRepresentative]
    ring
  · simpa only [neg_neg] using hjump

/-- The actual physical first-order rows with a preceding H1 coefficient
give the ENTIRE native inhomogeneous weak equation. -/
theorem singularDirichletMiura_forced_of_physical_rows (u : Coeff 2) (lambda : ℂ)
    (f g : UnitDirichletH1) (G : ℝ → ℂ) (hGc : Continuous G)
    (hGa : AbsolutelyContinuousOnInterval G 0 1)
    (hGr : MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)))
    (hYd : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
      (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x)
    (hGd : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
      (-lambda*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x-
        unitDirichletRepresentative g x) x) :
    singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g := by
  let Y := unitDirichletRepresentative f
  let Z := unitDirichletRepresentative g
  have hQG : unitL2SynthesisEquiv (unitDirichletQuasiDerivative u f)
      =ᵐ[volume.restrict (Ioc 0 1)] G := by
    filter_upwards [unitDirichletQuasiDerivative_representative u f, hYd] with x hq hy
    rw [hy.deriv] at hq
    simpa only [add_sub_cancel_left] using hq
  have hQcoef (n : ℤ) : unitFourierCoefficient G n = unitDirichletQuasiDerivative u f n := by
    rw [← unitFourierCoefficient_congr_ae hQG, unitFourierCoefficient_unitL2Synthesis]
  have hYcoef (n : ℤ) : unitFourierCoefficient Y n = f.val.val n := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact periodOneCoefficient_periodOneSobolevSynthesis f.val n
  have hZcoef (n : ℤ) : unitFourierCoefficient Z n = g.val.val n := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact periodOneCoefficient_periodOneSobolevSynthesis g.val n
  have hYi : IntervalIntegrable Y volume 0 1 :=
    (continuous_periodOneSobolevSynthesis f.val).intervalIntegrable 0 1
  have hZi : IntervalIntegrable Z volume 0 1 :=
    (continuous_periodOneSobolevSynthesis g.val).intervalIntegrable 0 1
  have hGm := memLp_two_interval hGc 0 1 (by norm_num)
  have hUGi : IntervalIntegrable (fun x => unitL2SynthesisEquiv u x*G x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((Lp.memLp (unitL2SynthesisEquiv u)).integrable_mul hGm)
  have hGi : IntervalIntegrable (deriv G) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hGr.integrable (by norm_num))
  have hder : deriv G =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => (-lambda*Y x-unitL2SynthesisEquiv u x*G x)-Z x) := by
    filter_upwards [hGd] with x hx
    exact hx.deriv
  apply singularDirichletMiura_forced_of_weak_equation u lambda (G 1-G 0) f g
  intro n
  have hcoef := unitFourierCoefficient_congr_ae hder n
  rw [unitFourierCoefficient_deriv_of_ac hGa hGi,
    unitFourierCoefficient_sub _ _ ((hYi.const_mul (-lambda)).sub hUGi) hZi,
    unitFourierCoefficient_sub _ _ (hYi.const_mul (-lambda)) hUGi,
    unitFourierCoefficient_const_mul, unitFourierCoefficient_L2_product _ _
      (Lp.memLp (unitL2SynthesisEquiv u)) hGm] at hcoef
  simp only [hQcoef, hYcoef, hZcoef, unitFourierCoefficient_unitL2Synthesis] at hcoef
  linear_combination hcoef

/-- Exact physical row criterion for every native associated-vector equation. -/
theorem singularDirichletMiura_forced_iff_physical_rows (u : Coeff 2) (lambda : ℂ)
    (f g : UnitDirichletH1) :
    singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g ↔
    ∃ G : ℝ → ℂ, Continuous G ∧ AbsolutelyContinuousOnInterval G 0 1 ∧
      MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
        (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x) ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
        (-lambda*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x-
          unitDirichletRepresentative g x) x) := by
  constructor
  · intro he
    obtain ⟨G, hc, ha, hr, hQG, hGd, _⟩ :=
      exists_intervalH1_quasiDerivative_of_native_forced u lambda f g he
    exact ⟨G, hc, ha, hr, native_Miura_first_row u f G hQG, hGd⟩
  · rintro ⟨G, hc, ha, hr, hYd, hGd⟩
    exact singularDirichletMiura_forced_of_physical_rows u lambda f g G hc ha hr hYd hGd

end NLS.KdV
