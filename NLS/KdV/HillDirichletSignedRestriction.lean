import NLS.KdV.HillDirichletSignedForms
import NLS.Fourier.CircleUnitContinuous
import NLS.KdV.SingularDirichletPhysicalPairing
import NLS.KdV.SingularDirichletRieszL2

/-! The exact original interval restriction of H1 vectors and their
native signed residuals, including the ACTUAL projected identity. -/
noncomputable section
open Set Metric MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat NLS.LinearVolterra

/-- The identical closed-unit-interval representative as ordinary
UNNORMALIZED physical L2, on the ENTIRE original native periodic H1 space. -/
def hillH1IntervalL2 : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] IntervalL2 :=
  (unitIntervalContinuousToLp 2).comp
    (circleUnitContinuousRestriction.comp singularHillContinuousDomainInclusion)

/-- This bounded restriction retains the SAME physical position almost everywhere. -/
theorem hillH1IntervalL2_representative (F : FourierLebesgueSpace (2:ℝ) 1 2) :
    hillH1IntervalL2 F =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      fun x : ℝ => singularHillContinuousDomainInclusion F (x : AddCircle (2:ℝ)) := by
  filter_upwards [unitIntervalContinuousToLp_representative 2
    (circleUnitContinuousRestriction (singularHillContinuousDomainInclusion F)),
    ae_restrict_mem measurableSet_Ioc] with x hx hxi
  exact hx.trans (extend_coe _ ⟨x,⟨hxi.1.le,hxi.2⟩⟩)

/-- Its full native Dirichlet-dual action is the literal unit-interval integral. -/
theorem hillH1IntervalL2_pairing (F : FourierLebesgueSpace (2:ℝ) 1 2) (h : UnitDirichletH1) :
    singularDirichletL2BaseInclusion (hillH1IntervalL2 F) h =
      ∫ x in (0:ℝ)..1, singularHillContinuousDomainInclusion F (x : AddCircle (2:ℝ))*
        unitDirichletRepresentative h x := by
  rw [singularDirichletL2BaseInclusion_representative_pairing]
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [hillH1IntervalL2_representative F] with x hx
  rw [hx]

/-- The signed test realizes the SAME ordinary interval mass for every H1 vector. -/
theorem hillH1_mass_signed_test_restriction (r : ℤ) (F : FourierLebesgueSpace (2:ℝ) 1 2)
    (h : UnitDirichletH1)
    (hF : ∀ x : ℝ, singularHillContinuousDomainInclusion F ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion F (x : AddCircle (2:ℝ))) :
    singularHillPairing (singularHillDomainInclusion F) (unitDirichletSignedH1 r h) =
      singularDirichletL2BaseInclusion (hillH1IntervalL2 F) h := by
  rw [hillH1_mass_signed_test_integral r F h hF,hillH1IntervalL2_pairing]

/-- A faithful native interval-domain representative has exactly this
physical L2 restriction, including the original normalization. -/
theorem hillH1IntervalL2_eq_dirichlet (G : FourierLebesgueSpace (2:ℝ) 1 2) (g : UnitDirichletH1)
    (hsame : ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
      singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) :
    hillH1IntervalL2 G = unitDirichletL2Inclusion g := by
  have he : circleUnitContinuousRestriction (singularHillContinuousDomainInclusion G) =
      unitDirichletContinuousInclusion g := by
    apply ContinuousMap.ext
    intro x
    exact (hsame x.val x.property).symm
  change unitIntervalContinuousToLp 2 (circleUnitContinuousRestriction
    (singularHillContinuousDomainInclusion G)) = _
  rw [he,unitIntervalContinuousToLp_two_dirichlet]

/-- The native Dirichlet domain inclusion equals testing the periodic
domain inclusion against SAME-PARITY extensions of ALL Dirichlet tests. -/
theorem singularDirichletDomainInclusion_signed_test (r : ℤ)
    (G : FourierLebesgueSpace (2:ℝ) 1 2) (g h : UnitDirichletH1)
    (hG : ∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hsame : ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
      singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) :
    singularDirichletDomainInclusion g h =
      singularHillPairing (singularHillDomainInclusion G) (unitDirichletSignedH1 r h) := by
  rw [hillH1_mass_signed_test_restriction r G h hG,hillH1IntervalL2_eq_dirichlet G g hsame,
    singularDirichletL2BaseInclusion_domain]

/-- An actual periodic native residual restricts to the FULL original
Dirichlet dual, with both physical forcing vectors restricted faithfully.
No weak operator compatibility premise is supplied. -/
theorem singularDirichlet_residual_of_signed_periodic
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (r : ℤ) (z a b : ℂ)
    (G f phi : FourierLebesgueSpace (2:ℝ) 1 2) (g : UnitDirichletH1)
    (hG : ∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hf : ∀ x : ℝ, singularHillContinuousDomainInclusion f ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ)))
    (hphi : ∀ x : ℝ, singularHillContinuousDomainInclusion phi ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion phi (x : AddCircle (2:ℝ)))
    (hsame : ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
      singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hres : singularHillOperator q G-z • singularHillDomainInclusion G =
      a • singularHillDomainInclusion f-b • singularHillDomainInclusion phi) :
    singularDirichletOperator q g-z • singularDirichletDomainInclusion g =
      a • singularDirichletL2BaseInclusion (hillH1IntervalL2 f)-
        b • singularDirichletL2BaseInclusion (hillH1IntervalL2 phi) := by
  apply ContinuousLinearMap.ext
  intro h
  have ht := congrArg (fun v : FourierLebesgueSpace (2:ℝ) (-1) 2 =>
    singularHillPairing v (unitDirichletSignedH1 r h)) hres
  simp only [singularHillPairing,map_sub,sub_apply,map_smul,smul_apply,smul_eq_mul] at ht
  change singularDirichletOperator q g h-z*singularDirichletDomainInclusion g h =
    a*singularDirichletL2BaseInclusion (hillH1IntervalL2 f) h-
      b*singularDirichletL2BaseInclusion (hillH1IntervalL2 phi) h
  rw [singularDirichletOperator_signed_test q r G g h hG hsame,
    singularDirichletDomainInclusion_signed_test r G g h hG hsame]
  rw [← hillH1_mass_signed_test_restriction r f h hf,
    ← hillH1_mass_signed_test_restriction r phi h hphi]
  exact ht

/-- The exact ACTUAL projected interval residual in physical L2. This is
the full operator/restriction step of source(31), with arbitrary complex
forcing coefficients and the original valid contour. -/
theorem singularDirichlet_projected_residual_of_signed_periodic
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (r : ℤ) (z a b c mu nu : ℂ) (rho : ℝ)
    (hrho : 0 ≤ rho) (hc : sphere c rho ⊆ singularDirichletResolventSet q)
    (G f phi : FourierLebesgueSpace (2:ℝ) 1 2) (g v : UnitDirichletH1)
    (hG : ∀ x : ℝ, singularHillContinuousDomainInclusion G ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hf : ∀ x : ℝ, singularHillContinuousDomainInclusion f ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ)))
    (hphi : ∀ x : ℝ, singularHillContinuousDomainInclusion phi ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*singularHillContinuousDomainInclusion phi (x : AddCircle (2:ℝ)))
    (hsame : ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
      singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ)))
    (hres : singularHillOperator q G-z • singularHillDomainInclusion G =
      a • singularHillDomainInclusion f-b • singularHillDomainInclusion phi)
    (hv : singularDirichletOperator q v = mu • singularDirichletDomainInclusion v)
    (hproj : singularDirichletL2RieszProjection q c rho (unitDirichletL2Inclusion g) =
      nu • unitDirichletL2Inclusion v) :
    (nu*(mu-z)) • unitDirichletL2Inclusion v =
      a • singularDirichletL2RieszProjection q c rho (hillH1IntervalL2 f)-
        b • singularDirichletL2RieszProjection q c rho (hillH1IntervalL2 phi) := by
  have hprojH : singularDirichletDomainRieszProjection q c rho g = nu • v := by
    apply unitDirichletL2Inclusion_injective
    rw [← singularDirichletL2RieszProjection_domain,map_smul]
    exact hproj
  have he := singularDirichletRiesz_projected_residual q c rho hrho hc z mu nu g v hv hprojH
  rw [singularDirichlet_residual_of_signed_periodic q r z a b G f phi g hG hf hphi hsame hres,
    map_sub,map_smul,map_smul] at he
  apply singularDirichletL2BaseInclusion_injective
  rw [map_sub,map_smul,map_smul,map_smul,singularDirichletL2BaseInclusion_domain,
    singularDirichletL2RieszProjection_base q c rho hrho hc,
    singularDirichletL2RieszProjection_base q c rho hrho hc]
  exact he.symm

end NLS.KdV
