import NLS.ZakharovShabat.SourceSpatialActionInvariance
import NLS.ZakharovShabat.SourceSobolevMomentumNormalization
import NLS.ZakharovShabat.SourceAngularThetaRectangularDifferential
import NLS.ZakharovShabat.SourceBirkhoffActionHamiltonian

/-! # The physical translation velocity in actual Birkhoff coordinates

The full rectangular Jacobian sends the period-one spatial derivative
to the signed rotations with frequencies 2πn. The selected coordinate
may be collapsed. The angle and Birkhoff normalized families are
independent, and no angle or coordinate covariance is postulated.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X U Wa : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The original H¹ physical translation gives the exact signed rectangular frequencies. -/
theorem map_coordinates_spatialDerivative
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (a : realTypeSobolevSourceLocus) (n : ℤ) :
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).1 n)
      (sobolevSourceInclusion a.val)) (sourceSobolevSpatialDerivative a.val) =
      -(sourceBirkhoffMap (by simp) (by norm_num) s (sobolevSourceInclusion a.val)).2 n *
        (2*(Real.pi : ℂ)*n) ∧
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).2 n)
      (sobolevSourceInclusion a.val)) (sourceSobolevSpatialDerivative a.val) =
      (sourceBirkhoffMap (by simp) (by norm_num) s (sobolevSourceInclusion a.val)).1 n *
        (2*(Real.pi : ℂ)*n) := by
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  by_cases hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0
  · have hz := D.real_closed_gap_zero φ.val (D.real_subset φ.property) φ.property n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hn)
    rw [hz.1,hz.2,neg_zero,zero_mul]
    exact D.map_coordinates_spatial_of_closed_gap a n hn
  · let x := (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 n
    let y := (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 n
    let J := sourceComplexAction (by simp) (by norm_num) n φ.val
    let dx := (fderiv ℂ (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).1 n)
      φ.val) (sourceSobolevSpatialDerivative a.val)
    let dy := (fderiv ℂ (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).2 n)
      φ.val) (sourceSobolevSpatialDerivative a.val)
    let c : ℂ := 2*(Real.pi : ℂ)*n
    have hrad : x^2+y^2 = 2*J := D.action_radius φ.val (D.real_subset φ.property) n
    have hJ : 2*J ≠ 0 := mul_ne_zero (by norm_num)
      (SourceAngularThetaCommonDomainData.birkhoff_action_ne_zero n φ hn)
    have hI := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (sourceSobolevSpatialDerivative a.val))
      (D.actionDifferential_eq_map_rectangular n φ.val (D.real_subset φ.property))
    rw [sourceActionDifferential_spatial_eq_zero a n] at hI
    have hi : x*dx+y*dy = 0 := hI.symm
    have ht := D.realSobolev_momentum_bracket_normalized E F A a n hn
    rw [sourceSobolevThetaMomentumBracket_eq_spatial,
      D.thetaDifferential_eq_map_rectangular E n φ hn] at ht
    change (-y/(2*J))*dx+(x/(2*J))*dy = c at ht
    have hJ0 : J ≠ 0 := (mul_ne_zero_iff.mp hJ).2
    have htheta : -y*dx+x*dy = (2*J)*c := by
      calc
        _ = (2*J)*((-y/(2*J))*dx+(x/(2*J))*dy) := by field_simp [hJ0]
        _ = (2*J)*c := by rw [ht]
    change dx = -y*c ∧ dy = x*c
    constructor
    · apply mul_left_cancel₀ hJ
      linear_combination x*hi-y*htheta-dx*hrad
    · apply mul_left_cancel₀ hJ
      linear_combination y*hi+x*htheta-dy*hrad

/-- Coordinate evaluation of the actual bounded complex Jacobian, closed gaps included. -/
theorem jacobian_spatialDerivative_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (a : realTypeSobolevSourceLocus) (n : ℤ) :
    (sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a.val)
      (sourceSobolevSpatialDerivative a.val)).1 n =
      -(sourceBirkhoffMap (by simp) (by norm_num) s (sobolevSourceInclusion a.val)).2 n *
        (2*(Real.pi : ℂ)*n) ∧
    (sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a.val)
      (sourceSobolevSpatialDerivative a.val)).2 n =
      (sourceBirkhoffMap (by simp) (by norm_num) s (sobolevSourceInclusion a.val)).1 n *
        (2*(Real.pi : ℂ)*n) := by
  have hd := D.jacobian_coordinates _ (D.real_subset a.property) (sourceSobolevSpatialDerivative a.val) n
  rw [← (D.fderiv_coordinates n _ (D.real_subset a.property)).1,
    ← (D.fderiv_coordinates n _ (D.real_subset a.property)).2] at hd
  rw [hd.1,hd.2]
  exact D.map_coordinates_spatialDerivative E F A a n

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
