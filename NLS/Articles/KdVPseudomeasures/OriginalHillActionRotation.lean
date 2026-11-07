import NLS.Articles.KdVPseudomeasures.OriginalHillActionGlobalFlow
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSignedGardner
import NLS.ComplexAnalysis.ScalarExponentialUniqueness

/-! The COMPLETE actual action flow rotates exactly its own signed native
coordinate pair with angular speed one, fixing every other coordinate.
The sign and speed follow from the literal actual Gardner matrix. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.Poisson
namespace NLS.Articles.KdVPseudomeasures

/-- Exact signed angular rate, including the literal zero mode. -/
def hillActionRotationRate (n : ℕ+) (k : ℤ) : ℂ :=
  if k=(n:ℤ) then I else if k= -(n:ℤ) then -I else 0

theorem hillHminusActionHamiltonianVector_eq_coordinate_product (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusActionAngleNativeDomain) :
    hillHminusActionHamiltonianVector n q=
      hillHminusNativeCoordinate (n:ℤ) q • gardnerHamiltonianVector (hillHminusNativeCoordinate (-(n:ℤ))) q+
      hillHminusNativeCoordinate (-(n:ℤ)) q • gardnerHamiltonianVector (hillHminusNativeCoordinate (n:ℤ)) q := by
  have he : hillHminusCanonicalAction n =ᶠ[𝓝 q]
      (fun p => hillHminusNativeCoordinate (n:ℤ) p*hillHminusNativeCoordinate (-(n:ℤ)) p) := by
    filter_upwards [isOpen_hillHminusActionAngleNativeDomain.mem_nhds hq] with p hp
    exact (hillHminusNativeComplexMap_action_identity p hp n).symm
  change gardnerHamiltonianDirection (fderiv ℂ (hillHminusCanonicalAction n) q)=_
  rw [he.fderiv_eq,fderiv_fun_mul
    (analyticOnNhd_hillHminusNativeCoordinate (n:ℤ) q hq).differentiableAt
    (analyticOnNhd_hillHminusNativeCoordinate (-(n:ℤ)) q hq).differentiableAt,
    map_add,map_smul,map_smul]
  rfl

theorem hillRealNativeCoordinate_action_velocity (n : ℕ+) (k : ℤ) (q : HillRealMeanZeroSource) :
    (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion q))
      (hillHminusActionHamiltonianVector n (hillRealMeanZeroInclusion q))=
        hillActionRotationRate n k*hillHminusNativeCoordinate k (hillRealMeanZeroInclusion q) := by
  rw [hillHminusActionHamiltonianVector_eq_coordinate_product n (hillRealMeanZeroInclusion q)
    (real_mem_hillHminusActionAngleNativeDomain _ q.property),map_add,map_smul,map_smul,
    fderiv_apply_gardnerHamiltonianVector,fderiv_apply_gardnerHamiltonianVector]
  change hillHminusNativeCoordinate (n:ℤ) _*hillHminusNativeGardnerBracket k (-(n:ℤ)) _+
    hillHminusNativeCoordinate (-(n:ℤ)) _*hillHminusNativeGardnerBracket k (n:ℤ) _= _
  rw [hillRealNativeGardner_signed_canonical,hillRealNativeGardner_signed_canonical]
  have hn : (0:ℤ) < n := by exact_mod_cast n.pos
  by_cases hkp : k=(n:ℤ)
  · subst k
    simp only [hillActionRotationRate,if_neg (by omega : (n:ℤ) ≠ 0),
      if_pos hn,if_neg (by omega : (n:ℤ) ≠ -(n:ℤ)),mul_zero,add_zero]
    ring
  · by_cases hkm : k= -(n:ℤ)
    · subst k
      simp only [hillActionRotationRate,
        if_neg (by omega : -(n:ℤ) ≠ 0),neg_neg,if_neg (by omega : ¬(0:ℤ)< -(n:ℤ)),
        if_neg (by omega : -(n:ℤ) ≠ (n:ℤ)),mul_zero,zero_add]
      ring
    · by_cases hk0 : k=0
      · subst k
        simp only [hillActionRotationRate,if_neg hkp,if_neg hkm,ite_true,mul_zero,add_zero,zero_mul]
      · simp only [hillActionRotationRate,if_neg hkp,if_neg hkm,if_neg hk0,
          if_neg (by omega : -(n:ℤ) ≠ -k),if_neg (by omega : (n:ℤ) ≠ -k),mul_zero,add_zero,zero_mul]

/-- The actual raw coordinate solves the exact scalar rotation equation globally. -/
theorem hasDerivAt_originalHillNativeActionFlow_coordinate
    (n : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun τ => hillHminusNativeCoordinate k
      (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q τ)))
      (hillActionRotationRate n k*hillHminusNativeCoordinate k
        (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q t))) t := by
  have hc := ((analyticOnNhd_hillHminusNativeCoordinate k _
    (real_mem_hillHminusActionAngleNativeDomain _ (originalHillNativeActionFlow n q t).property)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (hasDerivAt_originalHillNativeActionFlow_inclusion n q t)
  change HasDerivAt (fun τ => hillHminusNativeCoordinate k
    (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q τ)))
    ((fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q t)))
      (hillHminusActionHamiltonianVector n (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q t)))) t at hc
  convert hc using 1
  exact (hillRealNativeCoordinate_action_velocity n k _).symm

/-- The literal original signed raw coordinates have exactly unit rotation rate. -/
theorem originalHillNativeActionFlow_coordinate (n : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) (k : ℤ) :
    hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q t))=
      exp (hillActionRotationRate n k*t)*hillHminusNativeCoordinate k (hillRealMeanZeroInclusion q) := by
  simpa only [originalHillNativeActionFlow_zero] using
    NLS.ComplexAnalysis.eq_exp_mul_of_hasDerivAt (hillActionRotationRate n k)
      (fun τ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q τ)))
      (fun τ => hasDerivAt_originalHillNativeActionFlow_coordinate n q τ k) t

end NLS.Articles.KdVPseudomeasures
