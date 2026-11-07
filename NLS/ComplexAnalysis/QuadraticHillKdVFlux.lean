import NLS.ComplexAnalysis.QuadraticHillSystemPairing

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ComplexAnalysis

/-- A local flux certificate for the pairing of a Hill trace cotangent
with q'''-6*q*q'. Its periodic integral vanishes without dividing by energy. -/
def quadraticHillKdVFlux (E Q D D2 G H R : ℂ) : ℂ :=
  G*D2-H*D+2*R*Q-2*(Q*Q+E*Q)*G+4*E*(R+E*G)

theorem quadraticHillKdVFlux_algebra (E Q D D2 D3 G H R : ℂ) :
    (H*D2+G*D3)-((2*(Q-E)*G+2*R)*D+H*D2)+
      2*((Q-E)*H*Q+R*D)-
      2*((D*Q+Q*D+E*D)*G+(Q*Q+E*Q)*H)+
      4*E*((Q-E)*H+E*H) = G*(D3-6*Q*D) := by ring

theorem integral_quadraticHill_KdV_eq_zero
    (E : ℂ) (Q D D2 D3 G H R : Curve ℂ)
    (hQ : AbsolutelyContinuousOnInterval (extend Q) 0 1)
    (hD : AbsolutelyContinuousOnInterval (extend D) 0 1)
    (hD2 : AbsolutelyContinuousOnInterval (extend D2) 0 1)
    (hG : AbsolutelyContinuousOnInterval (extend G) 0 1)
    (hH : AbsolutelyContinuousOnInterval (extend H) 0 1)
    (hR : AbsolutelyContinuousOnInterval (extend R) 0 1)
    (hqd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend Q) (extend D x) x ∧
      HasDerivAt (extend D) (extend D2 x) x ∧
      HasDerivAt (extend D2) (extend D3 x) x)
    (hsys : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend G) (extend H x) x ∧
      HasDerivAt (extend H) (2*(extend Q x-E)*extend G x+2*extend R x) x ∧
      HasDerivAt (extend R) ((extend Q x-E)*extend H x) x)
    (hper : ∀ f ∈ ({Q,D,D2,G,H,R} : Set (Curve ℂ)),
      f ⟨1,by norm_num⟩ = f ⟨0,by norm_num⟩) :
    (∫ x in (0 : ℝ)..1,extend G x*(extend D3 x-6*extend Q x*extend D x)) = 0 := by
  let F : ℝ → ℂ :=
    (extend G*extend D2-extend H*extend D+(2 : ℂ) • (extend R*extend Q)-
      (2 : ℂ) • ((extend Q*extend Q+E • extend Q)*extend G))+
      (4*E) • (extend R+E • extend G)
  have hF : AbsolutelyContinuousOnInterval F 0 1 :=
    ((((hG.smul hD2).sub (hH.smul hD)).add
      ((hR.smul hQ).const_smul (2 : ℂ))).sub
      ((((hQ.smul hQ).add (hQ.const_smul E)).smul hG).const_smul (2 : ℂ))).add
      ((hR.add (hG.const_smul E)).const_smul (4*E))
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt F (extend G x*(extend D3 x-6*extend Q x*extend D x)) x := by
    filter_upwards [hqd,hsys] with x hx hy
    have hh := ((((hy.1.mul hx.2.2).sub (hy.2.1.mul hx.2.1)).add
      ((hy.2.2.mul hx.1).const_mul (2 : ℂ))).sub
      ((((hx.1.mul hx.1).add (hx.1.const_mul E)).mul hy.1).const_mul (2 : ℂ))).add
      ((hy.2.2.add (hy.1.const_mul E)).const_mul (4*E))
    convert! hh using 1
    exact (quadraticHillKdVFlux_algebra E (extend Q x) (extend D x) (extend D2 x)
      (extend D3 x) (extend G x) (extend H x) (extend R x)).symm
  have hi : IntervalIntegrable
      (fun x => extend G x*(extend D3 x-6*extend Q x*extend D x)) volume 0 1 :=
    ((continuous_extend G).mul ((continuous_extend D3).sub
      ((continuous_const.mul (continuous_extend Q)).mul (continuous_extend D)))).intervalIntegrable 0 1
  have hh := (ae_restrict_iff' measurableSet_Icc).mp
    (by simpa only [restrict_Ioc_eq_restrict_Icc] using hd)
  have hFTC := integral_eq_sub_of_ac_of_ae_hasDerivAt hF hi
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hh)
  have hFper : F 1 = F 0 := by
    dsimp only [F,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num)]
    rw [hper Q (by simp),hper D (by simp),hper D2 (by simp),
      hper G (by simp),hper H (by simp),hper R (by simp)]
  exact hFTC.trans (sub_eq_zero.mpr hFper)

end NLS.ComplexAnalysis
