import NLS.KdV.HillHminusOneIntrinsicWeakForm

/-! # The intrinsic H^-1 potential term is a bounded complex-linear functional

Physical L2 comparison and density prove exact linearity in the original
rough potential, without a chosen Riccati branch in the conclusion.
The kinetic term is retained separately with the original unit scale.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

def hillHminusWeakPotential (q : PeriodOneHminusOne) (y φ : Curve ℂ) : ℂ :=
  hillHminusWeakForm q y φ-(∫ s in (0 : ℝ)..1, deriv (extend y) s*deriv (extend φ) s)

section
variable (y φ : Curve ℂ)
variable (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
variable (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
variable (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
variable (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
variable (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0)
include hy hφ hy₂ hφ₂ hend

theorem hillHminusWeakPotential_eq_physicalL2 (p : Coeff 2) :
    hillHminusWeakPotential (periodOneL2Inclusion p) y φ =
      physicalL2HillPotentialPairing y φ (unitL2SynthesisEquiv p) := by
  rw [hillHminusWeakPotential,hillHminusWeakForm_eq_physicalL2 p y φ hy hφ hy₂ hφ₂ hend,
    physicalL2HillWeakForm,add_sub_cancel_left]

theorem continuous_hillHminusWeakPotential : Continuous (fun q => hillHminusWeakPotential q y φ) :=
  (analyticOnNhd_hillHminusWeakForm y φ hy hφ hy₂ hφ₂ hend).continuous.sub continuous_const

theorem hillHminusWeakPotential_add (q r : PeriodOneHminusOne) :
    hillHminusWeakPotential (q+r) y φ = hillHminusWeakPotential q y φ+hillHminusWeakPotential r y φ := by
  let F := fun q : PeriodOneHminusOne => hillHminusWeakPotential q y φ
  have hF : Continuous F := continuous_hillHminusWeakPotential y φ hy hφ hy₂ hφ₂ hend
  have hL : Continuous (fun p : PeriodOneHminusOne × PeriodOneHminusOne => F (p.1+p.2)) :=
    hF.comp (f := fun p : PeriodOneHminusOne × PeriodOneHminusOne => p.1+p.2) (continuous_fst.add continuous_snd)
  have hR : Continuous (fun p : PeriodOneHminusOne × PeriodOneHminusOne => F p.1+F p.2) :=
    (hF.comp continuous_fst).add (hF.comp continuous_snd)
  have he : (fun p : PeriodOneHminusOne × PeriodOneHminusOne => F (p.1+p.2)) =
      (fun p : PeriodOneHminusOne × PeriodOneHminusOne => F p.1+F p.2) := by
    apply (denseRange_periodOneL2Inclusion.prodMap denseRange_periodOneL2Inclusion).equalizer hL hR
    funext p
    change F (periodOneL2Inclusion p.1+periodOneL2Inclusion p.2) = F (periodOneL2Inclusion p.1)+F (periodOneL2Inclusion p.2)
    rw [← map_add]
    dsimp only [F]
    rw [hillHminusWeakPotential_eq_physicalL2 y φ hy hφ hy₂ hφ₂ hend,
      hillHminusWeakPotential_eq_physicalL2 y φ hy hφ hy₂ hφ₂ hend,
      hillHminusWeakPotential_eq_physicalL2 y φ hy hφ hy₂ hφ₂ hend,map_add,map_add]
  exact congrFun he (q,r)

theorem hillHminusWeakPotential_smul (c : ℂ) (q : PeriodOneHminusOne) :
    hillHminusWeakPotential (c • q) y φ = c*hillHminusWeakPotential q y φ := by
  let F := fun q : PeriodOneHminusOne => hillHminusWeakPotential q y φ
  have hF : Continuous F := continuous_hillHminusWeakPotential y φ hy hφ hy₂ hφ₂ hend
  have hL : Continuous (fun q => F (c • q)) :=
    hF.comp (f := fun q : PeriodOneHminusOne => c • q) (continuous_id.const_smul c)
  have hR : Continuous (fun q => c*F q) := continuous_const.mul hF
  have he : (fun q : PeriodOneHminusOne => F (c • q)) = (fun q => c*F q) := by
    apply denseRange_periodOneL2Inclusion.equalizer hL hR
    funext p
    change F (c • periodOneL2Inclusion p) = c*F (periodOneL2Inclusion p)
    rw [← map_smul]
    dsimp only [F]
    rw [hillHminusWeakPotential_eq_physicalL2 y φ hy hφ hy₂ hφ₂ hend,
      hillHminusWeakPotential_eq_physicalL2 y φ hy hφ hy₂ hφ₂ hend,map_smul,map_smul,smul_eq_mul]
  exact congrFun he q

/-- The actual intrinsic potential pairing is continuous in H^-1 and
complex linear, for every admissible H1 pair. -/
def hillHminusWeakPotentialCLM : PeriodOneHminusOne →L[ℂ] ℂ where
  toFun q := hillHminusWeakPotential q y φ
  map_add' := hillHminusWeakPotential_add y φ hy hφ hy₂ hφ₂ hend
  map_smul' c q := by
    simpa only [RingHom.id_apply,smul_eq_mul] using hillHminusWeakPotential_smul y φ hy hφ hy₂ hφ₂ hend c q
  cont := continuous_hillHminusWeakPotential y φ hy hφ hy₂ hφ₂ hend

@[simp] theorem hillHminusWeakPotentialCLM_apply (q : PeriodOneHminusOne) :
    hillHminusWeakPotentialCLM y φ hy hφ hy₂ hφ₂ hend q = hillHminusWeakPotential q y φ := rfl

theorem hillHminusWeakForm_eq_kinetic_add_potential (q : PeriodOneHminusOne) :
    hillHminusWeakForm q y φ =
      (∫ s in (0 : ℝ)..1, deriv (extend y) s*deriv (extend φ) s)+
        hillHminusWeakPotentialCLM y φ hy hφ hy₂ hφ₂ hend q := by
  rw [hillHminusWeakPotentialCLM_apply,hillHminusWeakPotential]
  ring

end
end NLS.KdV
