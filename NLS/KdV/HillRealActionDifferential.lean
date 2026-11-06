import NLS.KdV.HillWeakHamiltonianUniqueness
import NLS.ComplexAnalysis.LocalRealAxisDerivative

/-! # Real physical action differentials and conjugate reflection

Actual real affine source curves and the local real-axis derivative theorem
prove reality on real directions. Complexifying those directions gives
conjugate-reflection compatibility on the whole period-one tangent space.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Actual real actions have real derivatives on real physical directions. -/
theorem fderiv_hillRealAction_real_direction
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) (hvr : IsRealHillPotential v) :
    ((fderiv ℂ A (SpectralWeight.one.toCoeff q)) v).im=0 := by
  let Q := SpectralWeight.one.toCoeff q
  let lift := (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm
  have hcoeff (c : Coeff 2) : SpectralWeight.one.toCoeff (lift c)=c := by
    ext k
    rw [SpectralWeight.toCoeff_apply]
    change c k/(1:ℂ)=c k
    exact div_one _
  have hprop (t : ℝ) :
      SpectralWeight.one.toCoeff (q+(t:ℂ) • lift v)∈Coeff.paritySubspace 0 ∧
        IsRealHillPotential (SpectralWeight.one.toCoeff (q+(t:ℂ) • lift v)) := by
    rw [map_add,map_smul,hcoeff]
    constructor
    · exact (Coeff.paritySubspace 0).add_mem hq ((Coeff.paritySubspace 0).smul_mem _ hv)
    · intro k
      simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,map_add,map_mul,conj_ofReal,hr k,hvr k]
  let line : ℝ → RealPeriodOneHillPotential := fun t => ⟨q+(t:ℂ) • lift v,hprop t⟩
  have hc : Continuous line := by
    apply Continuous.subtype_mk
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hline0 : line 0=(⟨q,hq,hr⟩ : RealPeriodOneHillPotential) := by
    apply Subtype.ext
    simp [line]
  have ht : Tendsto line (𝓝 0) (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) := by
    rw [← hline0]
    exact hc.tendsto 0
  let F : ℂ → ℂ := fun z => A (Q+z • v)
  have hline : HasDerivAt (fun z : ℂ => Q+z • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℂ)).smul_const v).const_add Q
  have hAc : HasFDerivAt A (fderiv ℂ A Q) (Q+(0:ℂ) • v) := by
    simpa only [zero_smul,add_zero] using hA.hasFDerivAt
  have hd : HasDerivAt F ((fderiv ℂ A Q) v) 0 := hAc.comp_hasDerivAt 0 hline
  apply HasDerivAt.im_eq_zero_of_eventually_real F _ 0 hd
  filter_upwards [ht.eventually hmatch] with t hp
  have he : SpectralWeight.one.toCoeff (line t).val=Q+(t:ℂ) • v := by
    change SpectralWeight.one.toCoeff (q+(t:ℂ) • lift v)=_
    rw [map_add,map_smul,hcoeff]
  change (A (Q+(t:ℂ) • v)).im=0
  rw [← he,hp,ofReal_im]

/-- The actual real action differential commutes with physical conjugation
on the complexified period-one tangent space. -/
theorem fderiv_hillRealAction_conjugate_direction
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) :
    (fderiv ℂ A (SpectralWeight.one.toCoeff q)) (star (Coeff.reflection v))=
      conj ((fderiv ℂ A (SpectralWeight.one.toCoeff q)) v) := by
  let J := star (Coeff.reflection v)
  let R : Coeff 2 := (1/2:ℂ) • (v+J)
  let S : Coeff 2 := (-I/2:ℂ) • (v-J)
  let D := fderiv ℂ A (SpectralWeight.one.toCoeff q)
  have hJ : J∈Coeff.paritySubspace 0 := by
    rw [Coeff.mem_paritySubspace]
    intro k hk
    have hz := (Coeff.mem_paritySubspace 0 v).mp hv (-k) (by omega)
    simp [J,hz]
  have hR : R∈Coeff.paritySubspace 0 :=
    (Coeff.paritySubspace 0).smul_mem _ ((Coeff.paritySubspace 0).add_mem hv hJ)
  have hS : S∈Coeff.paritySubspace 0 :=
    (Coeff.paritySubspace 0).smul_mem _ ((Coeff.paritySubspace 0).sub_mem hv hJ)
  have hRreal : IsRealHillPotential R := by
    intro k
    change (1/2:ℂ)*(v (-k)+conj (v (-(-k))))=conj ((1/2:ℂ)*(v k+conj (v (-k))))
    have htwo : conj (2:ℂ)=(2:ℂ) := map_ofNat _ _
    simp [htwo,add_comm]
  have hSreal : IsRealHillPotential S := by
    intro k
    change (-I/2:ℂ)*(v (-k)-conj (v (-(-k))))=conj ((-I/2:ℂ)*(v k-conj (v (-k))))
    have htwo : conj (2:ℂ)=(2:ℂ) := map_ofNat _ _
    simp [htwo]
    ring
  have hDR : (D R).im=0 := fderiv_hillRealAction_real_direction q hq hr n A hA hmatch R hR hRreal
  have hDS : (D S).im=0 := fderiv_hillRealAction_real_direction q hq hr n A hA hmatch S hS hSreal
  have hDRc : conj (D R)=D R := by apply Complex.ext <;> simp [hDR]
  have hDSc : conj (D S)=D S := by apply Complex.ext <;> simp [hDS]
  have hpos : v=R+I • S := by
    dsimp only [R,S]
    rw [smul_smul]
    have hc : (I:ℂ)*(-I/2)=1/2 := by rw [mul_div,mul_neg,I_mul_I,neg_neg]
    rw [hc,← smul_add]
    have he : v+J+(v-J)=(2:ℂ) • v := by module
    rw [he,smul_smul]
    norm_num
  have hneg : J=R-I • S := by
    dsimp only [R,S]
    rw [smul_smul]
    have hc : (I:ℂ)*(-I/2)=1/2 := by rw [mul_div,mul_neg,I_mul_I,neg_neg]
    rw [hc,← smul_sub]
    have he : v+J-(v-J)=(2:ℂ) • J := by module
    rw [he,smul_smul]
    norm_num
  have hDJ : D J=D R-I*D S := by
    have hh := congrArg D hneg
    simpa only [map_sub,map_smul,smul_eq_mul] using hh
  have hDv : D v=D R+I*D S := by
    have hh := congrArg D hpos
    simpa only [map_add,map_smul,smul_eq_mul] using hh
  change D J=conj (D v)
  rw [hDJ,hDv,map_add,map_mul,conj_I,hDRc,hDSc]
  ring

end NLS.KdV
