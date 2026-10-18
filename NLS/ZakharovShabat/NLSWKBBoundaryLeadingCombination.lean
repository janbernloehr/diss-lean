import NLS.ZakharovShabat.WKBBoundaryLeadingFactors

/-! # The phase-free boundary leading-integral combination

The anti-discriminant model equals the exact leading-integral combination plus a small multiple of the separated model.
-/

noncomputable section
open Set Complex
open scoped ContDiff
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- After exact phase elimination, the anti-discriminant model is a
combination of the two actual leading integrals with multipliers near one,
plus a small multiple of the separated model. -/
theorem nlsWKB_anti_boundary_leading_combination
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ)
    (θ : BoundaryCondition)
    (hp : ‖nlsWKBInitialLower a b N z‖ ≤ 1/2)
    (hq : ‖nlsWKBInitialUpper a b N z‖ ≤ 1/2) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let A := 1+p*q-extensionSign θ*(p+q)
    nlsWKBAntiDiscriminantModel a b N z+
      wkbBoundaryLeadingFactor θ p q*nlsWKBLeadingTerm a b N z 1+
      wkbBoundaryLeadingFactor θ q p*nlsWKBLeadingTerm (-b) (-a) N (-z) 1 =
      (-2*I*(p-q)/A)*nlsWKBSeparatedCharacteristicModel θ a b N z := by
  let p := nlsWKBInitialLower a b N z
  let q := nlsWKBInitialUpper a b N z
  let A := 1+p*q-extensionSign θ*(p+q)
  have hη : ‖extensionSign θ‖ = 1 := by cases θ <;> norm_num [extensionSign]
  have hp0 : 1-extensionSign θ*p ≠ 0 := (norm_inv_one_sub_mul_le_two _ _
    (by simpa only [norm_mul,hη,one_mul] using hp)).1
  have hq0 : 1-extensionSign θ*q ≠ 0 := (norm_inv_one_sub_mul_le_two _ _
    (by simpa only [norm_mul,hη,one_mul] using hq)).1
  have hd : 1-p*q ≠ 0 := (norm_inv_one_sub_mul_le_two p q (by
    rw [norm_mul]; nlinarith [norm_nonneg p,norm_nonneg q])).1
  have hd' : 1-q*p ≠ 0 := by simpa only [mul_comm] using hd
  have hA : A ≠ 0 := (norm_inv_wkb_boundary_phase_factor_le_four θ p q hp hq).1
  have h := nlsWKB_anti_boundary_phase_elimination a b ha hb hpa hpb N z hd θ
  change A*(1-p*q)*nlsWKBAntiDiscriminantModel a b N z+
    (1-extensionSign θ*q)^2*nlsWKBLeadingTerm a b N z 1+
    (1-extensionSign θ*p)^2*nlsWKBLeadingTerm (-b) (-a) N (-z) 1 =
    -2*I*(p-q)*(1-p*q)*nlsWKBSeparatedCharacteristicModel θ a b N z at h
  have he : A = (1-extensionSign θ*p)*(1-extensionSign θ*q) := by
    dsimp [A]
    cases θ <;> simp only [extensionSign] <;> ring
  have hfac : wkbBoundaryLeadingFactor θ p q = (1-extensionSign θ*q)^2/(A*(1-p*q)) := by
    unfold wkbBoundaryLeadingFactor
    rw [he]
    field_simp [hp0,hq0,hd,hd']
  have hfac' : wkbBoundaryLeadingFactor θ q p = (1-extensionSign θ*p)^2/(A*(1-p*q)) := by
    unfold wkbBoundaryLeadingFactor
    rw [he]
    field_simp [hp0,hq0,hd,hd']
  change nlsWKBAntiDiscriminantModel a b N z+
    wkbBoundaryLeadingFactor θ p q*nlsWKBLeadingTerm a b N z 1+
    wkbBoundaryLeadingFactor θ q p*nlsWKBLeadingTerm (-b) (-a) N (-z) 1 =
    (-2*I*(p-q)/A)*nlsWKBSeparatedCharacteristicModel θ a b N z
  rw [hfac,hfac']
  field_simp [hA,hd,hd']
  linear_combination h

end NLS.ZakharovShabat
