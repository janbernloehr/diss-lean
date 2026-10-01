import NLS.ZakharovShabat.SourceBoundaryFloquetCommutation

/-! # Actual moving boundary cotangents at periodic terminals

At a zero of the full terminal anti-discriminant, differentiation of the
actual spectral-curve identity makes the moving terminal discriminant
cotangent zero. The anti-discriminant cotangent is twice the signed
Floquet cotangent. Actual Floquet involution therefore proves terminal
anti-discriminant involution at periodic terminals, including collapsed
gaps. Both spectral and source arguments remain moving throughout.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Either actual indexed periodic endpoint makes the full moving
boundary terminal anti-discriminant zero, also at complex sources. -/
theorem sourceBoundaryTerminalAntiDiscriminant_eq_zero_of_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hend : canonicalPeriodOneBoundaryRoots hp hp1 b φ n =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∨
      canonicalPeriodOneBoundaryRoots hp hp1 b φ n =
        canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) :
    sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ = 0 := by
  apply sq_eq_zero_iff.mp
  change sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)^2 = 0
  rw [← sourceDiscriminant_sq_sub_four_at_canonicalBoundaryRoot hp hp1 b φ n,
    canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem φ) n]
  rcases hend with hl | hr
  · simp only [hl,sub_self,mul_zero,zero_mul]
  · simp only [hr,sub_self,mul_zero,zero_mul]

/-- The full moving terminal discriminant cotangent is zero at a
periodic terminal; this is not the fixed-parameter discriminant cotangent. -/
theorem fderiv_sourceBoundaryTerminalDiscriminant_eq_zero_of_anti_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : realTypeSourceLocus p)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ.val = 0) :
    fderiv ℂ (sourceBoundaryTerminalDiscriminant hp hp1 b n) φ.val = 0 := by
  let D := sourceBoundaryTerminalDiscriminant hp hp1 b n
  let S := sourceBoundaryTerminalAntiDiscriminant hp hp1 b n
  change S φ.val = 0 at hzero
  have hD := (analyticAt_sourceBoundaryTerminalDiscriminant_of_realType hp hp1 b n φ.val φ.property).differentiableAt
  have hS := (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 b n φ.val φ.property).differentiableAt
  have heq : (fun ψ : CoeffPair p => D ψ^2-(4:ℂ)) = (fun ψ => S ψ^2) := by
    funext ψ
    exact sourceDiscriminant_sq_sub_four_at_canonicalBoundaryRoot hp hp1 b ψ n
  have hDne : D φ.val ≠ 0 := by
    intro hz
    have he := congrFun heq φ.val
    change D φ.val^2-4 = S φ.val^2 at he
    rw [hz,hzero] at he
    norm_num at he
  have hd := ((hD.hasFDerivAt.pow 2).sub_const (4:ℂ)).fderiv
  have hs := (hS.hasFDerivAt.pow 2).fderiv
  rw [heq,hs] at hd
  apply ContinuousLinearMap.ext
  intro h
  have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hd
  simp only [smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,nsmul_eq_mul] at he
  change 2*S φ.val*(fderiv ℂ S φ.val) h = 2*D φ.val*(fderiv ℂ D φ.val) h at he
  rw [hzero,mul_zero,zero_mul] at he
  change (fderiv ℂ D φ.val) h = 0
  exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (by norm_num) hDne)

/-- The actual periodic-terminal anti-discriminant cotangent is twice
the signed actual moving Floquet cotangent. -/
theorem fderiv_sourceBoundaryTerminalAntiDiscriminant_eq_floquet_of_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : realTypeSourceLocus p)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ.val = 0) :
    fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 b n) φ.val =
      (2*extensionSign b) • fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ.val := by
  have hD := (analyticAt_sourceBoundaryTerminalDiscriminant_of_realType hp hp1 b n φ.val φ.property).differentiableAt
  have hS := (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 b n φ.val φ.property).differentiableAt
  have hsum := hD.hasFDerivAt.fun_add (hS.hasFDerivAt.const_mul (extensionSign b))
  have hd := (hsum.mul_const (2:ℂ)⁻¹).fderiv
  change fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ.val = _ at hd
  rw [fderiv_sourceBoundaryTerminalDiscriminant_eq_zero_of_anti_eq_zero hp hp1 b n φ hzero,
    zero_add] at hd
  rw [hd]
  cases b <;> simp [extensionSign,smul_smul]

/-- Moving terminal anti-discriminants commute within either boundary
family when both terminals are periodic. No open-gap premise is needed. -/
theorem sourceBracket_boundaryTerminalAntiDiscriminants_eq_zero_of_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ.val = 0)
    (hm : sourceBoundaryTerminalAntiDiscriminant hp hp1 b m φ.val = 0) :
    sourceBracket h2p (sourceBoundaryTerminalAntiDiscriminant hp hp1 b n)
      (sourceBoundaryTerminalAntiDiscriminant hp hp1 b m) φ.val = 0 := by
  unfold sourceBracket
  rw [fderiv_sourceBoundaryTerminalAntiDiscriminant_eq_floquet_of_eq_zero hp hp1 b n φ hn,
    fderiv_sourceBoundaryTerminalAntiDiscriminant_eq_floquet_of_eq_zero hp hp1 b m φ hm]
  simp only [map_smul,smul_apply,smul_eq_mul]
  change (2*extensionSign b)*((2*extensionSign b)*
    sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
      (sourceBoundaryFloquetMultiplier hp hp1 b m) φ.val) = 0
  rw [sourceBracket_boundaryFloquetMultipliers_eq_zero hp hp1 h2p b φ.val φ.property n m]
  simp

end NLS.ZakharovShabat
