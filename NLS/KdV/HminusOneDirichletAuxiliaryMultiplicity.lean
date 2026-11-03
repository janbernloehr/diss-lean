import NLS.KdV.HminusOneDirichletOrder
import NLS.KdV.SingularDirichletMultiplicityOrder

/-! Exact auxiliary-to-native Dirichlet multiplicities for COMPLEX sources.
The zero-frequency factor contributes one, while the ramified squaring map
doubles the full native scalar algebraic multiplicity. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- The auxiliary zero frequency has precisely one spurious zero plus
TWICE the full native scalar algebraic multiplicity at the shifted energy.
No reality or scalar simplicity hypothesis is imposed. -/
theorem auxiliaryDirichletMultiplicity_zero_eq_one_add_twice
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property 0 =
      1+2*singularDirichletAlgebraicMultiplicity (periodOneOriginal q) (-c) := by
  let g : ℂ → ℂ := fun z => z^2-c
  have hg : AnalyticAt ℂ g 0 := (analyticAt_id.pow 2).sub analyticAt_const
  have hf : AnalyticAt ℂ (hillHminusDirichlet q) (g 0) :=
    analyticOnNhd_hillHminusDirichlet_energy q _ (mem_univ _)
  have ho := hf.analyticOrderAt_comp hg
  have hsub : (fun z : ℂ => g z-g 0) = (fun z : ℂ => z)^2 := by
    funext z
    dsimp [g]
    ring
  have hid : analyticOrderAt (fun z : ℂ => z) 0 = 1 := analyticOrderAt_id
  rw [hsub,analyticOrderAt_pow (f := fun z : ℂ => z) analyticAt_id,hid] at ho
  have he : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) = (fun z : ℂ => z)*(hillHminusDirichlet q ∘ g) :=
    funext fun z => auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u c z hi
  have haux := analyticOrderAt_auxiliaryPeriodOneCharacteristic (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u) 0
  rw [he,analyticOrderAt_mul (f := fun z : ℂ => z) analyticAt_id (hf.comp hg),hid,ho] at haux
  have henergy : g 0 = -c := by simp [g]
  rw [henergy,← singularDirichletAlgebraicMultiplicity_eq_analyticOrderAt q (-c)] at haux
  norm_num only [nsmul_eq_mul,mul_one] at haux
  norm_cast at haux
  omega

/-- Away from zero, the actual auxiliary algebraic multiplicity is exactly
the actual full native Dirichlet algebraic multiplicity of its squared energy. -/
theorem auxiliaryDirichletMultiplicity_eq_native_of_ne_zero
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (hz : z ≠ 0) :
    BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property z =
      singularDirichletAlgebraicMultiplicity (periodOneOriginal q) (z^2-c) := by
  rw [singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt]
  exact (analyticOrderNatAt_hillHminusDirichlet_shifted_miura q u c z hi hz).symm

/-- A single formula handles all complex frequencies, including the ramified
zero frequency and every possible associated vector of the native operator. -/
theorem auxiliaryDirichletMultiplicity_eq_native
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property z =
      if z = 0 then 1+2*singularDirichletAlgebraicMultiplicity (periodOneOriginal q) (-c)
      else singularDirichletAlgebraicMultiplicity (periodOneOriginal q) (z^2-c) := by
  classical
  split_ifs with hz
  · subst z
    exact auxiliaryDirichletMultiplicity_zero_eq_one_add_twice q u c hi
  · exact auxiliaryDirichletMultiplicity_eq_native_of_ne_zero q u c z hi hz

/-- Reflection preserves the ACTUAL auxiliary algebraic multiplicity on the
entire complex diagonal source, including every multiple central root. -/
theorem auxiliaryDirichletMultiplicity_neg (u : Coeff 2) (z : ℂ) :
    BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property (-z) =
    BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property z := by
  have hi : periodOneMiura u = periodOneMiura u+periodOneL2Inclusion (lp.single 2 0 (0:ℂ)) :=
    by simp
  rw [auxiliaryDirichletMultiplicity_eq_native (periodOneMiura u) u 0 (-z) hi,
    auxiliaryDirichletMultiplicity_eq_native (periodOneMiura u) u 0 z hi]
  simp only [neg_eq_zero,neg_sq]

end NLS.KdV
