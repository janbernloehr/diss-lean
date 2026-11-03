import NLS.KdV.HminusOneDirichletEigenfunctionComparison
import NLS.KdV.SingularDirichletPhysicalPairing
import NLS.Fourier.UnitIntervalContinuousLp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The LITERAL free Dirichlet sine, realized in the ENTIRE original native
H1 domain with exact physical bilinear mass one half and uniform bound one. -/
noncomputable section
open Set Metric Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat
local instance dirichletFreeSineH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletFreeSineH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- The literal free sine is uniformly bounded by one at every index. -/
theorem norm_dirichletFreeSineCurve_le_one (n : ℕ+) : ‖dirichletFreeSineCurve n‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  change ‖sin ((Real.pi:ℂ)*(n:ℕ)*t.val)‖ ≤ 1
  have he : (Real.pi:ℂ)*(n:ℕ)*t.val = ((Real.pi*(n:ℝ)*t.val:ℝ):ℂ) := by push_cast; rfl
  rw [he,← Complex.ofReal_sin,Complex.norm_real,Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

/-- The ordinary unnormalized unit-interval square integral is exactly one half. -/
theorem integral_dirichletFreeSine_squared (n : ℕ+) :
    (∫ x in (0:ℝ)..1, sin ((Real.pi:ℂ)*(n:ℕ)*x)*sin ((Real.pi:ℂ)*(n:ℕ)*x)) = (1/2:ℂ) := by
  let b := Real.pi*(n:ℝ)
  have hb : b ≠ 0 := mul_ne_zero Real.pi_ne_zero (by exact_mod_cast (ne_of_gt n.property))
  have hs : Real.sin b = 0 := by simpa only [b,mul_comm] using Real.sin_nat_mul_pi (n:ℕ)
  have hi : (∫ x in (0:ℝ)..1, (Real.sin (b*x))^2) = (1/2:ℝ) := by
    rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => (Real.sin x)^2) hb]
    simp only [mul_zero,mul_one,integral_sin_sq,Real.sin_zero,zero_mul,hs,sub_zero,
      sub_self,zero_add]
    simp only [smul_eq_mul]
    field_simp [hb]
  have he (x : ℝ) : sin ((Real.pi:ℂ)*(n:ℕ)*x)*sin ((Real.pi:ℂ)*(n:ℕ)*x) =
      (((Real.sin (b*x))^2:ℝ):ℂ) := by
    push_cast
    dsimp [b]
    push_cast
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_ofReal,hi]
  norm_num

/-- The literal sine is an ACTUAL nonzero native free eigenfunction,
with no formal Fourier or smaller-domain replacement. -/
theorem exists_native_freeDirichlet_sine (n : ℕ+) :
    ∃ h : UnitDirichletH1, h ≠ 0 ∧
      singularDirichletOperator 0 h = ((Real.pi:ℂ)*(n:ℕ))^2 • singularDirichletDomainInclusion h ∧
      unitDirichletContinuousInclusion h = dirichletFreeSineCurve n := by
  let z : ℂ := (Real.pi:ℂ)*(n:ℕ)
  have hz : z ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (by exact_mod_cast (ne_of_gt n.property))
  have hroot : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal 0) z = 0 :=
    (auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet _ z).mpr
      ((canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num) .dirichlet _ z).mpr
        ⟨((n:ℕ):ℤ),by simp [z]⟩)
  obtain ⟨h,hh0,hh,hpos⟩ := exists_native_Miura_eigen_with_sineCurve 0 z hz hroot
  refine ⟨h,hh0,?_,?_⟩
  · have hm : periodOneMiura (0 : Coeff 2) = 0 := by
      apply Subtype.ext
      funext k
      simp [periodOneMiura_apply]
    simpa only [hm,map_zero] using hh
  · rw [hpos]
    apply ContinuousMap.ext
    intro t
    change miuraDirichletSinePosition
      (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal 0)) z (1,I) t) = _
    rw [map_zero,map_zero,l2SolutionCurve_free,miuraDirichletSinePosition_free]
    rfl

/-- ANY native vector representing the literal free sine has exactly the
same physical bilinear mass, one half, independently of its construction. -/
theorem singularDirichlet_mass_of_freeSine (n : ℕ+) (h : UnitDirichletH1)
    (hh : unitDirichletContinuousInclusion h = dirichletFreeSineCurve n) :
    singularDirichletDomainInclusion h h = (1/2:ℂ) := by
  rw [singularDirichletDomainInclusion_representative_pairing]
  convert integral_dirichletFreeSine_squared n using 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hxi : x ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  have he := congrArg (fun F : C(Icc (0:ℝ) 1,ℂ) => F ⟨x,hxi⟩) hh
  change unitDirichletRepresentative h x = sin ((Real.pi:ℂ)*(n:ℕ)*x) at he
  dsimp only
  rw [he]

end NLS.KdV
