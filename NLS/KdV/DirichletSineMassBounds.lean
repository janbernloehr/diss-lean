import NLS.KdV.DirichletFreeSine
import NLS.KdV.SingularDirichletRieszKernel

/-! Quantitative physical norms and complex BILINEAR mass bounds derived
from the ACTUAL native eigenfunction comparison to the literal free sine. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance dirichletSineMassH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletSineMassH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- Actual native L2 and uniform norms, and actual complex bilinear mass,
have explicit bounds from a small literal-sine error. No denominator lower
bound is supplied; the original physical normalization fixes one half. -/
theorem dirichletSineComparison_norm_and_mass_bounds (n : ℕ+) (g : UnitDirichletH1)
    {delta : ℝ} (hdsmall : delta ≤ 1/16)
    (he : ‖unitDirichletContinuousInclusion g-dirichletFreeSineCurve n‖ ≤ delta) :
    (1/2:ℝ) ≤ ‖unitDirichletL2Inclusion g‖ ∧ ‖unitDirichletL2Inclusion g‖ ≤ 2 ∧
      ‖unitDirichletContinuousInclusion g‖ ≤ 2 ∧
      ‖singularDirichletDomainInclusion g g-(1/2:ℂ)‖ ≤ 3*delta ∧
      (1/4:ℝ) ≤ ‖singularDirichletDomainInclusion g g‖ := by
  obtain ⟨h,_,_,hh⟩ := exists_native_freeDirichlet_sine n
  have hC : ‖unitDirichletContinuousInclusion h‖ ≤ 1 := by
    rw [hh]
    exact norm_dirichletFreeSineCurve_le_one n
  have hL : ‖unitDirichletL2Inclusion h‖ ≤ 1 :=
    (norm_unitDirichletL2Inclusion_le_uniform h).trans hC
  have hdiffC : ‖unitDirichletContinuousInclusion (g-h)‖ ≤ delta := by
    rw [map_sub,hh]
    exact he
  have hdiffL : ‖unitDirichletL2Inclusion (g-h)‖ ≤ delta :=
    (norm_unitDirichletL2Inclusion_le_uniform _).trans hdiffC
  have hgC : ‖unitDirichletContinuousInclusion g‖ ≤ 2 := by
    have ht := norm_add_le (unitDirichletContinuousInclusion (g-h)) (unitDirichletContinuousInclusion h)
    rw [← map_add,sub_add_cancel] at ht
    linarith
  have hgL : ‖unitDirichletL2Inclusion g‖ ≤ 2 :=
    (norm_unitDirichletL2Inclusion_le_uniform g).trans hgC
  have hmass : ‖singularDirichletDomainInclusion g g-(1/2:ℂ)‖ ≤ 3*delta := by
    rw [← singularDirichlet_mass_of_freeSine n h hh]
    apply (norm_singularDirichlet_bilinear_mass_sub_le g h).trans
    calc
      _ ≤ (2+1)*delta := by gcongr
      _ = _ := by ring
  have hlow : (1/4:ℝ) ≤ ‖singularDirichletDomainInclusion g g‖ := by
    have ht := norm_add_le ((1/2:ℂ)-singularDirichletDomainInclusion g g)
      (singularDirichletDomainInclusion g g)
    rw [sub_add_cancel,norm_sub_rev] at ht
    norm_num at ht
    linarith
  have hgLlow : (1/2:ℝ) ≤ ‖unitDirichletL2Inclusion g‖ := by
    have hb := norm_singularDirichletL2BaseInclusion_pairing_le (unitDirichletL2Inclusion g) g
    rw [singularDirichletL2BaseInclusion_domain] at hb
    nlinarith [norm_nonneg (unitDirichletL2Inclusion g)]
  exact ⟨hgLlow,hgL,hgC,hmass,hlow⟩

/-- Rescaling an ACTUAL sine-close eigenfunction gives the SOURCE unit L2
normalization, with UNIFORM physical sup-norm and complex bilinear mass
bounds. Neither reality nor a bilinear denominator estimate is assumed. -/
theorem exists_normalized_dirichletSineComparison_bounds
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (n : ℕ+)
    (g : UnitDirichletH1)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (he : ‖unitDirichletContinuousInclusion g-dirichletFreeSineCurve n‖ ≤ 1/16) :
    ∃ v : UnitDirichletH1,
      singularDirichletOperator q v = lambda • singularDirichletDomainInclusion v ∧
      ‖unitDirichletL2Inclusion v‖ = 1 ∧ ‖unitDirichletContinuousInclusion v‖ ≤ 4 ∧
      (1/16:ℝ) ≤ ‖singularDirichletDomainInclusion v v‖ := by
  obtain ⟨hLlo,hLhi,hChi,_,hMlo⟩ :=
    dirichletSineComparison_norm_and_mass_bounds n g le_rfl he
  let b := ‖unitDirichletL2Inclusion g‖
  have hb : 0 < b := lt_of_lt_of_le (by norm_num) hLlo
  let a : ℂ := ((b⁻¹:ℝ):ℂ)
  have ha : ‖a‖ = b⁻¹ := by simp only [a,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hb)]
  have halow : (1/2:ℝ) ≤ b⁻¹ := by apply (le_inv_comm₀ (by norm_num) hb).mpr; norm_num; exact hLhi
  have hahi : b⁻¹ ≤ 2 := by apply (inv_le_comm₀ hb (by norm_num)).mpr; norm_num; exact hLlo
  refine ⟨a • g,?_,?_,?_,?_⟩
  · rw [map_smul,map_smul,hg,smul_smul,smul_smul,mul_comm a lambda]
  · rw [map_smul,norm_smul,ha]
    exact inv_mul_cancel₀ hb.ne'
  · rw [map_smul,norm_smul,ha]
    nlinarith [norm_nonneg (unitDirichletContinuousInclusion g)]
  · have hm : singularDirichletDomainInclusion (a • g) (a • g) =
        (a*a)*singularDirichletDomainInclusion g g := by
      have hj : singularDirichletDomainInclusion (a • g) g =
          a*singularDirichletDomainInclusion g g := by
        exact congrArg (fun F : UnitDirichletHminus => F g)
          (singularDirichletDomainInclusion.map_smul a g)
      calc
        _ = a*singularDirichletDomainInclusion (a • g) g :=
          (singularDirichletDomainInclusion (a • g)).map_smul a g
        _ = _ := by rw [hj]; ring
    rw [hm,norm_mul,norm_mul,ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr halow) (sub_nonneg.mpr halow)]

end NLS.KdV
