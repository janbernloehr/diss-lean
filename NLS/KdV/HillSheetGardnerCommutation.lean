import NLS.KdV.HillNormingGardnerCommutation
import NLS.KdV.HminusOneDirichletSheet
import NLS.Poisson.GardnerHamiltonianDirection

/-! Actual norming-sheet cotangents are scalar multiples of actual
norming-multiplier cotangents. Their native Gardner brackets commute
on the entire existing complex Dirichlet domain. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

theorem exists_fderiv_hillHminusDirichletSheet_eq_norming_smul (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    ∃ a : ℂ, fderiv ℂ (hillHminusDirichletSheet n) q=a • fderiv ℂ (hillHminusDirichletNorming n) q := by
  let f : ℂ → ℂ := fun z => z⁻¹-z
  have hf : DifferentiableAt ℂ f (hillHminusDirichletNorming n q) :=
    ((hasDerivAt_inv (hillHminusDirichletNorming_ne_zero n q hq)).fun_sub
      (hasDerivAt_id (hillHminusDirichletNorming n q))).differentiableAt
  have hd := hf.hasDerivAt.comp_hasFDerivAt q
    (analyticOnNhd_hillHminusDirichletNorming n q hq).differentiableAt.hasFDerivAt
  change HasFDerivAt (hillHminusDirichletSheet n) _ q at hd
  exact ⟨deriv f (hillHminusDirichletNorming n q),hd.fderiv⟩

theorem hillHminusDirichletSheets_Gardner_commute (n m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusDirichletSheet n) (hillHminusDirichletSheet m) q=0 := by
  obtain ⟨a,ha⟩ := exists_fderiv_hillHminusDirichletSheet_eq_norming_smul n q hq
  obtain ⟨b,hb⟩ := exists_fderiv_hillHminusDirichletSheet_eq_norming_smul m q hq
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusDirichletSheet n) q)
    (fderiv ℂ (hillHminusDirichletSheet m) q)=0
  rw [ha,hb]
  have hz : NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusDirichletNorming n) q)
      (fderiv ℂ (hillHminusDirichletNorming m) q)=0 := hillHminusNormings_Gardner_commute n m q hq
  simp only [map_smul,smul_apply,smul_eq_mul,hz,mul_zero]

end NLS.KdV
