import NLS.KdV.HillDirichletHamiltonianRealDirection
import NLS.KdV.HillRealSourceSubmodule
import NLS.KdV.HillNormingSourceVariations

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

def hillRealDirichletSource (q : RealPeriodOneHillPotential) (n : ℕ+) : hillRealSourceSubmodule :=
  ⟨hillDirichletHamiltonianSource q n n.pos,
    hillDirichletHamiltonianSource_mem_even q n n.pos,
    isReal_hillDirichletHamiltonianSource q n n.pos⟩

/-- An ACTUAL real L2 perturbation in the Dirichlet Hamiltonian direction. -/
def hillRealDirichletPerturbation (q : RealPeriodOneHillPotential) (n : ℕ+) (t : ℝ) : RealPeriodOneHillPotential :=
  let p := (⟨q.val,q.property⟩ : hillRealSourceSubmodule) + t • hillRealDirichletSource q n
  ⟨p.val,p.property⟩

theorem hillRealDirichletPerturbation_zero (q : RealPeriodOneHillPotential) (n : ℕ+) :
    hillRealDirichletPerturbation q n 0 = q := by
  apply Subtype.ext
  change q.val + (0:ℝ) • (hillDirichletHamiltonianSource q n n.pos) = q.val
  rw [zero_smul,add_zero]

theorem continuous_hillRealDirichletPerturbation (q : RealPeriodOneHillPotential) (n : ℕ+) :
    Continuous (hillRealDirichletPerturbation q n) := by
  have hc : Continuous (fun t : ℝ => (⟨q.val,q.property⟩ : hillRealSourceSubmodule) + t • hillRealDirichletSource q n) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact (continuous_subtype_val.comp hc).subtype_mk _

theorem hillRealDirichletPerturbation_mean_zero
    (q : RealPeriodOneHillPotential) (n : ℕ+) (hmean : q.val.val 0 = 0) (t : ℝ) :
    (hillRealDirichletPerturbation q n t).val.val 0 = 0 := by
  change q.val.val 0 + t • (hillDirichletHamiltonianSource q n n.pos).val 0 = 0
  rw [hmean,hillDirichletHamiltonianSource_mean_zero,smul_zero,add_zero]

theorem hillRealDirichletPerturbation_coefficients
    (q : RealPeriodOneHillPotential) (n : ℕ+) (t : ℝ) :
    SpectralWeight.one.toCoeff (hillRealDirichletPerturbation q n t).val =
      SpectralWeight.one.toCoeff q.val + t • SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n n.pos) := by
  change (SpectralWeight.one.toCoeff.restrictScalars ℝ)
    (q.val+t • hillDirichletHamiltonianSource q n n.pos) = _
  rw [map_add,map_smul]
  rfl

theorem hasDerivAt_hillRealDirichletPerturbation_coefficients
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    HasDerivAt (fun t : ℝ => SpectralWeight.one.toCoeff (hillRealDirichletPerturbation q n t).val)
      (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n n.pos)) 0 := by
  have he : (fun t : ℝ => SpectralWeight.one.toCoeff (hillRealDirichletPerturbation q n t).val) =
      (fun t : ℝ => SpectralWeight.one.toCoeff q.val + t •
        SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n n.pos)) :=
    funext (hillRealDirichletPerturbation_coefficients q n)
  rw [he]
  simpa only [zero_add,one_smul] using!
    (hasDerivAt_const (0:ℝ) (SpectralWeight.one.toCoeff q.val)).add
      ((hasDerivAt_id (0:ℝ)).smul_const (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n n.pos)))

/-- The actual physical norming coordinate has its nonzero diagonal
Darboux derivative along an ORIGINAL real mean-preserving L2 perturbation,
at EVERY source, including closed gaps. -/
theorem hasDerivAt_hillLogNorming_realDirichletPerturbation
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    HasDerivAt (fun t : ℝ =>
      (hillDirichletLogMultiplier (hillRealDirichletPerturbation q n t).val
        (hillRealDirichletPerturbation q n t).property.1
        (hillRealDirichletPerturbation q n t).property.2 n n.pos : ℂ)) (-(1/2:ℂ)) 0 := by
  obtain ⟨F,hF,hFM,hFD⟩ := exists_hillLogNorming_dirichletSource_variations q n n.pos
  have hp := hasDerivAt_hillRealDirichletPerturbation_coefficients q n
  have hF0 : HasFDerivAt F (fderiv ℂ F (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillRealDirichletPerturbation q n 0).val) := by
    rw [hillRealDirichletPerturbation_zero]
    exact hF.differentiableAt.hasFDerivAt
  have hd := (hF0.restrictScalars ℝ).comp_hasDerivAt 0 hp
  change HasDerivAt (fun t : ℝ => F (SpectralWeight.one.toCoeff (hillRealDirichletPerturbation q n t).val))
    ((fderiv ℂ F (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n n.pos))) 0 at hd
  rw [hFD n n.pos,if_pos rfl] at hd
  have ht : Tendsto (hillRealDirichletPerturbation q n) (𝓝 0) (𝓝 q) := by
    simpa only [hillRealDirichletPerturbation_zero] using
      ((continuous_hillRealDirichletPerturbation q n).continuousAt (x := (0:ℝ))).tendsto
  have he := ht.eventually hFM
  exact hd.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)

end NLS.KdV
