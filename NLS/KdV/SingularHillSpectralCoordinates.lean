import NLS.KdV.SingularHillRieszL2
import NLS.FunctionalAnalysis.TwoDimensionalUnitCoordinates

/-! Native original H1 coordinates in the ACTUAL physical spectral basis. -/
noncomputable section
namespace NLS.KdV
open NLS.Fourier

/-- Every unit spectral-range vector has an exact native H1 decomposition
in the actual orthonormal spectral basis, with original Euclidean energy one. -/
theorem exists_singularHill_unit_spectral_coordinates
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (rho : ℝ)
    (f phi G : FourierLebesgueSpace (2:ℝ) 1 2)
    (b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection q c rho).range)
    (hb0 : (b 0).val = singularHillL2DomainInclusion f)
    (hb1 : (b 1).val = singularHillL2DomainInclusion phi)
    (hG : singularHillL2DomainInclusion G ∈ (singularHillL2RieszProjection q c rho).range)
    (hGn : ‖singularHillL2DomainInclusion G‖ = 1) :
    ∃ alpha beta : ℂ, G = alpha • f+beta • phi ∧
      ‖alpha‖^2+‖beta‖^2 = 1 ∧ ‖alpha‖ ≤ 1 ∧ ‖beta‖ ≤ 1 := by
  let x : (singularHillL2RieszProjection q c rho).range := ⟨singularHillL2DomainInclusion G,hG⟩
  obtain ⟨a,d,he,henergy,ha,hd⟩ :=
    NLS.FunctionalAnalysis.exists_unit_coordinates_fin_two b x hGn
  refine ⟨a,d,?_,henergy,ha,hd⟩
  apply singularHillL2DomainInclusion_injective
  rw [map_add,map_smul,map_smul]
  have hp := congrArg (fun y : (singularHillL2RieszProjection q c rho).range => y.val) he
  simpa only [Submodule.coe_add,Submodule.coe_smul,hb0,hb1] using hp

end NLS.KdV
