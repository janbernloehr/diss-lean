import NLS.KdV.PseudomeasureWideInhomogeneous
import NLS.KdV.PseudomeasureWideSecondOrder
import NLS.Fourier.PeriodicEndpointLowerInclusion

/-! The literal s+2,infinity regularity of all reconstructed physical
solutions. Both finite modes and the complementary response keep the
same original distributions. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

def endpointSecondOrderH1Inclusion (r : ℝ) (hr1 : r<1/2) :
    FourierLebesgueSpace (2:ℝ) (2-r) ⊤ →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  endpointLowerInclusion (p:=2) (2-r) 1 (by norm_num) (by norm_num; linarith)

theorem endpointSecondOrderH1Inclusion_val (r : ℝ) (hr1 : r<1/2)
    (w : FourierLebesgueSpace (2:ℝ) (2-r) ⊤) :
    (endpointSecondOrderH1Inclusion r hr1 w).val=w.val :=
  endpointLowerInclusion_val (2-r) 1 (by norm_num) (by norm_num; linarith) w

theorem endpointHillH1Modes_sobolev (s : ℝ) (n : ℕ) (u : ℂ × ℂ) :
    ∃ v : FourierLebesgueSpace (2:ℝ) s ⊤, v.val=(endpointHillH1Modes n u).val := by
  let b := WeightedCoeff.exponentInclusion (Weight.sobolev s) (by simp : (1:ℝ≥0∞)≤⊤)
    (hillModes (Weight.sobolev s) n u)
  refine ⟨(sobolevCoefficients (L:=2) s ⊤).symm b,?_⟩
  apply Distribution.ext_coefficients
  intro k
  have hb := congrArg (fun x : WeightedCoeff (Weight.sobolev s) ⊤ => x.val k)
    ((sobolevCoefficients (L:=2) s ⊤).apply_symm_apply b)
  rw [sobolevCoefficients_apply] at hb
  apply hb.trans
  simp only [b,WeightedCoeff.exponentInclusion_apply,hillModes_apply,endpointHillH1Modes_coefficient]

theorem endpointReconstruction_response_secondOrder_wide (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (u : ℂ × ℂ) :
    ∃ v : FourierLebesgueSpace (2:ℝ) (2-r) ⊤,
      v.val=(endpointReconstructionFamily r hr hr1 n (q,z) u+
        endpointResponseFamily r hr hr1 n (q,z) g).val := by
  let a := endpointEffectiveFamily r hr hr1 n (q,z) u+endpointInverseFamily r hr hr1 n (q,z) g
  obtain ⟨v₁,h₁⟩ := endpointHillH1Modes_sobolev (2-r) n u
  obtain ⟨v₂,h₂⟩ := endpointH1ResolventFamily_secondOrder_wide r hr1 n hn z hz a
  have he : endpointReconstructionFamily r hr hr1 n (q,z) u+endpointResponseFamily r hr hr1 n (q,z) g=
      endpointHillH1Modes n u+endpointH1ResolventFamily r hr1 n z a := by
    simp only [endpointReconstructionFamily,endpointResponseFamily,_root_.add_apply,
      ContinuousLinearMap.comp_apply,a,map_add,add_assoc]
  refine ⟨v₁+v₂,?_⟩
  rw [he]
  change v₁.val+v₂.val=_
  rw [h₁,h₂]
  rfl

end NLS.KdV
