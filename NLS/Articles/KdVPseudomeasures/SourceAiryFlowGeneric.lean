import NLS.Articles.KdVPseudomeasures.SourceStrongFlowObstruction
import NLS.SequenceSpaces.FourierRealC0Generic

/-! The physical free Airy flow on the original endpoint potentials.
Its Fourier formula uses the unchanged period-one frequencies (2*pi*k)^3. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def sourceAiryFrequency (k : ℤ) : ℝ := (2*Real.pi*(k:ℝ))^3

theorem sourceAiryFrequency_neg (k : ℤ) : sourceAiryFrequency (-k)=-sourceAiryFrequency k := by
  simp only [sourceAiryFrequency,Int.cast_neg]
  ring

def sourceAiryFlow (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (t : ℝ) : Potential r :=
  originalEndpointPotential r hr (fourierRealZeroPhaseFlow (Weight.sobolev (-r))
    sourceAiryFrequency sourceAiryFrequency_neg t (originalEndpointRealSource r hr q))

theorem sourceAiryFlow_coefficients (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (t : ℝ) (k : ℤ) :
    (originalEndpointRealSource r hr (sourceAiryFlow r hr q t)).val.val.val k=
      Complex.exp (((t*sourceAiryFrequency k:ℝ):ℂ)*Complex.I)*
        (originalEndpointRealSource r hr q).val.val.val k := by
  rw [sourceAiryFlow,originalEndpointRealSource_potential,fourierRealZeroPhaseFlow_apply]

theorem sourceAiryFrequency_tendsto :
    Tendsto (fun j : ℕ => sourceAiryFrequency ((j+1:ℕ):ℤ)) atTop atTop := by
  have hx : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hb := hx.const_mul_atTop (show 0<2*Real.pi from by positivity)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<3 by norm_num)).comp hb
  simpa only [sourceAiryFrequency,Int.cast_add,Int.cast_one,Int.cast_natCast,Nat.cast_add,Nat.cast_one,Real.rpow_natCast,Real.rpow_ofNat,Function.comp_def] using hp

theorem sourceAiry_not_continuousAt_norm_of_not_c0 (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (hq : ¬PositiveWeightedC0 (Weight.sobolev (-r)) (originalEndpointRealSource r hr q)) :
    ¬ContinuousAt (sourceAiryFlow r hr q) 0 := by
  intro hc
  have hcurve : ContinuousAt (fun t => originalEndpointRealSource r hr (sourceAiryFlow r hr q t)) 0 :=
    (continuous_originalEndpointRealSource r hr).continuousAt.comp hc
  apply hq
  apply positiveWeightedC0_of_continuous_positive_phases (Weight.sobolev (-r))
    (originalEndpointRealSource r hr q)
    (fun t => originalEndpointRealSource r hr (sourceAiryFlow r hr q t))
    (by rw [sourceAiryFlow,originalEndpointRealSource_potential,fourierRealZeroPhaseFlow_zero])
    (fun j => sourceAiryFrequency ((j+1:ℕ):ℤ)) sourceAiryFrequency_tendsto _ hcurve
  intro t j
  exact sourceAiryFlow_coefficients r hr q t ((j+1:ℕ):ℤ)

/-- Airy norm discontinuity holds on an open dense subset of the actual
original endpoint source, with its original norm topology. -/
theorem sourceRemark1_2_Airy (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ G : Set (Potential r), IsOpen G ∧ Dense G ∧
      ∀ q ∈ G, ¬ContinuousAt (sourceAiryFlow r hr q) 0 := by
  let G := {q : Potential r | ¬PositiveWeightedC0 (Weight.sobolev (-r)) (originalEndpointRealSource r hr q)}
  refine ⟨G,?_,?_,fun q hq => sourceAiry_not_continuousAt_norm_of_not_c0 r hr q hq⟩
  · exact (isOpen_not_positiveWeightedC0 (Weight.sobolev (-r))).preimage (continuous_originalEndpointRealSource r hr)
  · exact (dense_not_positiveWeightedC0 (Weight.sobolev (-r)) (Weight.sobolev_neg (-r))).preimage
      (originalEndpointRealSourceHomeomorph r hr).isOpenMap

end NLS.Articles.KdVPseudomeasures
