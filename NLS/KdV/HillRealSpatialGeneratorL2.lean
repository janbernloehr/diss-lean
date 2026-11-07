import NLS.KdV.HillRealSpatialGenerator
import NLS.SequenceSpaces.SobolevDerivative

/-! The original physical Hminus-one spatial-generator domain is EXACTLY
the original L2 coefficient space. The period-two pi derivative criterion
is applied with the proved one-half factor for the physical2*pi generator. -/
noncomputable section
open Complex
namespace NLS.KdV

/-- A physical source with its spatial generator in Hminus-one has the
SAME ENTIRE original coefficient sequence in L2. -/
theorem exists_L2_of_hillRealSpatialGenerator (q v : HillRealMeanZeroSource)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k) :
    ∃ u : Coeff 2, ∀ k : ℤ, u k=q.val.val.val k := by
  have ha : Memℓp (fun k => (Weight.sobolev (-1) k:ℂ)*q.val.val.val k) 2 := q.val.val.property
  have hvm : Memℓp (fun k => (Weight.sobolev (-1) k:ℂ)*v.val.val.val k) 2 := v.val.val.property
  have hc := hvm.const_smul (1/2:ℂ)
  change Memℓp (fun k => (1/2:ℂ)*((Weight.sobolev (-1) k:ℂ)*v.val.val.val k)) 2 at hc
  have he (k : ℤ) : (1/2:ℂ)*((Weight.sobolev (-1) k:ℂ)*v.val.val.val k)=
      (Weight.sobolev (-1) k:ℂ)*(I*(Real.pi:ℂ)*k*q.val.val.val k) := by
    rw [hv]
    push_cast
    ring
  simp_rw [he] at hc
  have hd : Memℓp (fun k => (Weight.sobolev (-1) k:ℂ)*(I*(Real.pi:ℂ)*k*q.val.val.val k)) 2 := hc
  have h0 := WeightedCoeff.memlp_sobolev_succ_of_derivative (-1) ha hd
  have hw (k : ℤ) : (Weight.sobolev ((-1:ℝ)+1) k:ℂ)=1 := by
    simp [Weight.sobolev_apply]
  simp_rw [hw,one_mul] at h0
  exact ⟨⟨q.val.val.val,h0⟩,fun _ => rfl⟩

/-- Exact source generator-domain characterization in the original spaces. -/
theorem hillReal_source_L2_iff_spatialGenerator (q : HillRealMeanZeroSource) :
    (∃ u : Coeff 2, ∀ k : ℤ, u k=q.val.val.val k) ↔
      ∃ v : HillRealMeanZeroSource, ∀ k : ℤ,
        v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k := by
  constructor
  · rintro ⟨u,hu⟩
    exact exists_hillRealSpatialGenerator_of_L2 q u hu
  · rintro ⟨v,hv⟩
    exact exists_L2_of_hillRealSpatialGenerator q v hv

end NLS.KdV
