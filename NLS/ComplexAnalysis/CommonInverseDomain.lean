import NLS.ComplexAnalysis.LocalRightInverseMatching

/-! # One common weak inverse domain before stronger orders and bases -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- Actual weak local injectivity and continuity give ONE open source
domain on which the GIVEN right inverse is also a left inverse. The
choice precedes every later stronger topology and source base. -/
theorem exists_common_leftInverse_domain
    {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (f : P → Q) (U : Set P) (hU : IsOpen U) (h0U : (0 : P)∈U)
    (hfc : ContinuousOn f U) (hf0 : f 0=0) (hi : InjOn f U)
    (W : Set Q) (hW : IsOpen W) (h0W : (0 : Q)∈W)
    (R : Q → P) (hRc : ContinuousOn R W) (hR0 : R 0=0)
    (hRsolve : ∀ b∈W, f (R b)=b) :
    ∃ A : Set P, IsOpen A ∧ 0∈A ∧ A⊆U ∧ ∀ a∈A,
      f a∈W ∧ R (f a)∈U ∧ R (f a)=a := by
  let B := W∩R ⁻¹' U
  have hB : IsOpen B := hRc.isOpen_inter_preimage hW hU
  have h0B : (0 : Q)∈B := ⟨h0W,by change R 0∈U;rw [hR0];exact h0U⟩
  let A := U∩f ⁻¹' B
  have hA : IsOpen A := hfc.isOpen_inter_preimage hU hB
  have h0A : (0 : P)∈A := ⟨h0U,by change f 0∈B;rw [hf0];exact h0B⟩
  refine ⟨A,hA,h0A,inter_subset_left,?_⟩
  intro a ha
  exact ⟨ha.2.1,ha.2.2,hi ha.2.2 ha.1 (hRsolve _ ha.2.1)⟩

end NLS.ComplexAnalysis
