import NLS.ZakharovShabat.SourceFiniteGapNonzeroMomentum
import NLS.ZakharovShabat.SourceSection19Laurent

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The cubic Laurent part printed again in the proof of Lemma 20.2,
where the momentum coefficient has changed from -3i/4 to +3/4. -/
def section20PrintedCubePart (H₁ H₂ H₃ z : ℂ) : ℂ :=
  I*z^3-(3*I/2)*H₁*z+(3/4:ℂ)*H₂-(3*I/8)*(H₃-2*H₁^2)/z

/-- The two displayed Laurent parts differ by a constant momentum multiple. -/
theorem cubeLaurentPart_sub_section20Printed (H₁ H₂ H₃ z : ℂ) :
    phaseCubeLaurentPart H₁ H₂ H₃ z-section20PrintedCubePart H₁ H₂ H₃ z =
      -(3/4:ℂ)*(1+I)*H₂ := by
  unfold phaseCubeLaurentPart section20PrintedCubePart
  ring

/-- A nonzero momentum constant cannot be absorbed in a quadratic remainder at infinity. -/
theorem not_section20Printed_cube_isBigO
    (f : ℂ → ℂ) (H₁ H₂ H₃ : ℂ) (h₂ : H₂ ≠ 0)
    (hf : (fun z => f z-phaseCubeLaurentPart H₁ H₂ H₃ z)
      =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹^2)) :
    ¬ (fun z => f z-section20PrintedCubePart H₁ H₂ H₃ z)
      =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹^2) := by
  intro hbad
  have hd := hbad.sub hf
  have hc : (fun _ : ℂ => -(3/4:ℂ)*(1+I)*H₂)
      =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹^2) := by
    apply hd.congr_left
    intro z
    rw [← cubeLaurentPart_sub_section20Printed H₁ H₂ H₃ z]
    ring
  have ht : Tendsto (fun z : ℂ => z⁻¹^2) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0)] using
      (tendsto_inv₀_cobounded (α := ℂ)).pow 2
  have hz : -(3/4:ℂ)*(1+I)*H₂ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hc.trans_tendsto ht)
  have hcoef : -(3/4:ℂ)*(1+I) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    intro he
    have hre := congrArg Complex.re he
    norm_num at hre
  exact (mul_ne_zero hcoef h₂) hz

namespace SourceSection19Data
variable {W U : Set (CoeffPair 2)} (Q : SourceSection19Data (by simp) (by norm_num) W U)
include Q

/-- Every original Section 19 domain has an actual real finite-gap source
refuting the reprinted p.93 expansion. Corollary 19.3 retains its valid coefficient. -/
theorem exists_section20Printed_cube_counterexample :
    ∃ φ : realTypeSourceSubmodule 2, ∃ hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num),
      φ.val ∈ U ∧ sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2 ≠ 0 ∧
      ¬ (fun z : ℂ => (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,φ.val))^3-
        section20PrintedCubePart (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1)
          (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2)
          (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 3) z)
        =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹^2) := by
  obtain ⟨φ,hf,h₂⟩ := exists_sourceFiniteGap_nonzero_momentum
  exact ⟨φ,hf,Q.real_subset φ.property,h₂,
    not_section20Printed_cube_isBigO _ _ _ _ h₂ (Q.cube_isBigO φ hf)⟩

end SourceSection19Data
end NLS.ZakharovShabat
