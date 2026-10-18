import NLS.ZakharovShabat.PhysicalBirkhoffIntrinsic
import NLS.ZakharovShabat.PhysicalAngularReality

/-! # Global properties of the intrinsic physical Birkhoff map

The literal physical map has a named global homeomorphism and analytic
inverse. Any admissible eta choice gives the same coordinates, including
arbitrary values at closed gaps. Every original family supplies a complex
analytic extension of this independently defined real map.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The global homeomorphism whose forward map is given by the intrinsic physical integrals. -/
def intrinsicPhysicalBirkhoffHomeomorph : physicalRealSubmodule ≃ₜ PhysicalRealBirkhoffTarget :=
  intrinsicPhysicalBirkhoffMap_global_inverse.choose

/-- The homeomorphism evaluates to the literal physical sequence map. -/
@[simp] theorem intrinsicPhysicalBirkhoffHomeomorph_apply (u : physicalRealSubmodule) :
    intrinsicPhysicalBirkhoffHomeomorph u = intrinsicPhysicalBirkhoffMap u :=
  congrFun intrinsicPhysicalBirkhoffMap_global_inverse.choose_spec.1 u

/-- Both directions are analytic in the original physical Hilbert norms. -/
theorem intrinsicPhysicalBirkhoffHomeomorph_analytic :
    AnalyticOnNhd ℝ intrinsicPhysicalBirkhoffHomeomorph univ ∧
      AnalyticOnNhd ℝ intrinsicPhysicalBirkhoffHomeomorph.symm univ :=
  ⟨intrinsicPhysicalBirkhoffMap_global_inverse.choose_spec.2.1,
    intrinsicPhysicalBirkhoffMap_global_inverse.choose_spec.2.2.1⟩

/-- The independently defined physical map is real analytic on the entire real source. -/
theorem intrinsicPhysicalBirkhoffMap_analytic : AnalyticOnNhd ℝ intrinsicPhysicalBirkhoffMap univ := by
  rw [← intrinsicPhysicalBirkhoffMap_global_inverse.choose_spec.1]
  exact intrinsicPhysicalBirkhoffHomeomorph_analytic.1

/-- The global inverse recovers every physical L2 source, including collapsed-gap inputs. -/
@[simp] theorem intrinsicPhysicalBirkhoffHomeomorph_left_inv (u : physicalRealSubmodule) :
    intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u) = u := by
  rw [← intrinsicPhysicalBirkhoffHomeomorph_apply]
  exact intrinsicPhysicalBirkhoffHomeomorph.symm_apply_apply u

/-- Every real Hilbert sequence is attained by the intrinsic physical map. -/
@[simp] theorem intrinsicPhysicalBirkhoffHomeomorph_right_inv (z : PhysicalRealBirkhoffTarget) :
    intrinsicPhysicalBirkhoffMap (intrinsicPhysicalBirkhoffHomeomorph.symm z) = z := by
  rw [← intrinsicPhysicalBirkhoffHomeomorph_apply]
  exact intrinsicPhysicalBirkhoffHomeomorph.apply_symm_apply z

/-- The intrinsic nonlinear map preserves the Hilbert norm exactly. -/
theorem intrinsicPhysicalBirkhoffMap_norm (u : physicalRealSubmodule) :
    ‖intrinsicPhysicalBirkhoffMap u‖ = ‖u‖ := by
  rw [← intrinsicPhysicalBirkhoffHomeomorph_apply]
  exact intrinsicPhysicalBirkhoffMap_global_inverse.choose_spec.2.2.2 u

/-- The global inverse also preserves the Hilbert norm exactly. -/
theorem intrinsicPhysicalBirkhoffHomeomorph_symm_norm (z : PhysicalRealBirkhoffTarget) :
    ‖intrinsicPhysicalBirkhoffHomeomorph.symm z‖ = ‖z‖ := by
  simpa only [intrinsicPhysicalBirkhoffHomeomorph_right_inv] using
    (intrinsicPhysicalBirkhoffMap_norm (intrinsicPhysicalBirkhoffHomeomorph.symm z)).symm

/-- Every admissible physical eta value gives the same coordinates; closed gaps allow any value. -/
theorem intrinsicPhysicalBirkhoffMap_formula_of_eta (u : physicalRealSubmodule) (n : ℤ) (v : ℂ)
    (hv : physicalPeriodicLeft u.val n ≠ physicalPeriodicRight u.val n →
      v ∈ physicalAngularIntegralValues n n u) :
    (intrinsicPhysicalBirkhoffMap u).fst n = Real.sqrt (2*(intrinsicPhysicalAction n u).re)*
      Real.cos (v+physicalBetaCorrection n u).re ∧
    (intrinsicPhysicalBirkhoffMap u).snd n = Real.sqrt (2*(intrinsicPhysicalAction n u).re)*
      Real.sin (v+physicalBetaCorrection n u).re := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  rw [A.intrinsicPhysicalBirkhoffMap_eq,intrinsicPhysicalAction_eq_indexed,A.physicalBetaCorrection_eq_source]
  exact A.physicalRealActionAngleHomeomorph_formula_of_eta u n v
    (fun hg => A.physicalEta_value_toSource n u (hv ((physicalPeriodicGap_ne_iff u.val n).mpr hg)))

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- Every original complex family extends the same intrinsic physical real map. -/
theorem intrinsicPhysicalBirkhoffMap_complex (u : physicalRealSubmodule) :
    physicalRealTargetComplex (intrinsicPhysicalBirkhoffMap u) = physicalBirkhoffMap s u.val := by
  rw [D.intrinsicPhysicalBirkhoffMap_eq]
  exact D.physicalBirkhoffMap_real u

/-- The intrinsic global inverse equals every original physical inverse. -/
theorem intrinsicPhysicalBirkhoffHomeomorph_symm (z : PhysicalRealBirkhoffTarget) :
    intrinsicPhysicalBirkhoffHomeomorph.symm z = D.physicalRealActionAngleHomeomorph.symm z := by
  apply D.physicalRealActionAngleHomeomorph.injective
  rw [D.physicalRealActionAngleHomeomorph.apply_symm_apply]
  rw [← D.intrinsicPhysicalBirkhoffMap_eq,intrinsicPhysicalBirkhoffHomeomorph_right_inv]

end SourceSection14OriginalData

/-- The constructed complex extension is analytic on an open physical neighborhood of the real form. -/
theorem intrinsicPhysicalBirkhoffMap_complex_extension :
    ∃ U : Set IntervalPairL2, ∃ F : IntervalPairL2 → CoeffPair 2,
      IsOpen U ∧ (∀ u : physicalRealSubmodule, u.val ∈ U) ∧ AnalyticOnNhd ℂ F U ∧
      ∀ u : physicalRealSubmodule, physicalRealTargetComplex (intrinsicPhysicalBirkhoffMap u) = F u.val := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  exact ⟨physicalBirkhoffDomain V,physicalBirkhoffMap s,A.physicalBirkhoffDomain_open,
    A.physicalBirkhoffDomain_real,A.physicalBirkhoffMap_analytic,A.intrinsicPhysicalBirkhoffMap_complex⟩

end NLS.ZakharovShabat
