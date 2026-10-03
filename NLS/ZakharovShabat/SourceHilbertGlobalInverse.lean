import NLS.FunctionalAnalysis.ClosedLocalHomeomorph
import NLS.ZakharovShabat.SourceBirkhoffLocalHomeomorph
import NLS.ZakharovShabat.SourceHilbertProperness
import Mathlib.Analysis.Normed.Module.Connected

/-! # The global real analytic Hilbert Birkhoff inverse

Properness makes the actual map closed. Its proved local inverse and
singleton zero fiber give global bijectivity over the connected target.
The resulting homeomorphism agrees locally with each analytic inverse,
so its global inverse is analytic everywhere.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The actual real Hilbert Birkhoff map is globally bijective. -/
theorem hilbert_real_map_bijective
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    Function.Bijective (sourceRealBirkhoffMap (by simp) (by norm_num) s) := by
  apply NLS.FunctionalAnalysis.bijective_of_closed_localHomeomorph_singleton_fiber
    _ D.real_map_isLocalHomeomorph D.hilbert_real_map_proper.isClosedMap 0
  intro φ hφ
  apply (D.hilbert_real_map_eq_zero_iff φ).mp
  exact hφ.trans ((D.hilbert_real_map_eq_zero_iff 0).mpr rfl)

/-- The original real Hilbert Birkhoff map, bundled as a global homeomorphism. -/
def hilbertRealHomeomorph
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    realTypeSourceSubmodule 2 ≃ₜ (RealCoeff 2 × RealCoeff 2) :=
  D.real_map_isLocalHomeomorph.toHomeomorphOfBijective D.hilbert_real_map_bijective

@[simp] theorem hilbertRealHomeomorph_apply
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    D.hilbertRealHomeomorph φ = sourceRealBirkhoffMap (by simp) (by norm_num) s φ := rfl

/-- The global inverse agrees near every target point with its proved
analytic local inverse. -/
theorem hilbertRealHomeomorph_symm_analytic
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    AnalyticOnNhd ℝ D.hilbertRealHomeomorph.symm univ := by
  intro y _
  let φ := D.hilbertRealHomeomorph.symm y
  have hφ : sourceRealBirkhoffMap (by simp) (by norm_num) s φ = y :=
    D.hilbertRealHomeomorph.apply_symm_apply y
  obtain ⟨g,hg,_,_,hr,_⟩ := D.proposition17_1 φ
  rw [hφ] at hg hr
  apply hg.congr
  filter_upwards [hr] with z hz
  apply D.hilbert_real_map_bijective.1
  exact hz.trans (D.hilbertRealHomeomorph.apply_symm_apply z).symm

end SourceBirkhoffMapComplexData

/-- A constructed normalized family supplies a global real analytic
Hilbert Birkhoff homeomorphism and an analytic inverse everywhere. -/
theorem exists_sourceBirkhoffFamily_hilbert_globalInverse :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s ∧
      ∃ e : realTypeSourceSubmodule 2 ≃ₜ (RealCoeff 2 × RealCoeff 2),
        (∀ φ, e φ = sourceRealBirkhoffMap (by simp) (by norm_num) s φ) ∧
        AnalyticOnNhd ℝ (fun φ => e φ) univ ∧ AnalyticOnNhd ℝ (fun y => e.symm y) univ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,B,W,s,D,D.hilbertRealHomeomorph,fun _ => rfl,D.real_map_analytic,D.hilbertRealHomeomorph_symm_analytic⟩

end NLS.ZakharovShabat
