import NLS.ZakharovShabat.SourceBirkhoffProposition17_1
import NLS.SequenceSpaces.QuadraticActions

/-! # The actual Hilbert action sequence in ℓ¹

The Birkhoff action-radius identity identifies the quadratic sequence
map with every actual spectral action. Holomorphic dependence holds in
ℓ¹ norm, so summing and differentiating the entire series are legitimate.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The ℓ¹-valued complex action sequence for a Hilbert Birkhoff family. -/
def sourceHilbertActionSequence (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k)
    (φ : CoeffPair 2) : Coeff 1 :=
  quadraticActions (sourceBirkhoffMap (by simp) (by norm_num) s φ)

/-- Sum the complex action sequence by the bounded ℓ¹ summation map. -/
def sourceHilbertComplexTotalAction (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k)
    (φ : CoeffPair 2) : ℂ := lp.tsumCLM ℂ ℤ ℂ (sourceHilbertActionSequence s φ)

/-- The actual real action sequence, with values in real ℓ¹. -/
def sourceHilbertRealActionSequence (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k)
    (φ : realTypeSourceSubmodule 2) : RealCoeff 1 :=
  realQuadraticActions (sourceRealBirkhoffMap (by simp) (by norm_num) s φ)

/-- The real total action. The source-mass trace identity is a separate theorem. -/
def sourceHilbertTotalAction (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k)
    (φ : realTypeSourceSubmodule 2) : ℝ :=
  lp.tsumCLM ℝ ℤ ℝ (sourceHilbertRealActionSequence s φ)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Every coordinate of the ℓ¹ map is the original complex spectral action. -/
theorem hilbert_actionSequence_apply
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : CoeffPair 2) (hφ : φ ∈ W) (n : ℤ) :
    sourceHilbertActionSequence s φ n = sourceComplexAction (by simp) (by norm_num) n φ := by
  rw [sourceHilbertActionSequence, quadraticActions_apply, D.action_radius φ hφ n]
  ring

/-- Holomorphic dependence of the entire action sequence in ℓ¹ norm. -/
theorem hilbert_actionSequence_analytic
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    AnalyticOnNhd ℂ (sourceHilbertActionSequence s) W := by
  intro φ hφ
  exact (analyticOnNhd_quadraticActions _ (mem_univ _)).comp (D.analytic φ hφ)

/-- Absolute summability of the actual complex action series on the constructed domain. -/
theorem summable_norm_hilbert_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : CoeffPair 2) (hφ : φ ∈ W) :
    Summable (fun n : ℤ => ‖sourceComplexAction (by simp) (by norm_num) n φ‖) := by
  have h := (sourceHilbertActionSequence s φ).property.norm.summable_of_one
  simpa only [D.hilbert_actionSequence_apply φ hφ] using h

/-- The complex total equals the literal absolutely convergent spectral sum. -/
theorem hilbert_complexTotalAction_eq_tsum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : CoeffPair 2) (hφ : φ ∈ W) :
    sourceHilbertComplexTotalAction s φ =
      ∑' n : ℤ, sourceComplexAction (by simp) (by norm_num) n φ :=
  tsum_congr (D.hilbert_actionSequence_apply φ hφ)

/-- The complex total is holomorphic, without an assumption about termwise limits. -/
theorem hilbert_complexTotalAction_analytic
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    AnalyticOnNhd ℂ (sourceHilbertComplexTotalAction s) W :=
  (lp.tsumCLM ℂ ℤ ℂ).comp_analyticOnNhd D.hilbert_actionSequence_analytic

/-- Coordinates of the derivative are the actual individual action derivatives. -/
theorem hilbert_actionSequence_fderiv_apply
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : CoeffPair 2) (hφ : φ ∈ W) (h : CoeffPair 2) (n : ℤ) :
    (fderiv ℂ (sourceHilbertActionSequence s) φ h) n =
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ) h := by
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n
  have hd := (ev.hasFDerivAt.comp φ
    (D.hilbert_actionSequence_analytic φ hφ).differentiableAt.hasFDerivAt).fderiv
  have he : (fun ψ => ev (sourceHilbertActionSequence s ψ)) =ᶠ[𝓝 φ]
      sourceComplexAction (by simp) (by norm_num) n := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact D.hilbert_actionSequence_apply ψ hψ n
  have hh : fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ =
      ev.comp (fderiv ℂ (sourceHilbertActionSequence s) φ) := he.fderiv_eq.symm.trans hd
  exact (congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L h) hh).symm

/-- The differentiated action series is absolutely convergent in every direction. -/
theorem summable_norm_hilbert_action_derivatives
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : CoeffPair 2) (hφ : φ ∈ W) (h : CoeffPair 2) :
    Summable (fun n : ℤ => ‖(fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ) h‖) := by
  have hs := (fderiv ℂ (sourceHilbertActionSequence s) φ h).property.norm.summable_of_one
  simpa only [D.hilbert_actionSequence_fderiv_apply φ hφ h] using hs

/-- Differentiation of the full action sum equals the absolutely convergent
sum of the actual scalar derivatives. -/
theorem hilbert_complexTotalAction_fderiv_apply
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : CoeffPair 2) (hφ : φ ∈ W) (h : CoeffPair 2) :
    (fderiv ℂ (sourceHilbertComplexTotalAction s) φ) h =
      ∑' n : ℤ, (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ) h := by
  have hd := ((lp.tsumCLM ℂ ℤ ℂ).hasFDerivAt.comp φ
    (D.hilbert_actionSequence_analytic φ hφ).differentiableAt.hasFDerivAt).fderiv
  have hh := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L h) hd
  change (fderiv ℂ (sourceHilbertComplexTotalAction s) φ) h =
    ∑' n : ℤ, (fderiv ℂ (sourceHilbertActionSequence s) φ h) n at hh
  rw [hh]
  exact tsum_congr (D.hilbert_actionSequence_fderiv_apply φ hφ h)

/-- The real sequence coordinates are the original real spectral actions. -/
theorem hilbert_realActionSequence_apply
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    sourceHilbertRealActionSequence s φ n =
      (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  rw [sourceHilbertRealActionSequence, realQuadraticActions_apply, D.real_map_action_radius φ n]
  ring

/-- Absolute convergence of the literal real action sum. -/
theorem summable_hilbert_realActions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    Summable (fun n : ℤ => (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) := by
  have h := (sourceHilbertRealActionSequence s φ).property.summable_of_one
  exact h.congr (D.hilbert_realActionSequence_apply φ)

/-- The actual real action map is analytic in ℓ¹ norm on the whole real source space. -/
theorem hilbert_realActionSequence_analytic
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    AnalyticOnNhd ℝ (sourceHilbertRealActionSequence s) univ := by
  intro φ _
  exact (analyticOnNhd_realQuadraticActions _ (mem_univ _)).comp (D.real_map_analytic φ (mem_univ φ))

/-- The total actual real action is a real analytic scalar functional. -/
theorem hilbert_totalAction_analytic
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    AnalyticOnNhd ℝ (sourceHilbertTotalAction s) univ :=
  (lp.tsumCLM ℝ ℤ ℝ).comp_analyticOnNhd D.hilbert_realActionSequence_analytic

/-- The real total is the sum of the original real spectral actions. -/
theorem hilbert_totalAction_eq_tsum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceHilbertTotalAction s φ =
      ∑' n : ℤ, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re :=
  tsum_congr (D.hilbert_realActionSequence_apply φ)

/-- The ℓ¹ norm and the literal sum of actual real actions coincide. -/
theorem hilbert_realActionSequence_norm_eq_sum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    ‖sourceHilbertRealActionSequence s φ‖ =
      ∑' n : ℤ, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  rw [sourceHilbertRealActionSequence, norm_realQuadraticActions]
  change (∑' n : ℤ, sourceHilbertRealActionSequence s φ n) = _
  exact tsum_congr (D.hilbert_realActionSequence_apply φ)

end SourceBirkhoffMapComplexData

/-- Exact normalization of the total in terms of the two real output components. -/
theorem sourceHilbertTotalAction_eq_output_norms
    (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k) (φ : realTypeSourceSubmodule 2) :
    sourceHilbertTotalAction s φ =
      (‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1‖^2 +
       ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2‖^2)/2 :=
  realQuadraticActionTotal_eq _

/-- A constructed actual Hilbert family supplies the analytic ℓ¹ action map
and its literal spectral coordinates, without a summability premise. -/
theorem exists_sourceHilbertActionSequence_analytic :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s ∧
      AnalyticOnNhd ℝ (sourceHilbertRealActionSequence s) univ ∧
      ∀ φ : realTypeSourceSubmodule 2, ∀ n : ℤ,
        sourceHilbertRealActionSequence s φ n =
          (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,B,W,s,D,D.hilbert_realActionSequence_analytic,D.hilbert_realActionSequence_apply⟩

end NLS.ZakharovShabat
