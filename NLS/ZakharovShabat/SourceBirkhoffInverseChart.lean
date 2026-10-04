import NLS.ZakharovShabat.SourceBirkhoffProposition17_1
import NLS.ZakharovShabat.SourceActionSequenceExponent
import NLS.ZakharovShabat.SourceActionTorus

/-! # Complex inverse charts compatible with the real source locus

At every real source the complex Birkhoff inverse can be restricted to
any prescribed open source neighborhood. The same chart preserves real
coordinates and identifies the original actions with quadratic actions.
This supplies coordinate charts for analytic descent, not the descent itself.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- An actual complex inverse chart with real compatibility, restricted
inside a prescribed source neighborhood. -/
structure SourceBirkhoffInverseChart
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (U : Set (CoeffPair p)) where
  inverse : (Coeff p × Coeff p) → CoeffPair p
  target : Set (Coeff p × Coeff p)
  target_open : IsOpen target
  center_mem : sourceBirkhoffMap hp hp1 s φ.val ∈ target
  analytic : AnalyticOnNhd ℂ inverse target
  base_eq : inverse (sourceBirkhoffMap hp hp1 s φ.val) = φ.val
  image_subset : MapsTo inverse target (W ∩ U)
  right_inverse : ∀ z ∈ target, sourceBirkhoffMap hp hp1 s (inverse z) = z
  left_inverse : ∀ᶠ ψ in 𝓝 φ.val, inverse (sourceBirkhoffMap hp hp1 s ψ) = ψ
  real_preserving : ∀ z : RealCoeff p × RealCoeff p,
    ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ target →
    inverse (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z) ∈
      realTypeSourceLocus p

namespace SourceBirkhoffMapComplexData

/-- Complex and real local inverses agree on a real neighborhood. -/
theorem complex_localInverse_real_germ
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p)
    (g : (Coeff p × Coeff p) → CoeffPair p)
    (hl : ∀ᶠ ψ in 𝓝 φ.val, g (sourceBirkhoffMap hp hp1 s ψ) = ψ) :
    ∀ᶠ z in 𝓝 (sourceRealBirkhoffMap hp hp1 s φ),
      g (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z) ∈
        realTypeSourceLocus p := by
  obtain ⟨gR,ha,hbase,_,hr,_⟩ := D.proposition17_1 φ
  have hc : Tendsto (fun z => (gR z).val)
      (𝓝 (sourceRealBirkhoffMap hp hp1 s φ)) (𝓝 φ.val) := by
    have hv : Continuous (fun ψ : realTypeSourceSubmodule p => ψ.val) := continuous_subtype_val
    have ht := (hv.continuousAt (x := gR (sourceRealBirkhoffMap hp hp1 s φ))).tendsto.comp
      ha.continuousAt.tendsto
    simpa only [Function.comp_def,hbase] using ht
  filter_upwards [hc.eventually hl,hr] with z hz hzr
  have he := D.real_map_complex_inclusion (gR z)
  rw [hzr] at he
  rw [he,hz]
  exact (gR z).property

/-- Construct a real-compatible complex chart inside any open source
neighborhood, without supplying a reality premise for the complex inverse. -/
theorem exists_inverseChart
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hφU : φ.val ∈ U) :
    Nonempty (SourceBirkhoffInverseChart D φ U) := by
  obtain ⟨g,ha,hbase,hl,hr,_⟩ := D.exists_complex_localInverse_all_exponents φ
  let inc := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  let re := (Coeff.reCLM p).prodMap (Coeff.reCLM p)
  have hre (z : RealCoeff p × RealCoeff p) : re (inc z) = z := by
    ext n <;> simp [re,inc]
  have hcenter : re (sourceBirkhoffMap hp hp1 s φ.val) =
      sourceRealBirkhoffMap hp hp1 s φ := by
    rw [← D.real_map_complex_inclusion φ]
    exact hre _
  obtain ⟨R,hRsub,hRopen,hRmem⟩ :=
    mem_nhds_iff.mp (D.complex_localInverse_real_germ φ g hl)
  have hreal : ∀ᶠ z in 𝓝 (sourceBirkhoffMap hp hp1 s φ.val), re z ∈ R := by
    have ht := (re.continuous.continuousAt (x := sourceBirkhoffMap hp hp1 s φ.val)).tendsto
    rw [hcenter] at ht
    exact ht.eventually (hRopen.mem_nhds hRmem)
  have hsource : ∀ᶠ z in 𝓝 (sourceBirkhoffMap hp hp1 s φ.val), g z ∈ W ∩ U := by
    have ht := ha.continuousAt.tendsto
    rw [hbase] at ht
    exact ht.eventually ((D.source_open.inter hU).mem_nhds ⟨D.real_subset φ.property,hφU⟩)
  have hall := ha.eventually_analyticAt.and (hr.and (hsource.and hreal))
  obtain ⟨T,hTsub,hTopen,hTmem⟩ := mem_nhds_iff.mp hall
  refine ⟨{
    inverse := g
    target := T
    target_open := hTopen
    center_mem := hTmem
    analytic := fun z hz => (hTsub hz).1
    base_eq := hbase
    image_subset := fun z hz => (hTsub hz).2.2.1
    right_inverse := fun z hz => (hTsub hz).2.1
    left_inverse := hl
    real_preserving := ?_ }⟩
  intro z hz
  apply hRsub
  have hrz : re (inc z) ∈ R := (hTsub hz).2.2.2
  rwa [hre] at hrz

end SourceBirkhoffMapComplexData
namespace SourceBirkhoffInverseChart
variable {D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s}
  {φ : realTypeSourceSubmodule p} {U : Set (CoeffPair p)}

/-- The original spectral action has exactly its quadratic coordinate value. -/
theorem action_eq (C : SourceBirkhoffInverseChart D φ U)
    (z : Coeff p × Coeff p) (hz : z ∈ C.target) (n : ℤ) :
    sourceComplexAction hp hp1 n (C.inverse z) = (z.1 n ^ 2 + z.2 n ^ 2) / 2 := by
  have h := D.action_radius (C.inverse z) (C.image_subset hz).1 n
  rw [C.right_inverse z hz] at h
  linear_combination -(1 / 2 : ℂ) * h

/-- The inverse chart recovers the entire action sequence, including zero actions. -/
theorem actionSequence_eq {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderTriple p q]
    (C : SourceBirkhoffInverseChart D φ U) (z : Coeff p × Coeff p) (hz : z ∈ C.target) :
    sourceActionSequence (q := q) hp hp1 s (C.inverse z) = quadraticActionsExponent z := by
  unfold sourceActionSequence
  rw [C.right_inverse z hz]

/-- Restrict the inverse to real coordinates in its target. -/
def realInverse (C : SourceBirkhoffInverseChart D φ U)
    (z : RealCoeff p × RealCoeff p)
    (hz : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ C.target) :
    realTypeSourceSubmodule p :=
  ⟨C.inverse (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z),
    C.real_preserving z hz⟩

/-- The real chart also has the actual right inverse identity. -/
theorem real_right_inverse (C : SourceBirkhoffInverseChart D φ U)
    (z : RealCoeff p × RealCoeff p)
    (hz : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ C.target) :
    sourceRealBirkhoffMap hp hp1 s (C.realInverse z hz) = z := by
  have h := (D.real_map_complex_inclusion (C.realInverse z hz)).trans
    (C.right_inverse _ hz)
  apply Prod.ext <;> ext n
  · simpa using congrArg (fun a : Coeff p × Coeff p => (a.1 n).re) h
  · simpa using congrArg (fun a : Coeff p × Coeff p => (a.2 n).re) h

/-- Equal quadratic real actions lift to equal original source actions. -/
theorem realInverse_mem_actionLevelSet (C : SourceBirkhoffInverseChart D φ U)
    (z w : RealCoeff p × RealCoeff p)
    (hz : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z ∈ C.target)
    (hw : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) w ∈ C.target)
    (he : ∀ n, RealCoeff.pairAction w n = RealCoeff.pairAction z n) :
    C.realInverse w hw ∈ sourceRealActionLevelSet hp hp1 (C.realInverse z hz) := by
  intro n
  rw [← D.real_pairAction_eq,← D.real_pairAction_eq,
    C.real_right_inverse w hw,C.real_right_inverse z hz]
  exact he n

/-- Analytic source maps transport through the same chart for every target space. -/
theorem analytic_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (C : SourceBirkhoffInverseChart D φ U) (f : CoeffPair p → F)
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ (f ∘ C.inverse) C.target := by
  intro z hz
  exact (hf _ (C.image_subset hz).2).comp (C.analytic z hz)

end SourceBirkhoffInverseChart
end NLS.ZakharovShabat
