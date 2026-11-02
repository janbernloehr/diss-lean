import NLS.Articles.MKdVBelowL2.PhysicalScalarRealInput
import NLS.Articles.MKdVBelowL2.PhysicalMKdVFlowPreservation
import NLS.Articles.MKdVBelowL2.PhysicalFourthImageIdentities

/-! # Fourth trajectories on scalar real physical distributions

The scalar adapter is isometric. Local trajectories and the one invariant
neighborhood of zero inherit the full uniform trajectory norm of the actual
physical inverse lift. The smooth PDE identification is a separate theorem.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original equal physical pair of a scalar real distribution. -/
def physicalScalarPairCLM : PhysicalScalarRealInput p →L[ℝ] PhysicalRealInput p :=
  (physicalMKdVSubspace p).subtypeL.comp
    (physicalScalarDiagonal (p := p)).toContinuousLinearEquiv.toContinuousLinearMap

/-- Actual admissible scalar time-input pairs. -/
def fourthScalarImageDomain (hp : p ≠ ⊤) (hp1 : 1 < p) : Set (ℝ × PhysicalScalarRealInput p) :=
  {x | (x.1,physicalScalarPairCLM x.2) ∈ fourthPhysicalImageDomain hp hp1}

/-- Actual scalar inverse lift; outside its asserted domain choose the input. -/
def fourthScalarImageFlow (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalScalarRealInput p) (τ : ℝ) : PhysicalScalarRealInput p := by
  classical
  exact if h : (τ,u) ∈ fourthScalarImageDomain hp hp1 then
    (physicalScalarDiagonal (p := p)).symm ⟨fourthPhysicalImageFlow hp hp1 (physicalScalarPairCLM u) τ,
      fourthPhysicalImageFlow_preserves_mKdV hp hp1 (physicalScalarDiagonal u) τ h⟩
  else u

theorem fourthScalarImageFlow_pair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalScalarRealInput p) (τ : ℝ) (h : (τ,u) ∈ fourthScalarImageDomain hp hp1) :
    physicalScalarPairCLM (fourthScalarImageFlow hp hp1 u τ) =
      fourthPhysicalImageFlow hp hp1 (physicalScalarPairCLM u) τ := by
  unfold fourthScalarImageFlow
  rw [dif_pos h]
  exact congrArg Subtype.val ((physicalScalarDiagonal (p := p)).apply_symm_apply _)

theorem fourthScalarImageFlow_val (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalScalarRealInput p) (τ : ℝ) (h : (τ,u) ∈ fourthScalarImageDomain hp hp1) :
    (fourthScalarImageFlow hp hp1 u τ).val =
      (fourthPhysicalImageFlow hp hp1 (physicalScalarPairCLM u) τ).val.1 :=
  congrArg (fun v : PhysicalRealInput p => v.val.1) (fourthScalarImageFlow_pair hp hp1 u τ h)

theorem zero_mem_fourthScalarImageDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalScalarRealInput p) : (0,u) ∈ fourthScalarImageDomain hp hp1 :=
  zero_mem_fourthPhysicalImageDomain hp hp1 _

@[simp] theorem fourthScalarImageFlow_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalScalarRealInput p) : fourthScalarImageFlow hp hp1 u 0 = u := by
  apply Subtype.ext
  rw [fourthScalarImageFlow_val hp hp1 u 0 (zero_mem_fourthScalarImageDomain hp hp1 u),
    fourthPhysicalImageFlow_zero]
  rfl

theorem isOpen_fourthScalarImageDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsOpen (fourthScalarImageDomain hp hp1) :=
  (isOpen_fourthPhysicalImageDomain hp hp1).preimage
    (continuous_fst.prodMk (physicalScalarPairCLM.continuous.comp continuous_snd))

theorem continuousOn_fourthScalarImageFlow (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ContinuousOn (fun x : ℝ × PhysicalScalarRealInput p => fourthScalarImageFlow hp hp1 x.2 x.1)
      (fourthScalarImageDomain hp hp1) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  have hc := (continuous_fst.comp continuous_subtype_val).comp_continuousOn
    ((continuousOn_fourthPhysicalImageFlow hp hp1).comp
      (continuous_fst.prodMk (physicalScalarPairCLM.continuous.comp continuous_snd)).continuousOn
      (fun _ h => h))
  exact hc.congr (fun x hx => fourthScalarImageFlow_val hp hp1 x.2 x.1 hx)

/-- One common compact-time domain for the scalar physical source. -/
def fourthScalarTrajectoryDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) :
    Set (PhysicalScalarRealInput p) :=
  physicalScalarPairCLM ⁻¹' fourthPhysicalTrajectoryDomain hp hp1 T

/-- Scalar continuous paths with the original physical uniform norm. -/
def fourthScalarTrajectoryOn (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (u : PhysicalScalarRealInput p) : C(Icc (-T) T,PhysicalScalarRealInput p) :=
  ContinuousMap.mkD (fun τ => fourthScalarImageFlow hp hp1 u τ.val) 0

theorem isOpen_fourthScalarTrajectoryDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) :
    IsOpen (fourthScalarTrajectoryDomain hp hp1 T) :=
  (isOpen_fourthPhysicalTrajectoryDomain hp hp1 T).preimage physicalScalarPairCLM.continuous

theorem fourthScalarTrajectoryOn_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (u : PhysicalScalarRealInput p) (hu : u ∈ fourthScalarTrajectoryDomain hp hp1 T)
    (τ : Icc (-T) T) : fourthScalarTrajectoryOn hp hp1 T u τ = fourthScalarImageFlow hp hp1 u τ.val := by
  apply ContinuousMap.mkD_apply_of_continuous
  exact (continuousOn_fourthScalarImageFlow hp hp1).comp_continuous
    (f := fun r : Icc (-T) T => (r.val,u))
    (continuous_subtype_val.prodMk continuous_const) (fun r => hu r)

/-- Dependence on scalar initial data is continuous in the full uniform norm. -/
theorem continuousOn_fourthScalarTrajectoryOn (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ) :
    ContinuousOn (fourthScalarTrajectoryOn hp hp1 T) (fourthScalarTrajectoryDomain hp hp1 T) := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  exact (continuousOn_fourthScalarImageFlow hp hp1).comp
    (f := fun x : PhysicalScalarRealInput p × Icc (-T) T => (x.2.val,x.1))
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst).continuousOn
    (fun x hx => hx.1 x.2)

theorem exists_local_fourthScalarTrajectory (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalScalarRealInput p) :
    ∃ T > 0, ∃ U : Set (PhysicalScalarRealInput p), IsOpen U ∧ u ∈ U ∧
      U ⊆ fourthScalarTrajectoryDomain hp hp1 T ∧ ContinuousOn (fourthScalarTrajectoryOn hp hp1 T) U := by
  obtain ⟨T,hT,V,hV,hu,hmap,_⟩ := exists_local_fourthPhysicalTrajectory hp hp1 (physicalScalarPairCLM u)
  exact ⟨T,hT,physicalScalarPairCLM ⁻¹' V,hV.preimage physicalScalarPairCLM.continuous,hu,
    fun _ h => hmap h,(continuousOn_fourthScalarTrajectoryOn hp hp1 T).mono (fun _ h => hmap h)⟩

/-- A single invariant open scalar neighborhood works before every T. -/
theorem exists_global_small_fourthScalarTrajectory (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U : Set (PhysicalScalarRealInput p), IsOpen U ∧ (0 : PhysicalScalarRealInput p) ∈ U ∧
      (∀ T : ℝ, U ⊆ fourthScalarTrajectoryDomain hp hp1 T ∧
        ContinuousOn (fourthScalarTrajectoryOn hp hp1 T) U) ∧
      ∀ u ∈ U, ∀ τ : ℝ, fourthScalarImageFlow hp hp1 u τ ∈ U := by
  obtain ⟨V,hV,hzero,hmap,hinv⟩ := exists_global_small_fourthPhysicalTrajectory hp hp1
  have hU (T : ℝ) : physicalScalarPairCLM ⁻¹' V ⊆ fourthScalarTrajectoryDomain hp hp1 T :=
    fun _ h => (hmap T).1 h
  refine ⟨physicalScalarPairCLM ⁻¹' V,hV.preimage physicalScalarPairCLM.continuous,?_,
    fun T => ⟨hU T,(continuousOn_fourthScalarTrajectoryOn hp hp1 T).mono (hU T)⟩,?_⟩
  · simpa only [mem_preimage,map_zero] using hzero
  · intro u hu τ
    have hτ : (τ,u) ∈ fourthScalarImageDomain hp hp1 := by
      exact hU |τ| hu ⟨τ,by constructor <;> linarith [le_abs_self τ,neg_abs_le τ]⟩
    change physicalScalarPairCLM (fourthScalarImageFlow hp hp1 u τ) ∈ V
    rw [fourthScalarImageFlow_pair hp hp1 u τ hτ]
    exact hinv _ hu τ

/-- Every convergent family has uniformly convergent scalar paths on a common
admissible interval; openness supplies eventual admissibility of approximants. -/
theorem tendstoUniformly_fourthScalarImageFlow (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    {ι : Type*} {l : Filter ι} (u : ι → PhysicalScalarRealInput p) (v : PhysicalScalarRealInput p)
    (hv : v ∈ fourthScalarTrajectoryDomain hp hp1 T) (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun i (τ : Icc (-T) T) => fourthScalarImageFlow hp hp1 (u i) τ.val)
      (fun τ => fourthScalarImageFlow hp hp1 v τ.val) l := by
  have hc := (continuousOn_fourthScalarTrajectoryOn hp hp1 T v hv).continuousAt
    ((isOpen_fourthScalarTrajectoryDomain hp hp1 T).mem_nhds hv)
  have hl := ContinuousMap.tendsto_iff_tendstoUniformly.mp (hc.tendsto.comp hu)
  change TendstoUniformly (fun i (τ : Icc (-T) T) => fourthScalarTrajectoryOn hp hp1 T (u i) τ)
    (fun τ => fourthScalarTrajectoryOn hp hp1 T v τ) l at hl
  have hb : (fun τ : Icc (-T) T => fourthScalarTrajectoryOn hp hp1 T v τ) =
      fun τ => fourthScalarImageFlow hp hp1 v τ.val :=
    funext (fourthScalarTrajectoryOn_apply hp hp1 T v hv)
  rw [hb] at hl
  have he : (fun i (τ : Icc (-T) T) => fourthScalarTrajectoryOn hp hp1 T (u i) τ) =ᶠ[l]
      (fun i τ => fourthScalarImageFlow hp hp1 (u i) τ.val) := by
    filter_upwards [hu.eventually ((isOpen_fourthScalarTrajectoryDomain hp hp1 T).mem_nhds hv)] with i hi
    exact funext (fourthScalarTrajectoryOn_apply hp hp1 T (u i) hi)
  exact (tendstoUniformly_congr he).mp hl

end NLS.Articles.MKdVBelowL2
