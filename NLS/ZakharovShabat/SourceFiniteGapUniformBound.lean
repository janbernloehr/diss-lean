import NLS.ZakharovShabat.SourceFiniteGapEnergyConservation
import NLS.ZakharovShabat.SourceSobolevEnergyCoercivity
import NLS.ZakharovShabat.SourceFiniteGapClassicalRenormalizedNLS

/-! # Uniform physical bounds for finite-gap approximations

Energy conservation and H¹ coercivity supply a time-independent bound for
the actual continuous physical trajectories. H¹-convergent families have
an eventual common bound, without a common number of open gaps.
-/
noncomputable section
open Set Filter Topology NLS.Fourier
namespace NLS.ZakharovShabat

/-- The coefficient-preserving finite-gap H¹ pair lies on the real locus. -/
def sourceFiniteGapRealSobolev (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) : realTypeSobolevSourceLocus :=
  ⟨sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf,by
    rw [sobolevSourceInclusion_sourceFiniteGapSobolevPair]
    exact φ.property⟩

namespace SourceAbelianMomentAtlas
variable {W V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical ordinary finite-gap trajectory is bounded for all real time
by a continuous function of the initial H¹ mass and energy alone. -/
theorem norm_hamiltonianOrdinaryContinuousFlow_le_energy
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    ‖A.hamiltonianOrdinaryContinuousFlow D φ hf time‖ ≤
      sobolevEnergyAmplitude (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) := by
  let ψ := A.hamiltonianOrdinarySourceFlow D le_rfl φ time
  have hg := A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time
  have hb := norm_periodOneSobolevSynthesis_le_energy (sourceFiniteGapRealSobolev ψ hg)
  have hm : periodOneSobolevMass (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hg) =
      periodOneSobolevMass (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) := by
    rw [periodOneSobolevMass_sourceFiniteGapSobolevPair,periodOneSobolevMass_sourceFiniteGapSobolevPair,
      sourceFiniteGapNLSHamiltonian_one_eq_ordinaryMass,sourceFiniteGapNLSHamiltonian_one_eq_ordinaryMass]
    exact congrArg (fun m : ℝ => (m : ℂ)) (A.hamiltonianOrdinarySourceFlow_mass D le_rfl φ time)
  change ‖A.hamiltonianOrdinaryContinuousFlow D φ hf time‖ ≤
    sobolevEnergyAmplitude (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hg) at hb
  have he : periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hg) =
      periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) :=
    A.hamiltonianOrdinarySourceFlow_energy D φ hf time
  simpa only [sobolevEnergyAmplitude,hm,he] using hb

/-- The renormalized physical finite-gap trajectory has the same all-time bound. -/
theorem norm_hamiltonianRenormalizedContinuousFlow_le_energy
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    ‖A.hamiltonianRenormalizedContinuousFlow D φ hf time‖ ≤
      sobolevEnergyAmplitude (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) := by
  let ψ := A.hamiltonianRenormalizedSourceFlow D le_rfl φ time
  have hg := A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time
  have hb := norm_periodOneSobolevSynthesis_le_energy (sourceFiniteGapRealSobolev ψ hg)
  have hm : periodOneSobolevMass (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hg) =
      periodOneSobolevMass (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) := by
    rw [periodOneSobolevMass_sourceFiniteGapSobolevPair,periodOneSobolevMass_sourceFiniteGapSobolevPair,
      sourceFiniteGapNLSHamiltonian_one_eq_ordinaryMass,sourceFiniteGapNLSHamiltonian_one_eq_ordinaryMass]
    exact congrArg (fun m : ℝ => (m : ℂ)) (A.hamiltonianRenormalizedSourceFlow_mass D le_rfl φ time)
  change ‖A.hamiltonianRenormalizedContinuousFlow D φ hf time‖ ≤
    sobolevEnergyAmplitude (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hg) at hb
  have he : periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hg) =
      periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) :=
    A.hamiltonianRenormalizedSourceFlow_energy D φ hf time
  simpa only [sobolevEnergyAmplitude,hm,he] using hb

/-- H¹-convergent finite-gap families admit an eventual common physical
bound for both equations, uniformly over the whole real time axis. -/
theorem exists_eventual_uniform_finiteGap_bound
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    {ι : Type*} {l : Filter ι} (a : realTypeSobolevSourceLocus)
    (b : ι → realTypeSobolevSourceLocus) (hf : ∀ j, b j ∈ sourceSobolevFiniteGapLocus)
    (hb : Tendsto b l (𝓝 a)) :
    ∃ M > 0, ∀ᶠ j in l, ∀ time : ℝ,
      ‖A.hamiltonianOrdinaryContinuousFlow D ⟨sobolevSourceInclusion (b j).val,(b j).property⟩ (hf j) time‖ ≤ M ∧
      ‖A.hamiltonianRenormalizedContinuousFlow D ⟨sobolevSourceInclusion (b j).val,(b j).property⟩ (hf j) time‖ ≤ M := by
  let M := sobolevEnergyAmplitude a.val+1
  have hM : 0 < M := by dsimp [M]; linarith [sobolevEnergyAmplitude_nonneg a.val]
  refine ⟨M,hM,?_⟩
  have hc := (continuous_sobolevEnergyAmplitude.comp continuous_subtype_val).continuousAt.tendsto.comp hb
  have hm : sobolevEnergyAmplitude a.val < M := by dsimp [M]; linarith
  filter_upwards [hc.eventually (gt_mem_nhds hm)] with j hj
  intro time
  have ho := A.norm_hamiltonianOrdinaryContinuousFlow_le_energy D
    ⟨sobolevSourceInclusion (b j).val,(b j).property⟩ (hf j) time
  have hr := A.norm_hamiltonianRenormalizedContinuousFlow_le_energy D
    ⟨sobolevSourceInclusion (b j).val,(b j).property⟩ (hf j) time
  rw [sourceFiniteGapSobolevPair_sobolevSource (b j) (hf j)] at ho hr
  exact ⟨ho.trans hj.le,hr.trans hj.le⟩

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
