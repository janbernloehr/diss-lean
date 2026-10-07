import NLS.ZakharovShabat.SourceFiniteGapUniformBound
import NLS.ZakharovShabat.ClassicalNLSStability

/-! # Finite-gap approximation of arbitrary classical NLS trajectories

H¹ convergence of actual finite-gap initial data supplies the required
uniform amplitude bound through conserved mass and energy. The PDE stability
estimate then identifies the physical L² limit on every compact time interval
with any classical solution having the prescribed H¹ initial representative.
-/
noncomputable section
open Set Filter Topology MeasureTheory NLS.Fourier
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Actual H¹-convergent finite-gap approximations converge to an arbitrary
classical solution, uniformly in time in physical L². No common bound or
finite-gap hypothesis on the limiting classical initial data is assumed. -/
theorem tendstoUniformlyOn_finiteGap_classicalNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    {ι : Type*} {l : Filter ι} (a : realTypeSobolevSourceLocus)
    (b : ι → realTypeSobolevSourceLocus) (hf : ∀ j, b j ∈ sourceSobolevFiniteGapLocus)
    (hb : Tendsto b l (𝓝 a)) (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalNLSTrajectory u) (hinit : u 0 = periodOneSobolevSynthesis a.val.1) (T : ℝ) :
    TendstoUniformlyOn (fun j time => ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
      (A.hamiltonianOrdinaryContinuousFlow D ⟨sobolevSourceInclusion (b j).val,(b j).property⟩ (hf j) time))
      (fun time => ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time)) l (Icc (-T) T) := by
  let v := fun j => A.hamiltonianOrdinaryContinuousFlow D
    ⟨sobolevSourceInclusion (b j).val,(b j).property⟩ (hf j)
  obtain ⟨M,hM,hbound⟩ := A.exists_eventual_uniform_finiteGap_bound D a b hf hb
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hu.time_differentiable.continuous.continuousOn (s := Icc (-T) T))
  apply hu.tendstoUniformlyOn_toLp v
    (fun j => A.isClassicalNLSTrajectory_hamiltonianOrdinaryContinuousFlow hs D _ (hf j))
    T (max M R) (hM.le.trans (le_max_left _ _)) (fun r hr => (hR r hr).trans (le_max_right _ _))
  · filter_upwards [hbound] with j hj
    intro r _
    exact (hj r).1.trans (le_max_left _ _)
  · have hz (j : ι) : v j 0 = periodOneSobolevSynthesis (b j).val.1 := by
      simp only [v,hamiltonianOrdinaryContinuousFlow,hamiltonianOrdinarySourceFlow_zero]
      exact congrArg (fun c : ScalarDomain 2 × ScalarDomain 2 => periodOneSobolevSynthesis c.1)
        (sourceFiniteGapSobolevPair_sobolevSource (b j) (hf j))
    simp only [hz,hinit]
    exact ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).continuous.comp
      (periodOneSobolevSynthesis.continuous.comp (continuous_fst.comp continuous_subtype_val))).continuousAt.tendsto.comp hb

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
