import NLS.Fourier.FourierNLSReferenceInterval
import NLS.Fourier.PeriodOneSmoothSynthesis

/-! # A common local interval for all Sobolev orders

Every finite Sobolev weight present at the initial time persists on the
reference trajectory's whole interval, with a continuous higher-weight
trajectory solving the original equations. All weights give spatially
smooth Fourier synthesis on one common local interval.
-/
noncomputable section
open Set
open scoped ContDiff
namespace NLS.Fourier

/-- Initial Sobolev membership produces a continuous higher-weight lift on
the entire closed reference interval, preserving every original coefficient. -/
theorem IsFourierNLSTrajectoryOn.exists_sobolev_lift
    {v : SpectralWeight} {a b : ℝ} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn v a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b) (s : ℝ) (hs : 0 ≤ s)
    (hinit : Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z initial).val n) 1) :
    ∃ u : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1,
      IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) a b u ∧
      ∀ time ∈ Icc a b, ∀ n : ℤ, (u time).val n = (z time).val n := by
  let u₀ : WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1 := ⟨(z initial).val,by
    change Memℓp (fun n => (SpectralWeight.sobolev s hs n : ℂ)*(z initial).val n) 1
    simpa only [SpectralWeight.sobolev_apply] using hinit⟩
  obtain ⟨u,_,hu,he⟩ := exists_sobolev_fourierNLS_on_reference_interval s hs v a b initial hi
    z hz u₀ (fun _ => rfl)
  exact ⟨u,hu,he⟩

/-- Sobolev membership propagates to every time in the same closed interval. -/
theorem IsFourierNLSTrajectoryOn.mem_sobolev_at
    {v : SpectralWeight} {a b : ℝ} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn v a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b) (s : ℝ) (hs : 0 ≤ s)
    (hinit : Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z initial).val n) 1)
    (time : ℝ) (ht : time ∈ Icc a b) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z time).val n) 1 := by
  obtain ⟨u,_,he⟩ := hz.exists_sobolev_lift initial hi s hs hinit
  have hm := (u time).property
  change Memℓp (fun n => (SpectralWeight.sobolev s hs n : ℂ)*(u time).val n) 1 at hm
  simpa only [SpectralWeight.sobolev_apply,he time ht] using hm

/-- All initial Sobolev weights give an everywhere smooth spatial representative
at every time of the original reference interval, including its endpoints. -/
theorem IsFourierNLSTrajectoryOn.contDiff_synthesis_of_all_sobolev
    {v : SpectralWeight} {a b : ℝ} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn v a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z initial).val n) 1)
    (time : ℝ) (ht : time ∈ Icc a b) :
    ContDiff ℝ ∞ (periodOneSynthesis (v.toCoeff (z time))) := by
  apply contDiff_periodOneSynthesis_of_all_sobolev (p := 1) (by simp)
  intro s hs
  simpa only [SpectralWeight.toCoeff_apply] using hz.mem_sobolev_at initial hi s hs (hall s hs) time ht

/-- Initial data in every Sobolev weight have one positive local interval
supporting all higher-weight trajectories and spatially smooth synthesis.
The time interval is chosen once from the reference space, before the order. -/
theorem exists_local_fourierNLS_all_sobolev (w : SpectralWeight)
    (u₀ : WeightedCoeff w.toWeight 1)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*u₀.val n) 1) :
    ∃ T > 0, ∃ z : ℝ → WeightedCoeff w.toWeight 1,
      z 0 = u₀ ∧ IsFourierNLSTrajectoryOn w (-T) T z ∧
      (∀ s : ℝ, ∀ hs : 0 ≤ s,
        ∃ u : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1,
          IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) (-T) T u ∧
          ∀ time ∈ Icc (-T) T, ∀ n : ℤ, (u time).val n = (z time).val n) ∧
      ∀ time ∈ Icc (-T) T, ContDiff ℝ ∞ (periodOneSynthesis (w.toCoeff (z time))) := by
  obtain ⟨T,hT,z,hz0,hz⟩ := exists_local_fourierNLSTrajectory w u₀
  have hi : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith,hT.le⟩
  have hinit : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z 0).val n) 1 := by
    simpa only [hz0] using hall
  exact ⟨T,hT,z,hz0,hz,fun s hs => hz.exists_sobolev_lift 0 hi s hs (hinit s hs),
    hz.contDiff_synthesis_of_all_sobolev 0 hi hinit⟩

end NLS.Fourier
