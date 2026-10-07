import NLS.Dynamics.UnboundedPhaseObstruction
import Mathlib.Topology.ContinuousMap.Star

/-! # Phase obstruction with the Hamiltonian time orientation

Conjugating the trajectories transfers the unbounded-frequency obstruction
to the negative exponential sign, on the same forward interval `[0,T]`.
-/
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate
namespace NLS.Dynamics

/-- Negative phase rotation is also incompatible with uniform convergence
on any positive time interval when the limiting amplitude is nonzero. -/
theorem not_tendsto_hamiltonian_phase_trajectories {ι : Type*} {l : Filter ι} [NeBot l]
    (T : ℝ) (hT : 0 < T) (freq : ι → ℝ) (amp : ι → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hfreq : Tendsto freq l atTop) (hamp : Tendsto amp l (𝓝 a))
    (g : ι → C(Icc (0 : ℝ) T,ℂ))
    (he : ∀ j (time : Icc (0 : ℝ) T),
      g j time = Complex.exp (((-time.val*freq j : ℝ) : ℂ)*Complex.I)*amp j)
    (G : C(Icc (0 : ℝ) T,ℂ)) : ¬ Tendsto g l (𝓝 G) := by
  intro hg
  apply not_tendsto_phase_trajectories T hT freq (fun j => conj (amp j)) (conj a)
    (by simpa using ha) hfreq hamp.star (fun j => star (g j)) ?_ (star G) hg.star
  intro j time
  change conj (g j time) = _
  rw [he,map_mul,← Complex.exp_conj]
  congr 2
  simp only [map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

end NLS.Dynamics
