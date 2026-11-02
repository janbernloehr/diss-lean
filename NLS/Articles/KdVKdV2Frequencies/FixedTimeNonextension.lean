import NLS.Articles.KdVKdV2Frequencies.SignedMassInsertion
import NLS.Dynamics.FixedTimePhaseObstruction

/-! # Fixed-time nonextension from the KdV2 mass term

This proves the sequence-space obstruction used in Theorem 4.14(v), without
substituting a compact-time obstruction for its fixed-time claim. Two finite
signed approximants converge in the exact subcritical norm, and have masses
differing by pi/(t*20(2n*pi)). The actual spectral correction and agreement of
the physical flow with the displayed endpoint phase remain explicit inputs.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies

/-- The source positive-mode endpoint phase value, with the Hamiltonian sign.
This is used only on data with proved finite mass. -/
def kdv2EndpointModeValue {w : Weight} (n : ℕ) (t : ℝ)
    (correction : SignedCoordinates w 2 → ℝ) (z : SignedCoordinates w 2) : ℂ :=
  Complex.exp (((-t * kdv2FrequencyFromMass n (kdvFiniteMass z) (correction z) : ℝ) : ℂ) *
    Complex.I) * z.val.val (n : ℤ)

/-- For every subcritical signed Sobolev datum with a nonzero positive mode,
no continuous fixed-time mode map can agree on endpoint-regular data with
the KdV2 phase formula and a correction continuous at that datum.

This does not assert construction of the actual KdV2 correction or Birkhoff
map. Specializing sigma=s+1/2 gives the source range -1<s<0. -/
theorem not_continuousAt_kdv2_fixedTime_mode_extension
    (σ : ℝ) (hσ : σ < 1 / 2) (a : SignedCoordinates (Weight.sobolev σ) 2)
    (n : ℕ) (hn : 1 ≤ n) (ha : a.val.val (n : ℤ) ≠ 0) (t : ℝ) (ht : 0 < t)
    (correction : SignedCoordinates (Weight.sobolev σ) 2 → ℝ)
    (hc : ContinuousAt correction a) (Q : SignedCoordinates (Weight.sobolev σ) 2 → ℂ)
    (hQ : ∀ z, HasHalfRegularity z → Q z = kdv2EndpointModeValue n t correction z) :
    ¬ ContinuousAt Q a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let D : ℝ := Real.pi / (t * (20 * (2 * (n : ℝ) * Real.pi)))
  have hD : 0 < D := by dsimp only [D]; positivity
  have hphase : t * (20 * (2 * (n : ℝ) * Real.pi)) * D = Real.pi := by
    dsimp only [D]
    field_simp
  let p (N : ℕ) := signedTruncate (Weight.sobolev σ) N a
  let q (N : ℕ) := massInsertedTruncate (Weight.sobolev σ) N a
    (massInsertionAmplitude D (N + 1))
  have hp : Tendsto p atTop (𝓝 a) := tendsto_signedTruncate (Weight.sobolev σ) a
  have hq : Tendsto q atTop (𝓝 a) := tendsto_massInsertedTruncate σ hσ a D hD.le
  have hpreg (N : ℕ) : HasHalfRegularity (p N) :=
    hasHalfRegularity_signedTruncate (Weight.sobolev σ) N a
  have hqreg (N : ℕ) : HasHalfRegularity (q N) :=
    hasHalfRegularity_massInsertedTruncate (Weight.sobolev σ) N a _
  have hmass (N : ℕ) : kdvFiniteMass (q N) = kdvFiniteMass (p N) + D :=
    kdvFiniteMass_prescribed_insert (Weight.sobolev σ) N a D hD.le
  have hcoord (N : ℕ) (hN : n ≤ N) : (q N).val.val (n : ℤ) = (p N).val.val (n : ℤ) := by
    dsimp only [q, p]
    rw [massInsertedTruncate_pos, if_neg (by omega), add_zero]
  let f (N : ℕ) := kdv2FrequencyFromMass n (kdvFiniteMass (p N)) (correction (p N))
  let g (N : ℕ) := kdv2FrequencyFromMass n (kdvFiniteMass (q N)) (correction (q N))
  have he (N : ℕ) : t * (g N - f N) = Real.pi + t * (correction (q N) - correction (p N)) := by
    dsimp only [g, f, kdv2FrequencyFromMass]
    rw [hmass]
    calc
      _ = t * (20 * (2 * (n : ℝ) * Real.pi)) * D +
          t * (correction (q N) - correction (p N)) := by ring
      _ = _ := by rw [hphase]
  have hgap : Tendsto (fun N => t * (g N - f N)) atTop (𝓝 Real.pi) := by
    have h := (((hc.tendsto.comp hq).sub (hc.tendsto.comp hp)).const_mul t).const_add Real.pi
    simpa only [he, sub_self, mul_zero, add_zero, Function.comp_def] using! h
  intro hcont
  apply Dynamics.not_tendsto_same_limit_of_phase_gap t f g
    (fun N => (p N).val.val (n : ℤ)) (a.val.val (n : ℤ)) ha
    (tendsto_signedTruncate_coefficient (Weight.sobolev σ) a (n : ℤ)) hgap (Q a)
  constructor
  · exact (hcont.tendsto.comp hp).congr' (Eventually.of_forall (fun N => hQ (p N) (hpreg N)))
  · apply (hcont.tendsto.comp hq).congr'
    filter_upwards [eventually_ge_atTop n] with N hN
    change Q (q N) = Complex.exp (((-t * g N : ℝ) : ℂ) * Complex.I) * (p N).val.val (n : ℤ)
    rw [hQ (q N) (hqreg N)]
    change Complex.exp (((-t * g N : ℝ) : ℂ) * Complex.I) * (q N).val.val (n : ℤ) = _
    rw [hcoord N hN]

end NLS.Articles.KdVKdV2Frequencies
