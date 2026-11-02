import NLS.Dynamics.ActionDependentWeightedPhaseFlow

/-! # Signed real Birkhoff coordinates for the frequency-flow interface

The source uses one sequence indexed by ℤ with zero coordinate zero and
`z (-n) = conj (z n)`. It does not use the dNLS pair of independent ℤ-sequences.
The frequency sign below agrees with the Hamiltonian equations on PDF p. 3.
Actual KdV/KdV2 frequencies and their physical identification remain to be proved.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.Articles.KdVKdV2Frequencies
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real mean-zero signed sequence locus from source equations (4) and (22). -/
def IsSignedReal {w : Weight} (a : WeightedCoeff w p) : Prop :=
  a.val 0 = 0 ∧ ∀ n : ℤ, a.val (-n) = conj (a.val n)

omit [Fact (1 ≤ p)] in
theorem IsSignedReal.add {w : Weight} {a b : WeightedCoeff w p}
    (ha : IsSignedReal a) (hb : IsSignedReal b) : IsSignedReal (a + b) := by
  constructor
  · simp only [WeightedCoeff.add_val, ha.1, hb.1, add_zero]
  · intro n
    simp only [WeightedCoeff.add_val, ha.2 n, hb.2 n, map_add]

/-- The native weighted norm topology restricted to real signed coordinates. -/
abbrev SignedCoordinates (w : Weight) (p : ℝ≥0∞) :=
  {a : WeightedCoeff w p // IsSignedReal a}

/-- Positive modes have Hamiltonian sign `-i ω_n`; negative modes have `+i ω_n`.
The value of the input at natural index zero is deliberately unused. -/
def signedHamiltonianFrequency (ω : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 < n then -ω n.natAbs else if n < 0 then ω n.natAbs else 0

@[simp] theorem signedHamiltonianFrequency_zero (ω : ℕ → ℝ) :
    signedHamiltonianFrequency ω 0 = 0 := by simp [signedHamiltonianFrequency]

/-- The signed frequency is odd, including the zero mode. -/
theorem signedHamiltonianFrequency_neg (ω : ℕ → ℝ) (n : ℤ) :
    signedHamiltonianFrequency ω (-n) = -signedHamiltonianFrequency ω n := by
  simp only [signedHamiltonianFrequency, Int.natAbs_neg]
  split_ifs <;> simp_all
  all_goals omega

/-- Odd phase frequencies preserve both the zero mode and Fourier reality. -/
theorem isSignedReal_phaseFlow (w : Weight) (ω : ℤ → ℝ)
    (hω : ∀ n, ω (-n) = -ω n) (t : ℝ) (a : WeightedCoeff w p)
    (ha : IsSignedReal a) : IsSignedReal (WeightedCoeff.phaseFlow w ω t a) := by
  constructor
  · simp only [WeightedCoeff.phaseFlow_apply, ha.1, mul_zero]
  · intro n
    rw [WeightedCoeff.phaseFlow_apply, WeightedCoeff.phaseFlow_apply,
      ha.2 n, map_mul, ← Complex.exp_conj, hω n]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

/-- Action-dependent evolution on precisely the signed real sequence locus. -/
def coordinateFlow (w : Weight) (Ω : (ℤ → ℝ) → ℕ → ℝ)
    (t : ℝ) (a : SignedCoordinates w p) : SignedCoordinates w p :=
  ⟨WeightedCoeff.actionPhaseFlow w (fun A => signedHamiltonianFrequency (Ω A)) t a.val,
    isSignedReal_phaseFlow w _ (signedHamiltonianFrequency_neg _) t a.val a.property⟩

/-- Squared amplitudes are conserved on the signed locus. -/
@[simp] theorem coordinateFlow_actions (w : Weight) (Ω : (ℤ → ℝ) → ℕ → ℝ)
    (t : ℝ) (a : SignedCoordinates w p) :
    WeightedCoeff.squaredAmplitudes (coordinateFlow w Ω t a).val =
      WeightedCoeff.squaredAmplitudes a.val := by
  simpa only [coordinateFlow] using! WeightedCoeff.squaredAmplitudes_actionPhaseFlow
    (p := p) w (fun A => signedHamiltonianFrequency (Ω A)) t a.val

/-- Initial data are attained exactly. -/
@[simp] theorem coordinateFlow_zero (w : Weight) (Ω : (ℤ → ℝ) → ℕ → ℝ)
    (a : SignedCoordinates w p) : coordinateFlow w Ω 0 a = a := by
  apply Subtype.ext
  simpa only [coordinateFlow] using! WeightedCoeff.actionPhaseFlow_zero
    (p := p) w (fun A => signedHamiltonianFrequency (Ω A)) a.val

/-- The nonlinear group property uses the same conserved action sequence. -/
theorem coordinateFlow_add (w : Weight) (Ω : (ℤ → ℝ) → ℕ → ℝ)
    (t u : ℝ) (a : SignedCoordinates w p) :
    coordinateFlow w Ω t (coordinateFlow w Ω u a) = coordinateFlow w Ω (t + u) a := by
  apply Subtype.ext
  simpa only [coordinateFlow] using! WeightedCoeff.actionPhaseFlow_add
    (p := p) w (fun A => signedHamiltonianFrequency (Ω A)) t u a.val

omit [Fact (1 ≤ p)] in
/-- The true product `z_n z_(-n)` agrees with the nonnegative real action. -/
theorem signed_action_eq_squaredAmplitude (w : Weight) (a : SignedCoordinates w p)
    (n : ℤ) : a.val.val n * a.val.val (-n) =
      (WeightedCoeff.squaredAmplitudes a.val n : ℂ) := by
  rw [a.property.2 n]
  simp only [WeightedCoeff.squaredAmplitudes, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]
  ring

/-- At a fixed initial datum the signed orbit is continuous in its weighted norm. -/
theorem continuous_coordinateFlow_orbit (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℕ → ℝ) (a : SignedCoordinates w p) :
    Continuous (fun t : ℝ => coordinateFlow w Ω t a) := by
  apply Continuous.subtype_mk
  exact WeightedCoeff.continuous_actionPhaseFlow_orbit w hp _ a.val

/-- Coordinatewise continuity of the positive-mode frequencies suffices for
joint continuity on the signed locus, in its native weighted topology. -/
theorem continuous_coordinateFlow (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℕ → ℝ)
    (hΩ : ∀ n, Continuous (fun a : SignedCoordinates w p =>
      Ω (WeightedCoeff.squaredAmplitudes a.val) n)) :
    Continuous (fun x : ℝ × SignedCoordinates w p => coordinateFlow w Ω x.1 x.2) := by
  have hω (n : ℤ) : Continuous (fun a : SignedCoordinates w p =>
      signedHamiltonianFrequency (Ω (WeightedCoeff.squaredAmplitudes a.val)) n) := by
    unfold signedHamiltonianFrequency
    split_ifs
    · exact (hΩ n.natAbs).neg
    · exact hΩ n.natAbs
    · exact continuous_const
  apply Continuous.subtype_mk
  exact WeightedCoeff.continuous_phaseFlow_family (p := p) w hp
    (fun a : SignedCoordinates w p =>
      signedHamiltonianFrequency (Ω (WeightedCoeff.squaredAmplitudes a.val)))
    Subtype.val hω continuous_subtype_val

/-- Compact-time trajectories of signed coordinates. -/
def coordinateTrajectory (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℕ → ℝ) (T : ℝ) (a : SignedCoordinates w p) :
    C(Icc (-T) T, SignedCoordinates w p) where
  toFun τ := coordinateFlow w Ω τ.val a
  continuous_toFun := (continuous_coordinateFlow_orbit w hp Ω a).comp continuous_subtype_val

/-- Continuous dependence in the uniform compact-time topology on the signed locus. -/
theorem continuous_coordinateTrajectory (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℕ → ℝ)
    (hΩ : ∀ n, Continuous (fun a : SignedCoordinates w p =>
      Ω (WeightedCoeff.squaredAmplitudes a.val) n))
    (T : ℝ) : Continuous (coordinateTrajectory w hp Ω T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun x : SignedCoordinates w p × Icc (-T) T =>
    coordinateFlow w Ω x.2.val x.1)
  have hi : Continuous (fun x : SignedCoordinates w p × Icc (-T) T => (x.2.val, x.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  simpa only [Function.comp_def] using! (continuous_coordinateFlow w hp Ω hΩ).comp hi

/-- Every time slice is a homeomorphism of the signed real locus. -/
def coordinateHomeomorph (w : Weight) (hp : p ≠ ⊤)
    (Ω : (ℤ → ℝ) → ℕ → ℝ)
    (hΩ : ∀ n, Continuous (fun a : SignedCoordinates w p =>
      Ω (WeightedCoeff.squaredAmplitudes a.val) n))
    (t : ℝ) : SignedCoordinates w p ≃ₜ SignedCoordinates w p where
  toFun := coordinateFlow w Ω t
  invFun := coordinateFlow w Ω (-t)
  left_inv a := by simp only [coordinateFlow_add, neg_add_cancel, coordinateFlow_zero]
  right_inv a := by simp only [coordinateFlow_add, add_neg_cancel, coordinateFlow_zero]
  continuous_toFun := by
    have hi : Continuous (fun a : SignedCoordinates w p => (t, a)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! (continuous_coordinateFlow w hp Ω hΩ).comp hi
  continuous_invFun := by
    have hi : Continuous (fun a : SignedCoordinates w p => (-t, a)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! (continuous_coordinateFlow w hp Ω hΩ).comp hi

end NLS.Articles.KdVKdV2Frequencies
