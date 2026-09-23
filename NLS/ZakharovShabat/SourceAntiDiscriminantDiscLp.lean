import NLS.ZakharovShabat.UniformBoundaryCharacteristicDiscLp
import NLS.ZakharovShabat.SourceAntiDiscriminantCandidate
import NLS.ZakharovShabat.UniformCanonicalBoundaryRoots
import NLS.SequenceSpaces.FiniteModification

/-!
# Locally uniform source anti-discriminant disc bounds

Pull back the intrinsic boundary estimates through the actual auxiliary
source potential. Both auxiliary endpoint domains share one source
neighborhood, so their difference has a common ℓᵖ majorant.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The two actual starred source characteristics have uniform free-sine
value and free-cosine derivative majorants on one source neighborhood. -/
theorem exists_uniform_auxiliaryCharacteristic_disc_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        ∃ A : Coeff p, ‖A‖ ≤ K ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
            ‖auxiliaryPeriodOneCharacteristic hp hp1 b ψ z-sin z‖ ≤ ‖A n‖) ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
            ‖deriv (auxiliaryPeriodOneCharacteristic hp hp1 b ψ) z-cos z‖ ≤
              (4/Real.pi)*‖A n‖) := by
  let F := auxiliaryPeriodOneDirichletPotential hp hp1
  obtain ⟨V, hVo, hVc, hVφ, hV0, K, hK, hbound⟩ :=
    exists_uniform_boundaryCharacteristic_disc_majorants hp hp1 (F φ)
  refine ⟨F ⁻¹' V, hVo.preimage F.continuous,
    hVc.linear_preimage (F.restrictScalars ℝ).toLinearMap,
    hVφ, by simpa only [mem_preimage, map_zero] using hV0,
    K, hK, fun ψ hψ b => ?_⟩
  obtain ⟨A, hA, hv, hd⟩ := hbound (F ψ) hψ b
  exact ⟨A, hA, hv, hd⟩

/-- The source anti-discriminant and its spectral derivative have one
locally uniform ℓᵖ majorant throughout the free half-π and quarter-π discs. -/
theorem exists_uniform_sourceAntiDiscriminant_disc_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∃ A : Coeff p, ‖A‖ ≤ K ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
            ‖sourceAntiDiscriminantCandidate hp hp1 ψ z‖ ≤ ‖A n‖) ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
            ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) z‖ ≤
              (4/Real.pi)*‖A n‖) := by
  obtain ⟨U, ho, hc, hφ, h0, K, hK, hbound⟩ :=
    exists_uniform_auxiliaryCharacteristic_disc_majorants hp hp1 φ
  refine ⟨U, ho, hc, hφ, h0, 2*K, by positivity, fun ψ hψ => ?_⟩
  obtain ⟨AN, hAN, hvN, hdN⟩ := hbound ψ hψ .neumann
  obtain ⟨AD, hAD, hvD, hdD⟩ := hbound ψ hψ .dirichlet
  let A : Coeff p := Coeff.magnitude AN + Coeff.magnitude AD
  have hA (n : ℤ) : ‖A n‖ = ‖AN n‖+‖AD n‖ := by
    simp only [A, lp.coeFn_add, Pi.add_apply, Coeff.magnitude_apply, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  refine ⟨A, ?_, ?_, ?_⟩
  · calc
      ‖A‖ ≤ ‖Coeff.magnitude AN‖+‖Coeff.magnitude AD‖ := norm_add_le _ _
      _ = ‖AN‖+‖AD‖ := by rw [Coeff.norm_magnitude, Coeff.norm_magnitude]
      _ ≤ 2*K := by linarith
  · intro n z hz
    have he : sourceAntiDiscriminantCandidate hp hp1 ψ z =
        (auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ z-sin z) -
          (auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ z-sin z) := by
      unfold sourceAntiDiscriminantCandidate
      ring
    rw [he, hA]
    exact (norm_sub_le _ _).trans (add_le_add (hvN n z hz) (hvD n z hz))
  · intro n z hz
    have hderiv : deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) z =
        deriv (auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ) z -
          deriv (auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ) z := by
      change deriv (fun y => auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ y -
        auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ y) z = _
      exact deriv_fun_sub
        ((analyticOnNhd_auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ z
          (mem_univ _)).differentiableAt)
        ((analyticOnNhd_auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ z
          (mem_univ _)).differentiableAt)
    rw [hderiv]
    have he : deriv (auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ) z -
        deriv (auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ) z =
          (deriv (auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ) z-cos z) -
            (deriv (auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ) z-cos z) := by
      ring
    rw [he, hA]
    calc
      ‖(deriv (auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ) z-cos z) -
          (deriv (auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ) z-cos z)‖ ≤
          ‖deriv (auxiliaryPeriodOneCharacteristic hp hp1 .neumann ψ) z-cos z‖ +
            ‖deriv (auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet ψ) z-cos z‖ :=
        norm_sub_le _ _
      _ ≤ (4/Real.pi)*‖AN n‖+(4/Real.pi)*‖AD n‖ :=
        add_le_add (hdN n z hz) (hdD n z hz)
      _ = (4/Real.pi)*(‖AN n‖+‖AD n‖) := by ring

/-- Simultaneous samples in all free quarter-discs have locally uniformly
bounded anti-discriminant and derivative ℓᵖ norms. -/
theorem exists_uniform_sampled_sourceAntiDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ z : ℤ → ℂ,
        (∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) →
          ∃ a b : Coeff p, ‖a‖ ≤ K ∧ ‖b‖ ≤ (4/Real.pi)*K ∧
            (∀ n, a n = sourceAntiDiscriminantCandidate hp hp1 ψ (z n)) ∧
            (∀ n, b n = deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) (z n)) := by
  obtain ⟨U, ho, hc, hφ, h0, K, hK, hbound⟩ :=
    exists_uniform_sourceAntiDiscriminant_disc_majorants hp hp1 φ
  refine ⟨U, ho, hc, hφ, h0, K, hK, fun ψ hψ z hz => ?_⟩
  obtain ⟨A, hA, hv, hd⟩ := hbound ψ hψ
  have hv' (n : ℤ) : ‖sourceAntiDiscriminantCandidate hp hp1 ψ (z n)‖ ≤ ‖A n‖ :=
    hv n (z n) (by linarith [Real.pi_pos, hz n])
  let B : Coeff p := ((4/Real.pi : ℝ) : ℂ) • A
  have hd' (n : ℤ) : ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) (z n)‖ ≤ ‖B n‖ := by
    simpa only [B, lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using hd n (z n) (hz n)
  let a : Coeff p := ⟨_, (lp.memℓp A).mono' hv'⟩
  let b : Coeff p := ⟨_, (lp.memℓp B).mono' hd'⟩
  refine ⟨a, b, (lp.norm_mono (zero_lt_one.trans hp1).ne' hv').trans hA,
    (lp.norm_mono (zero_lt_one.trans hp1).ne' hd').trans ?_, fun _ => rfl, fun _ => rfl⟩
  change ‖((4/Real.pi : ℝ) : ℂ) • A‖ ≤ (4/Real.pi)*K
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

/-- On a common source neighborhood, all sufficiently distant ordinary
Dirichlet roots lie in free quarter-discs, and the anti-discriminant and
its derivative there obey a single uniformly bounded ℓᵖ majorant. -/
theorem exists_uniform_sourceAntiDiscriminant_at_dirichlet_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∃ A : Coeff p, ‖A‖ ≤ K ∧ ∀ n : ℤ, N < n.natAbs →
          ‖sourceAntiDiscriminantCandidate hp hp1 ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)‖ ≤ ‖A n‖ ∧
          ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ)
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)‖ ≤
              (4/Real.pi)*‖A n‖ := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨N, _, V, hVo, hVc, hVφ, hV0, _, _, hroots⟩ :=
    exists_uniform_canonicalBoundaryRoots hp hp1 (F φ)
  obtain ⟨U, hUo, hUc, hUφ, hU0, K, hK, hbound⟩ :=
    exists_uniform_sourceAntiDiscriminant_disc_majorants hp hp1 φ
  refine ⟨N, U ∩ (F ⁻¹' V), hUo.inter (hVo.preimage F.continuous),
    hUc.inter (hVc.linear_preimage (F.restrictScalars ℝ).toLinearMap),
    ⟨hUφ, hVφ⟩, ⟨hU0, by simpa only [mem_preimage, map_zero] using hV0⟩,
    K, hK, fun ψ hψ => ?_⟩
  obtain ⟨A, hA, hv, hd⟩ := hbound ψ hψ.1
  refine ⟨A, hA, fun n hn => ?_⟩
  have hdisc : ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n -
      (Real.pi : ℂ)*n‖ ≤ Real.pi/4 := by
    have h := (hroots (F ψ) hψ.2 .dirichlet).1.distant_spec n hn
    have h' : ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n -
        (Real.pi : ℂ)*n‖ < Real.pi/4 := by
      simpa only [canonicalPeriodOneBoundaryRoots, mem_ball, dist_eq_norm] using h.1
    exact h'.le
  exact ⟨hv n _ (by linarith [Real.pi_pos, hdisc]), hd n _ hdisc⟩

/-- At every source potential, both canonical Dirichlet-root samples belong
to ℓᵖ; the finitely many central values are handled by finite modification. -/
theorem memℓp_sourceAntiDiscriminant_at_dirichletRoots
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Memℓp (fun n => sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)) p ∧
    Memℓp (fun n => deriv (sourceAntiDiscriminantCandidate hp hp1 φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)) p := by
  obtain ⟨N, U, _, _, hφ, _, K, _, hbound⟩ :=
    exists_uniform_sourceAntiDiscriminant_at_dirichlet_tail hp hp1 φ
  obtain ⟨A, _, htail⟩ := hbound φ hφ
  let v : ℤ → ℂ := fun n => sourceAntiDiscriminantCandidate hp hp1 φ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)
  let d : ℤ → ℂ := fun n => deriv (sourceAntiDiscriminantCandidate hp hp1 φ)
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)
  change Memℓp v p ∧ Memℓp d p
  constructor
  · let g : ℤ → ℂ := fun n => if N < n.natAbs then v n else 0
    have hg : Memℓp g p := (lp.memℓp A).mono' (fun n => by
      by_cases hn : N < n.natAbs
      · simpa only [g, if_pos hn] using (htail n hn).1
      · simp only [g, if_neg hn, norm_zero]
        exact norm_nonneg _)
    apply NLS.memℓp_of_eq_outside_finset hg (Finset.Icc (-(N : ℤ)) N)
    intro n hn
    have hn' : N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [g, if_pos hn']
  · let B : Coeff p := ((4/Real.pi : ℝ) : ℂ) • A
    let g : ℤ → ℂ := fun n => if N < n.natAbs then d n else 0
    have hg : Memℓp g p := (lp.memℓp B).mono' (fun n => by
      by_cases hn : N < n.natAbs
      · have hd := (htail n hn).2
        simpa only [g, if_pos hn, B, lp.coeFn_smul, Pi.smul_apply, norm_smul,
          Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using hd
      · simp only [g, if_neg hn, norm_zero]
        exact norm_nonneg _)
    apply NLS.memℓp_of_eq_outside_finset hg (Finset.Icc (-(N : ℤ)) N)
    intro n hn
    have hn' : N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [g, if_pos hn']

end NLS.ZakharovShabat
