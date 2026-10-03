import NLS.ZakharovShabat.SourceMidpointGradientContour

/-! # Uniform distant contours for the actual midpoint derivative

Disjoint open isolating discs separate each closed disc from all the
other periodic segments. Thus one source neighborhood and one cutoff
support the quarter-pi midpoint contour formula at every distant index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The closure of an isolating disc avoids every unselected periodic segment. -/
theorem closure_sourceIsolatingDisc_subset_omittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆ sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j → Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
      (sourceIsolatingDisc hp hp1 φ N ε j)) (n : ℤ) :
    closure (sourceIsolatingDisc hp hp1 φ N ε n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  intro z hz m hmn hm
  have hopen : IsOpen (sourceIsolatingDisc hp hp1 φ N ε m) := by
    unfold sourceIsolatingDisc sourceClusterDisc refinedResonantDisk
    split <;> exact isOpen_ball
  exact Set.disjoint_left.mp ((hdisjoint n m hmn.symm).closure_left hopen) hz
    (sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε m (hcluster m) hm)

/-- Enclosed endpoints and avoidance of all other cuts exclude zeros of the
actual periodic characteristic function on the boundary circle. -/
theorem canonicalDiscriminant_sq_sub_four_ne_zero_on_isolating_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (c : ℂ) (r : ℝ)
    (ha : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r)
    (hb : canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r)
    (hisolate : closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (z : ℂ) (hz : z ∈ sphere c r) :
    (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4 ≠ 0 := by
  rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n z]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz ha).symm))
    (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hb).symm))
    (canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain hp hp1 ψ n z
      (hisolate (sphere_subset_closedBall hz)))

/-- Around every real source, one cutoff and one open neighborhood support
all distant quarter-pi midpoint contours, without supplied isolation premises. -/
theorem exists_local_source_midpoint_gradient_tail_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : φ ∈ realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∃ N : ℕ,
      ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
      (∀ z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4),
        (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4 ≠ 0) ∧
      ∀ h : CoeffPair p,
      (fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ) h =
      -(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C((Real.pi : ℂ)*n,Real.pi/4),
        canonicalDiscriminant hp (periodOnePotential ψ) z*
          ((fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h)/
          ((canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4)) := by
  obtain ⟨W,hW,hWreal,hformula⟩ := exists_global_source_midpoint_gradient_contour hp hp1
  obtain ⟨N,ε,_,_,V,hV,hφV,hcluster,hdisjoint⟩ :=
    exists_local_source_pairwise_disjoint_isolating_discs hp hp1 φ hφ
  refine ⟨V ∩ W,hV.inter hW,⟨hφV,hWreal hφ⟩,N,?_⟩
  intro ψ hψ n hn
  have hdisc : sourceIsolatingDisc hp hp1 φ N ε n = ball ((Real.pi : ℂ)*n) (Real.pi/4) := by
    simp [sourceIsolatingDisc,refinedResonantDisk,not_le.mpr hn]
  have ha := hcluster ψ hψ.1 n (Or.inl rfl)
  have hb := hcluster ψ hψ.1 n (Or.inr (Or.inl rfl))
  rw [hdisc] at ha hb
  have hisolate := closure_sourceIsolatingDisc_subset_omittedDomain hp hp1 φ ψ N ε
    (hcluster ψ hψ.1) hdisjoint n
  rw [hdisc,closure_ball _ (by positivity : (Real.pi/4 : ℝ) ≠ 0)] at hisolate
  exact ⟨canonicalDiscriminant_sq_sub_four_ne_zero_on_isolating_circle hp hp1 ψ n _ _ ha hb hisolate,
    hformula ψ hψ.2 n _ _ (by positivity) ha hb hisolate⟩

end NLS.ZakharovShabat
