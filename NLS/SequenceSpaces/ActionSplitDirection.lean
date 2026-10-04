import NLS.SequenceSpaces.TailSquareDescentCoordinateAnalytic
import NLS.SequenceSpaces.ComplexActionStationarity

/-! # Differential of mixed squares along an action rotation

A coordinate rotation preserves the sum of the two squares. Under the
mixed-square map its tangent is a scalar multiple of the direction that
transfers one unit from the first square to the second square.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Transfer a unit between two coordinates without changing their sum. -/
def actionSplitDirection (q : ℝ≥0∞) (k : ℤ) : Coeff q × Coeff q :=
  (-lp.single (E := fun _ : ℤ => ℂ) q k 1,lp.single (E := fun _ : ℤ => ℂ) q k 1)

variable [p.HolderTriple p q]

/-- A rotation tangent changes a squared tail pair by a linear action-splitting
term and an explicit quadratic error. -/
theorem pairMixedSquare_rotationLine (S : Finset ℤ) (k : ℤ) (hk : k ∉ S)
    (z : Coeff p × Coeff p) (t : ℂ) :
    pairMixedSquare (q := q) S (z+t • actionRotationVectorCLM p k z) =
      pairMixedSquare S z + (2*z.1 k*z.2 k*t) • actionSplitDirection q k +
        t^2 • (lp.single (E := fun _ : ℤ => ℂ) q k (z.2 k^2),lp.single (E := fun _ : ℤ => ℂ) q k (z.1 k^2)) := by
  classical
  rw [actionRotationVectorCLM_apply]
  apply Prod.ext
  · ext n
    change mixedSquare S (z.1+t • (-lp.single (E := fun _ : ℤ => ℂ) p k (z.2 k))) n =
      mixedSquare S z.1 n+(2*z.1 k*z.2 k*t)*(-(lp.single (E := fun _ : ℤ => ℂ) q k 1) n)+t^2*(lp.single (E := fun _ : ℤ => ℂ) q k (z.2 k^2)) n
    rw [mixedSquare_apply,mixedSquare_apply]
    change (if n ∈ S then z.1 n+t*(-(lp.single (E := fun _ : ℤ => ℂ) p k (z.2 k)) n)
      else (z.1 n+t*(-(lp.single (E := fun _ : ℤ => ℂ) p k (z.2 k)) n))^2) = _
    by_cases hn : n = k
    · subst n
      simp only [if_neg hk,lp.single_apply,Pi.single_eq_same]
      ring
    · simp [lp.single_apply,hn]
  · ext n
    change mixedSquare S (z.2+t • lp.single (E := fun _ : ℤ => ℂ) p k (z.1 k)) n =
      mixedSquare S z.2 n+(2*z.1 k*z.2 k*t)*(lp.single (E := fun _ : ℤ => ℂ) q k 1) n+t^2*(lp.single (E := fun _ : ℤ => ℂ) q k (z.1 k^2)) n
    rw [mixedSquare_apply,mixedSquare_apply]
    change (if n ∈ S then z.2 n+t*(lp.single (E := fun _ : ℤ => ℂ) p k (z.1 k)) n
      else (z.2 n+t*(lp.single (E := fun _ : ℤ => ℂ) p k (z.1 k)) n)^2) = _
    by_cases hn : n = k
    · subst n
      simp only [if_neg hk,lp.single_apply,Pi.single_eq_same]
      ring
    · simp [lp.single_apply,hn]

/-- The mixed-square image of the rotation line has the expected tangent,
including when one or both coordinates vanish. -/
theorem hasDerivAt_pairMixedSquare_rotationLine (S : Finset ℤ) (k : ℤ) (hk : k ∉ S)
    (z : Coeff p × Coeff p) :
    HasDerivAt (fun t : ℂ => pairMixedSquare (q := q) S (z+t • actionRotationVectorCLM p k z))
      ((2*z.1 k*z.2 k) • actionSplitDirection q k) 0 := by
  have hlin := ((hasDerivAt_id (0 : ℂ)).const_mul (2*z.1 k*z.2 k)).smul_const (actionSplitDirection q k)
  have hquad := ((hasDerivAt_id (0 : ℂ)).pow 2).smul_const
    ((lp.single (E := fun _ : ℤ => ℂ) q k (z.2 k^2),lp.single (E := fun _ : ℤ => ℂ) q k (z.1 k^2)) : Coeff q × Coeff q)
  have he : (fun t : ℂ => pairMixedSquare (q := q) S (z+t • actionRotationVectorCLM p k z)) =
      (fun t : ℂ => pairMixedSquare S z+(2*z.1 k*z.2 k*t) • actionSplitDirection q k+
        t^2 • (lp.single (E := fun _ : ℤ => ℂ) q k (z.2 k^2),lp.single (E := fun _ : ℤ => ℂ) q k (z.1 k^2))) :=
    funext (pairMixedSquare_rotationLine S k hk z)
  rw [he]
  simpa [Pi.add_def] using (hlin.const_add (pairMixedSquare (q := q) S z)).add hquad

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The rotation identity for a lifted function gives the weighted
splitting identity for any differentiable mixed-coordinate descent. -/
theorem smul_fderiv_actionSplit_eq_zero_of_recovery
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (G : (Coeff q × Coeff q) → F)
    (U : Set (Coeff p × Coeff p)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hG : DifferentiableOn ℂ G (pairMixedSquare S '' U))
    (himage : IsOpen (pairMixedSquare (q := q) S '' U))
    (he : ∀ z ∈ U, G (pairMixedSquare S z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ U) (k : ℤ) (hk : k ∉ S)
    (hrot : fderiv ℂ f z (actionRotationVectorCLM p k z) = 0) :
    (2*z.1 k*z.2 k) • (fderiv ℂ G (pairMixedSquare S z) (actionSplitDirection q k)) = 0 := by
  let γ : ℂ → Coeff p × Coeff p := fun t => z+t • actionRotationVectorCLM p k z
  have hγ0 : γ 0 = z := by simp [γ]
  have hγ : HasDerivAt γ (actionRotationVectorCLM p k z) 0 := by
    simpa [γ] using ((hasDerivAt_id (0 : ℂ)).smul_const (actionRotationVectorCLM p k z)).const_add z
  have hdf : HasFDerivAt f (fderiv ℂ f z) (γ 0) := by
    rw [hγ0]
    exact ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hfc := hdf.comp_hasDerivAt (f := γ) 0 hγ
  rw [hrot] at hfc
  have hzQ : pairMixedSquare (q := q) S z ∈ pairMixedSquare S '' U := ⟨z,hz,rfl⟩
  have hgd := ((hG _ hzQ).differentiableAt (himage.mem_nhds hzQ)).hasFDerivAt
  have hgd' : HasFDerivAt G (fderiv ℂ G (pairMixedSquare S z))
      (pairMixedSquare (q := q) S (z+(0 : ℂ) • actionRotationVectorCLM p k z)) := by simpa using hgd
  have hgc := hgd'.comp_hasDerivAt
    (f := fun t : ℂ => pairMixedSquare (q := q) S (z+t • actionRotationVectorCLM p k z)) 0
    (hasDerivAt_pairMixedSquare_rotationLine S k hk z)
  have heq : (fun t => f (γ t)) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => G (pairMixedSquare S (γ t))) := by
    have hstay : ∀ᶠ t in 𝓝 (0 : ℂ), γ t ∈ U :=
      hγ.continuousAt (by simpa only [hγ0] using hU.mem_nhds hz)
    filter_upwards [hstay] with t ht
    exact (he (γ t) ht).symm
  have hu := (hgc.congr_of_eventuallyEq heq).unique hfc
  simpa only [map_smul] using hu

end NLS.Coeff
