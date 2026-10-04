import NLS.ZakharovShabat.SourceAbelianCauchyNormalization

/-! # Exactly normalized complex-source abelian disc continuations

The Cauchy primitive with its now determined constant agrees with every
old collar value. It is jointly analytic off the moving cut and has
endpoint value i (n-j) pi at both ends of the selected gap j.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianCauchyChart
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {j : ℤ}

/-- The actual index normalization, with the selected gap's endpoint
 constant derived from the real-source primitive. -/
def primitive (D : SourceAbelianCauchyChart hp hp1 j) (n : ℤ) (t : ℂ × CoeffPair p) : ℂ :=
  sourceAbelianCauchyPrimitive hp hp1 j D.center D.radius t-I*(Real.pi : ℂ)*j+I*(Real.pi : ℂ)*n

theorem primitive_analytic (D : SourceAbelianCauchyChart hp hp1 j) (n : ℤ) :
    AnalyticOnNhd ℂ (D.primitive n)
      {t | t.1 ∈ ball D.center D.radius ∧ t.2 ∈ D.sources ∧ t.1 ∉ sourcePeriodicSegment hp hp1 t.2 j} := by
  intro t ht
  exact ((D.root_analytic t ht.2).mul (D.quotient_analytic t ⟨ht.1,ht.2.1⟩)).sub analyticAt_const |>.add analyticAt_const

theorem primitive_derivative (D : SourceAbelianCauchyChart hp hp1 j) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) (z : ℂ)
    (hz : z ∈ ball D.center D.radius \ sourcePeriodicSegment hp hp1 ψ j) :
    HasDerivAt (fun w => D.primitive n (w,ψ))
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z :=
  ((D.primitive_hasDerivAt ψ hψ z hz).sub_const _).add_const _

/-- Both ordered endpoints have exactly the prescribed value, including
 when their labels coincide at a collapsed gap. -/
theorem primitive_endpoint_limit (D : SourceAbelianCauchyChart hp hp1 j) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    Tendsto (fun z => D.primitive n (z,ψ))
      (𝓝[ball D.center D.radius \ sourcePeriodicSegment hp hp1 ψ j] a) (𝓝 (I*(Real.pi : ℂ)*(n-j))) := by
  have h := ((sourceAbelianCauchyPrimitive_endpoint_limit hp hp1 ψ j D.center D.radius
    (D.segment_subset_outer ψ hψ) (D.quotient_slice_analytic ψ hψ) a ha).sub_const (I*(Real.pi : ℂ)*j)).add_const (I*(Real.pi : ℂ)*n)
  have he : (0:ℂ)-I*(Real.pi : ℂ)*j+I*(Real.pi : ℂ)*n = I*(Real.pi : ℂ)*(n-j) := by ring
  simpa only [primitive,he] using! h

theorem primitive_eq_zeroIndex_add (D : SourceAbelianCauchyChart hp hp1 j) (n : ℤ) (t : ℂ × CoeffPair p) :
    D.primitive n t = D.primitive 0 t+I*(Real.pi : ℂ)*n := by simp only [primitive,Int.cast_zero,mul_zero,add_zero]

/-- Once the source offset is fixed, the Cauchy continuation retains
 every existing collar value, not merely the value at its anchor. -/
theorem primitive_eq_joint_on_collar (D : SourceAbelianCauchyChart hp hp1 j)
    (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) (hnorm : D.offset ψ = -I*(Real.pi : ℂ)*j) (n : ℤ) :
    EqOn (fun z => D.primitive n (z,ψ)) (fun z => sourceAbelianJointPrimitive hp hp1 n (z,ψ))
      (ball D.center D.radius \ closedBall D.center D.inner) := by
  have hcollar (z : ℂ) (hz : z ∈ ball D.center D.radius \ closedBall D.center D.inner) :
      (z,ψ) ∈ sourceAbelianJointDomain hp hp1 :=
    D.collar_joint ψ hψ z ⟨ball_subset_closedBall hz.1,fun h => hz.2 (ball_subset_closedBall h)⟩
  obtain ⟨F,heq,_,hF⟩ := exists_sourceAbelian_complexDisc_from_annulus hp hp1 ψ j D.center D.inner D.radius
    D.inner_pos.le D.inner_lt (D.segment_subset ψ hψ) (D.avoids_other ψ hψ)
    (fun z => sourceAbelianJointPrimitive hp hp1 n (z,ψ)) (by
      intro z hz
      have hd : HasDerivAt (fun w : ℂ => sourceAbelianJointPrimitive hp hp1 n (w,ψ))
          (deriv (fun w : ℂ => sourceAbelianJointPrimitive hp hp1 n (w,ψ)) z) z := by
        simpa only using! ((sourceAbelianJointPrimitive_analytic hp hp1 n (z,ψ) (hcollar z hz)).comp
          (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
      rwa [sourceAbelianJointPrimitive_spectral_deriv hp hp1 n z ψ (hcollar z hz)] at hd)
  have hmatch := sourceAbelian_complexDisc_unique hp hp1 ψ j D.center D.radius (D.segment_subset_outer ψ hψ)
    (fun z => D.primitive n (z,ψ)) F (D.primitive_derivative n ψ hψ) hF D.anchor
    ⟨D.anchor_mem.1,D.anchor_off_segment ψ hψ⟩ (by
      rw [heq D.anchor_mem]
      change D.primitive n (D.anchor,ψ) = sourceAbelianJointPrimitive hp hp1 n (D.anchor,ψ)
      rw [sourceAbelianJointPrimitive_eq_zeroIndex_add hp hp1 n (D.anchor,ψ) (D.anchor_joint ψ hψ)]
      dsimp only [primitive,offset] at *
      linear_combination -hnorm)
  intro z hz
  exact (hmatch ⟨hz.1,fun hs => hz.2 (ball_subset_closedBall (D.segment_subset ψ hψ hs))⟩).trans (heq hz)

/-- The same collar agreement holds with the enlarged joint primitive. -/
theorem primitive_eq_enlarged_on_collar (D : SourceAbelianCauchyChart hp hp1 j)
    (W : Set (CoeffPair p)) (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) (hnorm : D.offset ψ = -I*(Real.pi : ℂ)*j) (n : ℤ) :
    EqOn (fun z => D.primitive n (z,ψ)) (fun z => sourceAbelianEnlargedPrimitive hp hp1 W n (z,ψ))
      (ball D.center D.radius \ closedBall D.center D.inner) := by
  apply sourceAbelian_complexDisc_eq_enlarged_on_collar hp hp1 W hD hM ψ n D.center D.inner D.radius _
    (fun z hz => D.collar_joint ψ hψ z ⟨ball_subset_closedBall hz.1,fun h => hz.2 (ball_subset_closedBall h)⟩)
  exact D.primitive_eq_joint_on_collar ψ hψ hnorm n

/-- The continued function agrees throughout each real cut disc with
 the previously normalized actual abelian primitive. -/
theorem primitive_eq_real (D : SourceAbelianCauchyChart hp hp1 j) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ D.sources) (n : ℤ) :
    EqOn (fun z => D.primitive n (z,φ.val))
      (fun z => sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n)
      (ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ.val j) :=
  sourceAbelian_complexDisc_eq_real hp hp1 φ j n D.center D.radius (D.segment_subset_outer φ.val hφ)
    (D.avoids_other φ.val hφ) _ (D.primitive_derivative n φ.val hφ) D.anchor
    ⟨D.anchor_mem.1,D.anchor_off_segment φ.val hφ⟩
    (D.primitive_eq_joint_on_collar φ.val hφ (D.offset_eq_of_real φ hφ) n D.anchor_mem)

end NLS.ZakharovShabat.SourceAbelianCauchyChart
