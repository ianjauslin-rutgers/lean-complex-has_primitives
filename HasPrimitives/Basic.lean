import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

import Mathlib.Tactic.LibrarySearch

open Complex Topology

set_option autoImplicit false

-- From V. Beffara https://github.com/vbeffara/RMT4
def hasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

/-- The wedge integral from z to w of a function f -/
noncomputable def WedgeInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))

--example (x y z : ℝ ) : x • y  - x •  z = x • (y - z) := by exact (smul_sub x y z).symm

/-- diff of wedges -/
lemma diff_of_wedges {c : ℂ} {r : ℝ} (h0 : 0 < r) {z : ℂ} (hz : z ∈ Metric.ball c r)
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∀ᶠ h in 𝓝 0,
      WedgeInt c (z+h) f - WedgeInt c z f = WedgeInt z (z+h) f := by
  simp only [Metric.mem_ball] at hz
  have : 0 < (r - dist z c) / 2 := by sorry
  filter_upwards [Metric.ball_mem_nhds 0 this]
  intro h hh
  simp only [Metric.mem_ball, dist_zero_right, norm_eq_abs] at hh
  simp only [WedgeInt] --, add_re, ofReal_add, add_im, smul_eq_mul]
  rw [add_sub_add_comm]
  have := @intervalIntegral.integral_interval_sub_left ℂ _ _ c.re (z+h).re z.re (λ x => f (x + c.im * I))  MeasureTheory.volume ?_ ?_
  rw [this]

  -- need that integral of f over rectangle is zero



  have := (@smul_sub ℂ ℂ _ _ _ I (∫ (y : ℝ) in c.im..(z + h).im, f (↑(z + h).re + ↑y * I)) (∫ (y : ℝ) in c.im..z.im, f (↑z.re + ↑y * I))).symm
  rw [this]
  have := @intervalIntegral.integral_interval_sub_left ℂ _ _ c.im (z+h).im z.im (λ y => f (↑z.re + ↑y * I))  MeasureTheory.volume ?_ ?_
  rw [this]
  --apply intervalIntegral.integral_interval_sub_left

#exit

lemma derivOfLinint (z₀ : ℂ) (f: ℂ → ℂ) (hf: Continuous f) (l: Filter ℂ):
    Asymptotics.IsLittleO l (fun h ↦ ((linint z₀ (z₀+h) f) - h*(f z₀))) (fun h ↦ h) := by
  sorry

-- trivial case: empty set
theorem hasPrimitivesOfEmpty : hasPrimitives ∅ := by
  dsimp [hasPrimitives]
  simp only [Set.eqOn_empty, and_true]
  dsimp [DifferentiableOn]
  dsimp [DifferentiableWithinAt]
  dsimp [HasFDerivWithinAt]
  dsimp [HasFDerivAtFilter]
  simp only [Set.mem_empty_iff_false, nhdsWithin_empty, map_sub, IsEmpty.forall_iff, forall_const, exists_const,
  forall_true_left]


-- To prove the main theorem, we first prove it on a disc
-- not sure what happens if U is empty
theorem hasPrimitivesOfConvex (U: Set ℂ) (hU: Convex ℝ U) : hasPrimitives U := by
  by_cases hne : U = ∅
  · convert hasPrimitivesOfEmpty

  · intros f hf_diff
    -- get z₀
    have : Nonempty U := Set.nonempty_iff_ne_empty'.mpr hne
    obtain ⟨z₀,hz₀⟩ := Set.exists_mem_of_nonempty U
    use fun z ↦ linint z₀ z f
    constructor
    · sorry

    · intro z  hz
      have : ∀ h : ℂ, z+h∈ U → linint z₀ (z+h) f - linint z₀ z f = linint z (z+h) f:= by
        intros h hinU
        refine diffOfIntegrals U hU z₀ (z+h) z ?_ hinU hz f hf_diff

        exact Subtype.mem z₀
      sorry


-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem hasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    hasPrimitives U := by
  sorry


#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
