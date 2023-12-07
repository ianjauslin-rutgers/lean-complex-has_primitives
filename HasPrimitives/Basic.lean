import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

open Set Complex Real Metric Topology

-- From V. Beffara https://github.com/vbeffara/RMT4
def has_primitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

lemma has_primitives_of_simply_connected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
   has_primitives U := by sorry

namespace Real

noncomputable def straightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) : ℝ → ℂ :=
  fun t => z₁ * (1 - cos (t * π / (t₂ - t₁))) + z₂ * cos (t * π / (t₂ - t₁))

#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
