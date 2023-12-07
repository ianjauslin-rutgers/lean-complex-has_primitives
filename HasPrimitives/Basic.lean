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
