import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Init.Prelude
import Mathlib.Data.Matrix.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.PNat.Notation
import Mathlib.Data.Real.ConjExponents
import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!

Math implementation for lecture 00:
https://github.com/stephenbeckr/convex-optimization-class/blob/main/Notes/00_IntroToOptProblems.pdf

uses CvxLean as a reference:
- https://github.com/verified-optimization/CvxLean/blob/c62c2f292c6420f31a12e738ebebdfed50f6f840/CvxLean/Lib/Minimization.lean

-/

section intro_to_opt_problems

variable
    {D: Type*}
    {R: Type*} [LE R]
    (f: D → R)
    (S: Set D)

/-- min of f(x) for all x in C -/
def MinimumOn
    (f: D → R)
    (S: Set D)
    (value : R)
    : Prop
    := IsLeast (S.image f) value

/-- max of f(x) for all x in C -/
def MaximumOn
    (f: D → R)
    (S: Set D)
    (value : R)
    : Prop
    := IsGreatest (S.image f) value

/-- y s.t. f(y) = min of f(x) for all x in C -/
def ArgumentMinimumOn
    (f: D → R)
    (S: Set D)
    : Set D
    := setOf fun xmin: D => xmin ∈ S ∧ MinimumOn f S (f xmin)

/-- y s.t. f(y) = max of f(x) for all x in C -/
def ArgumentMaximumOn
    (f: D → R)
    (S: Set D)
    : Set D
    := setOf fun xmax: D => xmax ∈ S ∧ MaximumOn f S (f xmax)

/-- inf of f(x) for all x in C -/
def InfimumOn
    (f: D → R)
    (S: Set D)
    (value : R)
    : Prop
    := IsGLB (S.image f) value

/-- sup of f(x) for all x in C -/
def SupremumOn
    (f: D → R)
    (S: Set D)
    (value : R)
    : Prop
    := IsLUB (S.image f) value

theorem inf_of_min
    {f: D → R}
    {S: Set D}
    {min : R}
    (hmin : MinimumOn f S min)
    : InfimumOn f S min
    := by
    simp [InfimumOn, IsGLB, IsGreatest, upperBounds, lowerBounds]
    simp [MinimumOn, IsLeast, lowerBounds] at hmin

    constructor
    exact hmin.right
    intro y h
    rw [← hmin.left.choose_spec.right]
    apply h
    exact hmin.left.choose_spec.left

theorem min_of_inf_and_exists
    {f: D → R}
    {S: Set D}
    {inf : R}
    (hinf : InfimumOn f S inf)
    (h : ∃ x ∈ S, f x = inf)
    : MinimumOn f S inf
    := by
    simp [MinimumOn, IsLeast, upperBounds, lowerBounds]
    simp [InfimumOn, IsGLB, IsGreatest, IsLeast, lowerBounds, upperBounds] at hinf

    constructor
    exact h
    intro x hXInS
    exact hinf.left x hXInS

/--
If a function is L-continuous, any two points that are a distance `d` apart
are no more than `L * d` apart when mapped through the function.
-/
def lipschitz_continuous
    [Field ℝ] [Lattice ℝ]
    {ℝn : Type*} [NormedAddCommGroup ℝn] [NormedSpace ℝ ℝn]
    (f : ℝn → ℝ)
    (L : NNReal)
    : Prop
    := ∀ x y : ℝn, abs ((f y) - (f x)) ≤ L * dist y x

#check lipschitz_continuous (fun x => ![1, 3] ⬝ᵥ x) (3 : NNReal)


theorem holder_inequality
    {n : Nat}
    (p q: ENNReal)
    (hp : p ≥ 1)
    (hq : q ≥ 1)
    (hpq : p.IsConjExponent q)
    (x : WithLp p (Fin n → ℝ)) [Norm (WithLp p (Fin n → ℝ))]
    (y : WithLp q (Fin n → ℝ)) [Norm (WithLp q (Fin n → ℝ))]
    :
    (∑ i: Fin n, (x i) * (y i))
    ≤ ‖x‖ * ‖y‖
    := sorry


def epsilon_optimal
    [HSub R R R]
    (min : R)
    (hmin : MinimumOn f S min)
    (value : D)
    (epsilon : R)
    : Prop
    := f value - min ≤ epsilon

end intro_to_opt_problems
