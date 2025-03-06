import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Group.Defs

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Group/Defs.html#neg_le_neg

/-!

Math implementation for lecture 00:
https://github.com/stephenbeckr/convex-optimization-class/blob/main/Notes/00_IntroToOptProblems.pdf

uses CvxLean as a reference:
- https://github.com/verified-optimization/CvxLean/blob/c62c2f292c6420f31a12e738ebebdfed50f6f840/CvxLean/Lib/Minimization.lean

-/


/- Constraint Set -/

structure ConstraintSet (S: Type) where
    constraints: S -> Prop

namespace ConstraintSet

variable {S: Type}
variable (c: ConstraintSet S)

/-- A point `x : S` is feasible in `c` if it satisfies the constraints. -/
@[reducible]
def feasible (x : S) : Prop := c.constraints x

end ConstraintSet

/- Minimization -/
structure Minimization (Domain Range: Type) where
    objectiveFunc: Domain -> Range
    constraintSet: ConstraintSet Domain

namespace Minimization

variable {D R : Type} [Preorder R]
variable (p : Minimization D R)

/-- A point `x : D` is optimal in `p` if it is feasible and for any feasible point `y : D` the
value of `x` is a lower bound to the value of `y`. --/
@[reducible]
def optimal (x : D) : Prop :=
    (p.constraintSet.feasible x) ∧ ∀ y, p.constraintSet.feasible y
    → p.objectiveFunc x ≤ p.objectiveFunc y

/-- A solution is simply an optimal point. -/
structure Solution where
  point : D
  isOptimal : p.optimal point

end Minimization


/- Maximization -/
structure Maximization (Domain Range: Type) where
    objectiveFunc: Domain -> Range
    constraintSet: ConstraintSet Domain

namespace Maximization

variable {D R : Type} [Preorder R]
variable (p : Maximization D R)

/-- A point `x : D` is optimal in `p` if it is feasible and for any feasible point `y : D` the
value of `x` is a lower bound to the value of `y`. --/
@[reducible]
def optimal (x : D) : Prop :=
    (p.constraintSet.feasible x)
    ∧ ∀ y, p.constraintSet.feasible y → p.objectiveFunc y ≤ p.objectiveFunc x

/-- A solution is simply an optimal point. -/
structure Solution where
  point : D
  isOptimal : p.optimal point

end Maximization


/- Remark -/
/-- max_x f(x) = -min_x (-f(x)) -/
theorem max_obj_eq_neg_min_neg_obj
    {D R : Type} [OrderedAddCommGroup R]
        -- [InvolutiveNeg R]
    (min : Minimization D R)
    (s: min.Solution)
    : (
        Maximization.mk
        (fun x: D => -(min.objectiveFunc x))
        min.constraintSet
    ).optimal s.point
    := by
        constructor
        exact s.isOptimal.left
        choose y
        choose y_feasible
        show -min.objectiveFunc y <= -min.objectiveFunc s.point
        have isLeq := s.isOptimal.right y y_feasible
        exact neg_le_neg isLeq
