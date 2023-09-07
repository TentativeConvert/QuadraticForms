import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional

universe v u

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable (m : ℕ)

open scoped LinearMap
open FiniteDimensional
open Set

structure QuadSpaceCat where
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module K carrier]
  [isFinDim : FiniteDimensional K carrier]
  form : QuadraticForm K carrier


#check QuadSpaceCat.form
attribute [instance] QuadSpaceCat.isAddCommGroup QuadSpaceCat.isModule QuadSpaceCat.isFinDim

/-- An alias for `QuadSpaceCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev QuadSpaceCatMax.{v₁, v₂, u₁} (K : Type u₁) [Field K] := QuadSpaceCat.{max v₁ v₂, u₁} K

namespace QuadSpaceCat

def of_form {V : Type v} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) : QuadSpaceCat K:= ⟨V, Q⟩

-- instance : CoeSort (QuadSpaceCat.{v} K) (Type v) :=
--  ⟨QuadSpaceCat.carrier⟩

--instance (Q : QuadSpaceCat.{v} K) : CoeDep _ Q (QuadraticForm K Q.carrier) :=
--  ⟨Q.form⟩

-- attribute [coe] QuadSpaceCat.carrier

instance QuadFormsEquiv : Setoid ( QuadSpaceCat K) where
  r := λ Q₁ Q₂ ↦ QuadraticForm.Equivalent Q₁.form Q₂.form
  iseqv := {
    refl := by tauto
    symm := by tauto
    trans := λ hx hy ↦ hx.trans hy
  }

def GW := Quotient (QuadFormsEquiv K)

noncomputable def out_form (Q : GW K) := (Quotient.out Q).form

noncomputable def add : GW K → GW K → GW K := λ Q₁ Q₂ ↦
Quotient.mk _ ⟨_, QuadraticForm.prod Q₁.out.form Q₂.out.form⟩
noncomputable def mul : GW K → GW K → GW K := λ Q₁ Q₂ ↦
Quotient.mk _ ⟨_, QuadraticForm.tmul Q₁.out.form Q₂.out.form⟩

noncomputable instance GWMonoid : CommSemiring (GW K) where
  add := add K
  add_assoc := sorry
  zero := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  mul := mul K
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  mul_comm := sorry