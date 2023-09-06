import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

variable (K L : Type) [Field K] [Field L]
variable (m : ℕ)

example : Module K ((Fin m) → K) := by
  exact Pi.module (Fin m) (fun _ => K) K

open scoped LinearMap
open FiniteDimensional
open Set


structure FinDimVecSpaces (K : Type) [Field K] where
  carrier : Type
  isAddCommGroup : AddCommGroup carrier
  isModule : Module K carrier
  isFinDim : FiniteDimensional K carrier

attribute [instance] FinDimVecSpaces.isAddCommGroup FinDimVecSpaces.isModule
--  FinDimVecSpaces.isFinDim


def VecSpacesUptoEquiv : Setoid ( FinDimVecSpaces K) where
  r := λ V W ↦ Nonempty (V.carrier ≃ₗ[K] W.carrier)
  --(finrank K V.carrier = finrank K W.carrier)
  iseqv := {
    refl := sorry
    symm := sorry
    trans := sorry --fun hx hy => hx.trans hy
  }

def MyNat := Quotient (VecSpacesUptoEquiv K)

def MyKn (n : ℕ) : FinDimVecSpaces K := ⟨(Fin n → K), by exact Pi.addCommGroup, by exact Pi.module (Fin n) (fun _ => K) K, by exact
  Module.Finite.pi ⟩

#check MyKn

example : FinDimVecSpaces K := MyKn K 3

#check VecSpacesUptoEquiv K

example (n : ℕ) : MyNat K := Quotient.mk (VecSpacesUptoEquiv K) (MyKn K n)


def F : ℕ → MyNat K := λ n ↦ Quotient.mk (VecSpacesUptoEquiv K) (MyKn K n)

theorem F_bijection : Function.Bijective (F K):= by
  constructor
  · sorry
  · sorry
done



def example_qf : QuadraticForm K (Fin m → K) where
  toFun := sorry
  toFun_smul := sorry
  exists_companion' := sorry


structure QuadForms' where
  M : Type
  is_add_comm_monoid : AddCommMonoid M
  is_module : Module K M
  q : QuadraticForm K M


example (T : Type) [AddCommMonoid T] (x y : T) : x + y = 0 := by
  sorry
done

structure QuadForms where
  n : ℕ
  q : QuadraticForm K (Fin n → K)

instance : Setoid (QuadForms K) where
  r := 
  iseqv := sorry

#check QuadForms

