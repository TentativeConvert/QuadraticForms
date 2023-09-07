import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

variable (K L : Type) [Field K] [Field L]
variable (m : ℕ)

example : Module K ((Fin m) → K) := by
  exact Pi.module (Fin m) (fun _ => K) K

open scoped LinearMap
open FiniteDimensional
open Set

@[ext]
structure FinDimVecSpaces (K : Type) [Field K] where
  carrier : Type
  isAddCommGroup : AddCommGroup carrier
  isModule : Module K carrier
  isFinDim : FiniteDimensional K carrier

attribute [instance] FinDimVecSpaces.isAddCommGroup FinDimVecSpaces.isModule
  FinDimVecSpaces.isFinDim


def TT (V : FinDimVecSpaces K) : V.carrier → ℕ := by
  sorry
  done

instance VecSpacesUptoEquiv : Setoid ( FinDimVecSpaces K) where
  r := λ V W ↦ Nonempty (V.carrier ≃ₗ[K] W.carrier)
  --(finrank K V.carrier = finrank K W.carrier)
  iseqv := {
    refl := sorry
    symm := sorry
    trans := sorry --fun hx hy => hx.trans hy
  }

lemma vecspace_equiv_iff (V W : FinDimVecSpaces K) : V ≈ W ↔ Nonempty (V.carrier ≃ₗ[K] W.carrier) := Iff.rfl

def MyNat := Quotient (VecSpacesUptoEquiv K)

def MyKn (n : ℕ) : FinDimVecSpaces K := ⟨(Fin n → K), Pi.addCommGroup, Pi.module (Fin n) (fun _ => K) K, by exact
  Module.Finite.pi ⟩

#check MyKn

example : FinDimVecSpaces K := MyKn K 3

#check VecSpacesUptoEquiv K

example (n : ℕ) : MyNat K := ⟦MyKn K n⟧


def F : ℕ → MyNat K := λ n ↦  ⟦MyKn K n⟧

noncomputable def G : MyNat K → ℕ := Quotient.lift (fun V ↦ FiniteDimensional.finrank K V.carrier)
  (fun V W ↦ by sorry  )

set_option pp.proofs.withType false

example (C : MyNat K) : F K (G K C) = C := by
  simp only [F, G] 
  rw [←Quotient.out_eq C,
    Quotient.lift_mk,
    Quotient.out_eq C,
    Quotient.mk_eq_iff_out,
    vecspace_equiv_iff]
  apply nonempty_linearEquiv_of_rank_eq
  simp [MyKn]
  done

def example_qf : QuadraticForm K (Fin m → K) where
  toFun := sorry
  toFun_smul := sorry
  exists_companion' := sorry

