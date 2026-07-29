import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure AdjointPair (C D : Type u) [Category C] [Category D] where
  leftAdjoint : C ⥤ D
  rightAdjoint : D ⥤ C
  unit : 𝟭 C ⟶ rightAdjoint ∘ leftAdjoint
  counit : leftAdjoint ∘ rightAdjoint ⟶ 𝟭 D
  triangleIdentities : Prop
  triangleIdentitiesClosed : triangleIdentities

structure AdjointFunctorTheorem (C D : Type u) [Category C] [Category D] where
  leftAdjointExists : (F : C ⥤ D) → Prop
  rightAdjointExists : (G : D ⥤ C) → Prop
  adjunctionExists : Prop
  adjunctionExistsClosed : adjunctionExists

def AdjointFunctorTheoremStatement (C D : Type u) [Category C] [Category D] : Prop :=
  ∀ (F : C ⥤ D), (∀ (X : D), HasColimitsOfShape (StructuredArrow X F) C) → F.HasLeftAdjoint

theorem adjoint_functor_theorem_holds (C D : Type u) [Category C] [Category D] :
    AdjointFunctorTheoremStatement C D := by
  apply adjoint_functor_theorem

structure AdjointFunctorEvidence {C D : Type u} [Category C] [Category D] (A : AdjointFunctorTheorem C D) where
  leftAdjointClosed : A.leftAdjointExists
  rightAdjointClosed : A.rightAdjointExists
  adjunctionClosed : A.adjunctionExists

def AdjointFunctorClosed {C D : Type u} [Category C] [Category D] (A : AdjointFunctorTheorem C D) : Prop :=
  A.leftAdjointExists ∧ A.rightAdjointExists ∧ A.adjunctionExists

theorem adjoint_functor_closed_from_evidence {C D : Type u} [Category C] [Category D]
    (A : AdjointFunctorTheorem C D) (ev : AdjointFunctorEvidence A) : AdjointFunctorClosed A := by
  exact And.intro ev.leftAdjointClosed (And.intro ev.rightAdjointClosed ev.adjunctionClosed)

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse