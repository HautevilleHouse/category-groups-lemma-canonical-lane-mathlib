import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.FunctorsAndNaturalTransformations
import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.LimitsAndColimits

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure Adjunction {A : AdmissibleClass} {C D : MorphismCategory A} (F : Functor C D) (G : Functor D C) where
  unit : NaturalTransformation (idFunctor C) (functorComposition F G)
  counit : NaturalTransformation (functorComposition G F) (idFunctor D)
  triangleLeft : ∀ (x : C.sourceObject), D.compositionLaw (F.morphismMap (unit.components x)) (counit.components (F.objectMap x)) = D.identityMorphism
  triangleRight : ∀ (y : D.sourceObject), C.compositionLaw (unit.components (G.objectMap y)) (G.morphismMap (counit.components y)) = C.identityMorphism
  where
    idFunctor (C' : MorphismCategory A) : Functor C' C' where
      objectMap := fun x => x
      morphismMap := fun f => f
      functoriality := fun f g => rfl
      identityPreserved := rfl
    functorComposition (F' : Functor C D) (G' : Functor D C) : Functor C C :=
      FunctorComposition F' G'

structure AdjointFunctorsEvidence {A : AdmissibleClass} {C D : MorphismCategory A} {F : Functor C D} {G : Functor D C} (adj : Adjunction F G) where
  triangleLeftClosed : adj.triangleLeft
  triangleRightClosed : adj.triangleRight

def AdjointFunctorsClosed {A : AdmissibleClass} {C D : MorphismCategory A} {F : Functor C D} {G : Functor D C} (adj : Adjunction F G) : Prop :=
  adj.triangleLeft ∧ adj.triangleRight

theorem adjoint_functors_closed_from_evidence {A : AdmissibleClass} {C D : MorphismCategory A} {F : Functor C D} {G : Functor D C} (adj : Adjunction F G) (E : AdjointFunctorsEvidence adj) : AdjointFunctorsClosed adj := by
  exact And.intro E.triangleLeftClosed E.triangleRightClosed

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse