import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.MorphismsAndComposition

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure Functor {A : AdmissibleClass} (C D : MorphismCategory A) where
  objectMap : C.sourceObject → D.sourceObject
  morphismMap : C.morphismSet → D.morphismSet
  functoriality : ∀ f g : C.morphismSet, morphismMap (C.compositionLaw f g) = D.compositionLaw (morphismMap f) (morphismMap g)
  identityPreserved : morphismMap C.identityMorphism = D.identityMorphism

structure NaturalTransformation {A : AdmissibleClass} {C D : MorphismCategory A} (F G : Functor C D) where
  components : ∀ x : C.sourceObject, D.morphismSet
  naturality : ∀ (x y : C.sourceObject) (f : C.morphismSet), D.compositionLaw (components x) (G.morphismMap f) = D.compositionLaw (F.morphismMap f) (components y)

def FunctorComposition {A : AdmissibleClass} {C D E : MorphismCategory A} (F : Functor C D) (G : Functor D E) : Functor C E where
  objectMap x := G.objectMap (F.objectMap x)
  morphismMap f := G.morphismMap (F.morphismMap f)
  functoriality f g := by
    calc
      G.morphismMap (F.morphismMap (C.compositionLaw f g)) = G.morphismMap (D.compositionLaw (F.morphismMap f) (F.morphismMap g)) := by rw [F.functoriality f g]
      _ = E.compositionLaw (G.morphismMap (F.morphismMap f)) (G.morphismMap (F.morphismMap g)) := by rw [G.functoriality]
  identityPreserved := by
    calc
      G.morphismMap (F.morphismMap C.identityMorphism) = G.morphismMap D.identityMorphism := by rw [F.identityPreserved]
      _ = E.identityMorphism := by rw [G.identityPreserved]

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse