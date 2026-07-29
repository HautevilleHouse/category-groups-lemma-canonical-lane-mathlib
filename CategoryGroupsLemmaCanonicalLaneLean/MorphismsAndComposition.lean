import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure MorphismCategory {A : AdmissibleClass} where
  sourceObject : Type u
  targetObject : Type u
  morphismSet : Type v
  compositionLaw : morphismSet → morphismSet → morphismSet
  identityMorphism : morphismSet
  associativity : ∀ f g h : morphismSet, compositionLaw (compositionLaw f g) h = compositionLaw f (compositionLaw g h)
  identityLeft : ∀ f : morphismSet, compositionLaw identityMorphism f = f
  identityRight : ∀ f : morphismSet, compositionLaw f identityMorphism = f

structure MorphismCategoryEvidence {A : AdmissibleClass} (M : MorphismCategory A) where
  associativityClosed : M.associativity
  identityLeftClosed : M.identityLeft
  identityRightClosed : M.identityRight

def MorphismCategoryClosed {A : AdmissibleClass} (M : MorphismCategory A) : Prop :=
  M.associativity ∧ M.identityLeft ∧ M.identityRight

theorem morphism_category_closed_from_evidence {A : AdmissibleClass} (M : MorphismCategory A) (E : MorphismCategoryEvidence M) : MorphismCategoryClosed M := by
  exact And.intro E.associativityClosed (And.intro E.identityLeftClosed E.identityRightClosed)

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse