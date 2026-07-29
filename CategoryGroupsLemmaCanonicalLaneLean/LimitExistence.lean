import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.AdjointFunctorTheorem

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure LimitExistencePackage (A : AdmissibleClass) where
  hasSmallLimits : Prop
  hasColimits : Prop
  completeness : Prop
  cocompleteness : Prop
  hasSmallLimitsClosed : hasSmallLimits
  hasColimitsClosed : hasColimits
  completenessClosed : completeness
  cocompletenessClosed : cocompleteness

def LimitExistenceClosed (A : AdmissibleClass) (L : LimitExistencePackage A) : Prop :=
  L.completeness ∧ L.cocompleteness

theorem limit_existence_closed_from_evidence (A : AdmissibleClass) (L : LimitExistencePackage A) :
    LimitExistenceClosed A L := by
  exact And.intro L.completenessClosed L.cocompletenessClosed

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse