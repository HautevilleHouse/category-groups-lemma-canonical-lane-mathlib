import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.CategoryGroupsLemma

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure YonedaEmbeddingPackage where
  sourceCategory : Type u
  targetCategory : Type v
  yonedaFunctor : Type w
  fullFidelity : Prop
  representablePreservation : Prop

structure YonedaEmbeddingEvidence (Y : YonedaEmbeddingPackage) where
  fullFidelityClosed : Y.fullFidelity
  representablePreservationClosed : Y.representablePreservation

def YonedaEmbeddingClosed (Y : YonedaEmbeddingPackage) : Prop :=
  Y.fullFidelity ∧ Y.representablePreservation

theorem yoneda_embedding_closed_from_evidence
    (Y : YonedaEmbeddingPackage) (E : YonedaEmbeddingEvidence Y) :
    YonedaEmbeddingClosed Y := by
  exact And.intro E.fullFidelityClosed E.representablePreservationClosed

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse