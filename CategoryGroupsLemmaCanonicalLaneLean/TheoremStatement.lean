import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.ReviewerBridge

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure TheoremStatement where
  sourceKey : String
  theoremName : String
  theoremObject : String
  classicalBoundary : String
  categoryConstrainedStatement : String
  certificateLane : String
  carriedRemainder : String
deriving Repr, DecidableEq

def sourceTheoremStatement : TheoremStatement := {
  sourceKey := "category-groups-lemma-canonical-lane",
  theoremName := "Category Groups Lemma",
  theoremObject := "Adjoint Functor Theorem, Yoneda Lemma, existence of limits",
  classicalBoundary := "category-theoretic ZFC foundation carried as open boundary",
  categoryConstrainedStatement := "category-constrained theorem certificate internalized through baseline gates and reviewer bridge",
  certificateLane := "category_constrained",
  carriedRemainder := "classical source boundary carried by formalization certificate"
}

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse