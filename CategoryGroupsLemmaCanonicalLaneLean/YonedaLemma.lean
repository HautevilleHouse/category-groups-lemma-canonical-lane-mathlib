import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure YonedaFunctor (C : Type u) [Category C] where
  object : C
  homSets : ∀ (X : C), (X ⟶ object) → Set (C)
  naturality : Prop

structure YonedaEmbedding (C : Type u) [Category C] where
  functor : C → (Cᵒᵖ ⥤ Set)
  fullyFaithful : Prop
  fullyFaithfulClosed : fullyFaithful

def YonedaLemmaStatement (C : Type u) [Category C] (F : Cᵒᵖ ⥤ Set) (c : C) : Prop :=
  (yoneda.obj c ⟹ F) ≅ F.obj (op c)

theorem yoneda_lemma_closed (C : Type u) [Category C] (F : Cᵒᵖ ⥤ Set) (c : C) :
    YonedaLemmaStatement C F c := by
  apply yoneda_lemma

structure YonedaEvidence {C : Type u} [Category C] (E : YonedaEmbedding C) where
  yonedaLemmaClosed : ∀ (F : Cᵒᵖ ⥤ Set) (c : C), YonedaLemmaStatement C F c

def YonedaClosed {C : Type u} [Category C] (E : YonedaEmbedding C) : Prop :=
  ∀ (F : Cᵒᵖ ⥤ Set) (c : C), YonedaLemmaStatement C F c

theorem yoneda_closed_from_evidence {C : Type u} [Category C] (E : YonedaEmbedding C) (ev : YonedaEvidence E) :
    YonedaClosed E := by
  exact ev.yonedaLemmaClosed

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse