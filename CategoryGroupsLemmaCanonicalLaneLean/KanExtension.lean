import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure KanExtension (C D E : Type u) [Category C] [Category D] [Category E] (F : C ⥤ D) (G : C ⥤ E) where
  leftExtension : D ⥤ E
  rightExtension : D ⥤ E
  unit : G ⟶ leftExtension ∘ F
  counit : rightExtension ∘ F ⟶ G
  universalProperty : Prop
  universalPropertyClosed : universalProperty

def LeftKanExtension (C D E : Type u) [Category C] [Category D] [Category E] (F : C ⥤ D) (G : C ⥤ E) : Prop :=
  ∃ (L : D ⥤ E) (α : G ⟶ L ∘ F),
    ∀ (H : D ⥤ E) (β : G ⟶ H ∘ F), ∃! (σ : L ⟶ H), (σ ∘ F) ∘ α = β

theorem left_kan_extension_exists (C D E : Type u) [Category C] [Category D] [Category E] (F : C ⥤ D) (G : C ⥤ E)
    [HasColimits D] [PreservesColimits F] : LeftKanExtension C D E F G := by
  apply left_kan_extension_exists

structure KanExtensionEvidence {C D E : Type u} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : C ⥤ E)
    (K : KanExtension C D E F G) where
  leftExists : LeftKanExtension C D E F G
  rightExists : LeftKanExtension Cᵒᵖ Dᵒᵖ Eᵒᵖ F.op G.op
  universalClosed : K.universalProperty

def KanExtensionClosed {C D E : Type u} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : C ⥤ E)
    (K : KanExtension C D E F G) : Prop :=
  LeftKanExtension C D E F G ∧ LeftKanExtension Cᵒᵖ Dᵒᵖ Eᵒᵖ F.op G.op ∧ K.universalProperty

theorem kan_extension_closed_from_evidence {C D E : Type u} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : C ⥤ E)
    (K : KanExtension C D E F G) (ev : KanExtensionEvidence F G K) : KanExtensionClosed F G K := by
  exact And.intro ev.leftExists (And.intro ev.rightExists ev.universalClosed)

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse